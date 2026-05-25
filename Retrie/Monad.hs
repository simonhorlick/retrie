-- Copyright (c) 2025 Andrew Farmer
-- Copyright (c) 2020-2024 Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
module Retrie.Monad
  ( -- * Retrie Computations
    Retrie
  , addImports
  , apply
  , applyWithConfig
  , applyWithRenameInfo
  , applyWithStrategy
  , applyWithUpdate
  , applyWithUpdateAndStrategy
  , ApplyConfig(..)
  , defaultApplyConfig
  , focus
  , ifChanged
  , iterateR
  , query
  , queryWithConfig
  , queryWithRenameInfo
  , queryWithUpdate
  , topDownPrune
    -- * Internal
  , changeReplacements
  , getGroundTerms
  , liftRWST
  , runRetrie
  ) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.State.Strict
import Control.Monad.RWS
import Control.Monad.Writer.Strict
import Data.Foldable

import Retrie.AlphaEnv
import Retrie.Context
import Retrie.CPP
import Retrie.ExactPrint
import Retrie.Fixity
import Retrie.GroundTerms
import Retrie.Query
import Retrie.RenameInfo
import Retrie.Replace
import Retrie.Substitution
import Retrie.SYB
import Retrie.Types
import Retrie.Universe

-------------------------------------------------------------------------------

-- | The 'Retrie' monad is essentially 'IO', plus state containing the module
-- that is being transformed. __It is run once per target file.__
--
-- It is special because it also allows Retrie to extract a set of 'GroundTerms'
-- from the 'Retrie' computation /without evaluating it/.
--
-- Retrie uses the ground terms to select which files to target. This is the
-- key optimization that allows Retrie to handle large codebases.
--
-- Note: Due to technical limitations, we cannot extract ground terms if you
-- use 'liftIO' before calling one of 'apply', 'focus', or 'query' at least
-- once. This will cause Retrie to attempt to parse every module in the target
-- directory. In this case, please add a call to 'focus' before the call to
-- 'liftIO'.
data Retrie a where
  Bind :: Retrie b -> (b -> Retrie a) -> Retrie a
  Inst :: RetrieInstruction a -> Retrie a
  Pure :: a -> Retrie a

data RetrieInstruction a where
  Focus :: [GroundTerms] -> RetrieInstruction ()
  Tell :: Change -> RetrieInstruction ()
  IfChanged :: Retrie () -> Retrie () -> RetrieInstruction ()
  Compute :: RetrieComp a -> RetrieInstruction a

type RetrieComp = RWST FixityEnv Change (CPP AnnotatedModule) IO

singleton :: RetrieInstruction a -> Retrie a
singleton = Inst

liftRWST :: RetrieComp a -> Retrie a
liftRWST = singleton . Compute

-- Note [Retrie Monad]
-- We want to extract a set of ground terms (See Note [Ground Terms])
-- from a 'Retrie' computation corresponding to the ground terms of
-- the _first_ rewrite application. To do so, we keep the chain of
-- binds associated to the right (normal form) so an application is
-- always at the head of the chain. This allows us to look at the
-- ground terms without evaluating the computation.
--
-- We _must_ be able to get ground terms without evaluating, because
-- we use them to filter the set of files on which we run the
-- computation itself. This is why we can't simply use a writer.

-- | We want a right-associated chain of binds, because then we can inspect
-- the instructions in a list-like fashion. We could re-associate in the Monad
-- instance, but that leads to a quadratic bind operation. Instead, we use the
-- view technique.
--
-- Right-associativity is guaranteed because the left side of ':>>='
-- can never be another 'Retrie' computation. It is a primitive
-- 'RetrieInstruction'.
data RetrieView a where
  Return :: a -> RetrieView a
  (:>>=) :: RetrieInstruction b -> (b -> Retrie a) -> RetrieView a

view :: Retrie a -> RetrieView a
view (Pure x) = Return x
view (Inst inst) = inst :>>= return
view (Bind (Pure x) k) = view (k x)
view (Bind (Inst inst) k) = inst :>>= k
view (Bind (Bind m k1) k2) = view (Bind m (k1 >=> k2))

-------------------------------------------------------------------------------
-- Instances

instance Functor Retrie where
  fmap = liftM

instance Applicative Retrie where
  pure = Pure
  (<*>) = ap

instance Monad Retrie where
  (>>=) = Bind

instance MonadIO Retrie where
  liftIO = singleton . Compute . liftIO

-------------------------------------------------------------------------------
-- Running

-- | Run the 'Retrie' monad.
runRetrie
  :: FixityEnv
  -> Retrie a
  -> CPP AnnotatedModule
  -> IO (a, CPP AnnotatedModule, Change)
runRetrie fixities retrie = runRWST (getComp retrie) fixities

-- | The 'Replacement's carried by a 'Change'.
changeReplacements :: Change -> [Replacement]
changeReplacements NoChange         = []
changeReplacements (Change repls _) = repls

-- | Helper to extract the ground terms from a 'Retrie' computation.
getGroundTerms :: Retrie a -> [GroundTerms]
getGroundTerms = eval . view
  where
    eval :: RetrieView a -> [GroundTerms]
    eval Return{} = [] -- The computation is empty!
    eval (inst :>>= k) =
      case inst of
        Focus gts -> gts
        Tell _ -> getGroundTerms $ k ()
        IfChanged retrie1 retrie2
          | gts@(_:_) <- getGroundTerms retrie1 -> gts
          | gts@(_:_) <- getGroundTerms retrie2 -> gts
          | otherwise -> getGroundTerms $ k ()
        -- If we reach actual computation, we have to give up. The only
        -- way this can currently happen is if 'liftIO' is called before
        -- any focusing is done.
        Compute _ -> []

-- | Reflect the reified monadic computation.
getComp :: Retrie a -> RetrieComp a
getComp = eval . view
  where
    eval (Return x) = return x
    eval (inst :>>= k) = evalInst inst >>= getComp . k

    evalInst (Focus _) = return ()
    evalInst (Tell c) = tell c
    evalInst (IfChanged r1 r2) = ifChangedComp (getComp r1) (getComp r2)
    evalInst (Compute m) = m

-------------------------------------------------------------------------------
-- Public API

-- | Use the given queries/rewrites to select files for rewriting.
-- Does not actually perform matching. This is useful if the queries/rewrites
-- which best determine which files to target are not the first ones you run,
-- and when you need to 'liftIO' before running any queries/rewrites.
focus :: Data k => [Query k v] -> Retrie ()
focus [] = return ()
focus qs = singleton $ Focus $ map groundTerms qs

-- | Options for 'applyWithConfig' and 'queryWithConfig'. Build one by
-- record-updating 'defaultApplyConfig', so adding a new option is not
-- a breaking change for callers.
data ApplyConfig = ApplyConfig
  { acContextUpdater :: ContextUpdater
    -- ^ Context update function. Default: 'updateContext'.
  , acStrategy :: Strategy (TransformT (WriterT Change IO))
    -- ^ Traversal strategy. Default: 'topDownPrune'. Not used by
    -- queries, which always traverse everything.
  , acRenameInfo :: RenameInfo
    -- ^ Renamer side-table; see 'applyWithRenameInfo'.
    -- Default: 'emptyRenameInfo'.
  }

defaultApplyConfig :: ApplyConfig
defaultApplyConfig = ApplyConfig
  { acContextUpdater = updateContext
  , acStrategy = topDownPrune
  , acRenameInfo = emptyRenameInfo
  }

-- | Apply a set of rewrites. By default, rewrites are applied top-down,
-- pruning the traversal at successfully changed AST nodes. See 'topDownPrune'.
apply :: [Rewrite Universe] -> Retrie ()
apply = applyWithConfig defaultApplyConfig

-- | Apply a set of rewrites with a user-supplied 'RenameInfo'.
--
-- Use this when you have access to a 'RenamedSource' (e.g. via HLS or
-- a custom GHC session) and want retrie to correctly handle binders
-- introduced by @RecordWildCards@ or @NamedFieldPuns@.
--
-- __The 'RenameInfo' must cover every module whose source contributes
-- to the rewriting.__ This means:
--
--   * each /target/ module retrie traverses to apply rewrites, and
--   * each /defining/ module whose function definition is being
--     unfolded or folded via @--unfold@ or @--fold@ (the rewrite's
--     template body retains the defining module's source spans).
--
-- Build a 'RenameInfo' per module with 'mkRenameInfo' and combine them
-- with @('<>')@ (or 'mconcat'). A single 'RenameInfo' value safely
-- carries entries for arbitrarily many modules because 'RealSrcSpan'
-- keys are filename-qualified.
--
-- Template variables whose source spans the 'RenameInfo' covers are
-- matched by renamer-resolved 'Name', so qualified, unqualified, and
-- aliased references to the same definition unify; variables outside
-- its coverage match textually, as with 'apply'.
--
-- If a module's 'RenameInfo' is missing, retrie silently falls back to
-- parser-pass binder collection for that module's nodes, which cannot
-- see wildcard-introduced binders — the original capture bug
-- reappears for that module only.
applyWithRenameInfo :: RenameInfo -> [Rewrite Universe] -> Retrie ()
applyWithRenameInfo ri =
  applyWithConfig defaultApplyConfig { acRenameInfo = ri }

-- | Apply a set of rewrites with a custom context-update function.
applyWithUpdate
  :: ContextUpdater -> [Rewrite Universe] -> Retrie ()
applyWithUpdate updCtxt =
  applyWithConfig defaultApplyConfig { acContextUpdater = updCtxt }

-- | Apply a set of rewrites with a custom traversal strategy.
applyWithStrategy
  :: Strategy (TransformT (WriterT Change IO))
  -> [Rewrite Universe]
  -> Retrie ()
applyWithStrategy strategy =
  applyWithConfig defaultApplyConfig { acStrategy = strategy }

-- | Apply a set of rewrites with custom context-update and traversal strategy.
applyWithUpdateAndStrategy
  :: ContextUpdater
  -> Strategy (TransformT (WriterT Change IO))
  -> [Rewrite Universe]
  -> Retrie ()
applyWithUpdateAndStrategy updCtxt strategy =
  applyWithConfig defaultApplyConfig
    { acContextUpdater = updCtxt, acStrategy = strategy }

-- | Most-general apply variant, taking an 'ApplyConfig'.
applyWithConfig :: ApplyConfig -> [Rewrite Universe] -> Retrie ()
applyWithConfig _ [] = return ()
applyWithConfig ApplyConfig{..} rrs = do
  focus rrs
  singleton $ Compute $ rs $ \ fixityEnv ->
    traverse $ flip transformA $
      everywhereMWithContextBut acStrategy
        (const False) acContextUpdater replace
        (emptyContextWithRenameInfo fixityEnv acRenameInfo m d)
  where
    -- Thread the RenameInfo's NameMap into template construction so
    -- template variables it covers are keyed (and later matched) by
    -- renamer-resolved Name; see the VMap instance.
    compileRewrite =
      mkLocalRewriterWithNames (riNameMap acRenameInfo) emptyAlphaEnv
    m = foldMap compileRewrite rrs
    d = foldMap compileRewrite $ rewritesWithDependents rrs

-- | Query the AST. Each match returns the context of the match, a substitution
-- mapping quantifiers to matched subtrees, and the query's value.
query :: [Query Universe v] -> Retrie [(Context, Substitution, v)]
query = queryWithConfig defaultApplyConfig

-- | Query the AST with a user-supplied 'RenameInfo'. See
-- 'applyWithRenameInfo'.
queryWithRenameInfo
  :: RenameInfo
  -> [Query Universe v]
  -> Retrie [(Context, Substitution, v)]
queryWithRenameInfo ri =
  queryWithConfig defaultApplyConfig { acRenameInfo = ri }

-- | Query the AST with a custom context update function.
queryWithUpdate
  :: ContextUpdater
  -> [Query Universe v]
  -> Retrie [(Context, Substitution, v)]
queryWithUpdate updCtxt =
  queryWithConfig defaultApplyConfig { acContextUpdater = updCtxt }

-- | Most-general query variant, taking an 'ApplyConfig'
-- ('acStrategy' is not used by queries).
queryWithConfig
  :: ApplyConfig
  -> [Query Universe v]
  -> Retrie [(Context, Substitution, v)]
queryWithConfig _ [] = return []
queryWithConfig ApplyConfig{..} qs = do
  focus qs
  singleton $ Compute $ do
    fixityEnv <- ask
    cpp <- get
    results <- lift $ forM (toList cpp) $ \modl -> do
      annotatedResults <- transformA modl $
        everythingMWithContextBut
          (const False)
          acContextUpdater
          (genericQ matcher)
          (emptyContextWithRenameInfo fixityEnv acRenameInfo mempty mempty)
      return (astA annotatedResults)
    return $ concat results
  where
    matcher =
      foldMap (mkLocalMatcherWithNames (riNameMap acRenameInfo) emptyAlphaEnv) qs

-- | If the first 'Retrie' computation makes a change to the module,
-- run the second 'Retrie' computation.
ifChanged :: Retrie () -> Retrie () -> Retrie ()
ifChanged r1 r2 = singleton $ IfChanged r1 r2

ifChangedComp :: RetrieComp () -> RetrieComp () -> RetrieComp ()
ifChangedComp r1 r2 = do
  (_, c) <- listen r1
  case c of
    Change{} -> r2
    NoChange -> return ()

-- | Iterate given 'Retrie' computation until it no longer makes changes,
-- or N times, whichever happens first.
iterateR :: Int -> Retrie () -> Retrie ()
iterateR n r = when (n > 0) $ ifChanged r $ iterateR (n-1) r
-- By implementing in terms of 'ifChanged', we expose the ground terms for 'r'

-- | Add imports to the module.
addImports :: AnnotatedImports -> Retrie ()
addImports imports = singleton $ Tell $ Change [] [imports]

-- | Top-down traversal that does not descend into changed AST nodes.
-- Default strategy used by 'apply'.
topDownPrune :: Monad m => Strategy (TransformT (WriterT Change m))
topDownPrune p cs x = do
  (p', c) <- listenTransformT (p x)
  case c of
    Change{} -> return p'
    NoChange -> cs x

-- | Monad transformer shuffling.
listenTransformT
  :: (Monad m, Monoid w)
  => TransformT (WriterT w m) a -> TransformT (WriterT w m) (a, w)
listenTransformT (TransformT rwst) =
  TransformT $ RWST $ \ r s -> do
    ((x,y,z),w) <- listen $ runRWST rwst r s
    return ((x,w),y,z) -- naming is hard

-- | Like 'rws', but builds 'RWST' instead of 'RWS',
-- takes argument in WriterT layer, and specialized to ().
rs :: Monad m => (r -> s -> WriterT w m s) -> RWST r w s m ()
rs f = RWST $ \ r s -> do
  (s', w) <- runWriterT (f r s)
  return ((), s', w)
