-- Copyright (c) 2025 Andrew Farmer
-- Copyright (c) 2020-2024 Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Retrie.Types
  ( Direction(..)
    -- * Queries and Matchers
  , Query(..)
  , Matcher(..)
  , mkMatcher
  , mkLocalMatcher
  , mkLocalMatcherWithNames
  , runMatcher
    -- * Rewrites and Rewriters
  , Rewrite
  , mkRewrite
  , Rewriter
  , mkRewriter
  , mkLocalRewriter
  , mkLocalRewriterWithNames
  , runRewriter
  , MatchResult(..)
  , Template(..)
  , MatchResultTransformer
  , defaultTransformer
    -- ** Functions on Rewrites
  , addRewriteImports
  , setRewriteTransformer
  , toURewrite
  , fromURewrite
  , ppRewrite
  , rewritesWithDependents
    -- * Internal
  , RewriterResult(..)
  , ParentPrec(..)
  , Context(..)
  ) where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.State
import Data.Bifunctor
import qualified Data.IntMap.Strict as I
import Data.Data hiding (Fixity)
import Data.Maybe

import Retrie.AlphaEnv
import Retrie.ExactPrint
import Retrie.Fixity
import Retrie.GHC
import Retrie.PatternMap.Class
import Retrie.Quantifiers
import Retrie.RenameInfo
import Retrie.Substitution
import Retrie.Universe

-- | 'Context' maintained by AST traversals.
data Context = Context
  { ctxtBinders :: [RdrName]
    -- ^ Stack of bindings of which we are currently in the right-hand side.
    -- Used to avoid introducing self-recursion.
  , ctxtDependents :: Rewriter
    -- ^ The rewriter we apply to determine whether to add context-dependent
    -- rewrites to 'ctxtRewriter'. We keep this separate because most of the time
    -- it is empty, and we don't want to match every rewrite twice.
  , ctxtFixityEnv :: FixityEnv
    -- ^ Current FixityEnv.
  , ctxtInScope :: AlphaEnv
    -- ^ In-scope local bindings. Used to detect shadowing.
  , ctxtLayoutCol :: Int
    -- ^ Column of the innermost enclosing layout group (1 at the top
    -- level). A textually spliced replacement must lay out its
    -- delta-positioned lines against this column, the way exactprint
    -- would when printing the whole module.
  , ctxtParentPrec :: ParentPrec
    -- ^ Precedence of parent
    -- (app = HasPrec 10, infix op = HasPrec $ op precedence)
  , ctxtRewriter :: Rewriter
    -- ^ The rewriter we should use to mutate the code.
  , ctxtSubst :: Maybe Substitution
    -- ^ If present, update substitution with binder renamings.
    -- Used to implement capture-avoiding substitution.
  , ctxtRenameInfo :: RenameInfo
    -- ^ Optional side-table derived from a 'RenamedSource'.
    -- Lets retrie see binders introduced by features the parser pass
    -- cannot resolve (notably @RecordWildCards@ and @NamedFieldPuns@).
    -- Defaults to 'emptyRenameInfo', which is silent and matches
    -- legacy behaviour.
  , ctxtScopeNames :: FastStringEnv Name
    -- ^ Renamer-resolved 'Name's of the local binders currently in
    -- scope, keyed by occurrence string (innermost binder wins,
    -- matching how shadowing resolves). Only populated when a
    -- 'RenameInfo' is supplied; a miss means unknown, not unbound.
    -- Used to detect when a free variable of a rewrite template would
    -- be captured by a binder enclosing the match site.
  , ctxtMatchSpan :: Maybe SrcSpan
    -- ^ Location of the node rewrites are currently being matched at,
    -- set by the traversal just before the match is attempted. Lets a
    -- 'MatchResultTransformer' accept or refuse a match by where it
    -- occurs (e.g. restrict rewriting to chosen call sites). A refused
    -- match leaves the node unchanged and the traversal descends into
    -- it, so a permitted location nested inside a refused one is still
    -- rewritten.
  }

-- | Precedence of parent node in the AST.
data ParentPrec
  = HasPrec Fixity -- ^ Parent has precedence info.
  | IsLhs      -- ^ We are a pattern in a left-hand-side
  | IsBodyStmt -- ^ We are the body expression of a do-block statement,
               -- a layout position where a leading @let@ would be read as
               -- a let-statement. A spliced @let ... in ...@ here is
               -- parenthesized so it stays one expression.
  | NeverParen -- ^ Based on parent, we should never add parentheses.

------------------------------------------------------------------------

data Direction = LeftToRight | RightToLeft
  deriving (Eq)

------------------------------------------------------------------------

-- | 'Query' is the primitive way to specify a matchable pattern (quantifiers
-- and expression). Whenever the pattern is matched, the associated result
-- will be returned.
data Query ast v = Query
  { qQuantifiers  :: Quantifiers
  , qPattern      :: Annotated ast
  , qResult       :: v
  }

instance Functor (Query ast) where
  fmap f (Query qs ast v) = Query qs ast (f v)

instance Bifunctor Query where
  bimap f g (Query qs ast v) = Query qs (fmap f ast) (g v)

instance (Data (Annotated ast), Show ast, Show v) => Show (Query ast v) where
  show (Query q p r) = "Query " ++ show q ++ " " ++ showAst p ++ " " ++ show r


------------------------------------------------------------------------

-- | 'Matcher' is a compiled 'Query'. Several queries can be compiled and then
-- merged into a single compiled 'Matcher' via 'Semigroup'/'Monoid'.
newtype Matcher a = Matcher (I.IntMap (UMap a))
  deriving (Functor)
-- The 'IntMap' tracks the binding level at which the 'Matcher' was built.
-- See Note [AlphaEnv Offset] for details.

instance Semigroup (Matcher a) where
  (Matcher m1) <> (Matcher m2) = Matcher (I.unionWith mUnion m1 m2)

instance Monoid (Matcher a) where
  mempty = Matcher I.empty

-- | Compile a 'Query' into a 'Matcher'.
mkMatcher :: Matchable ast => Query ast v -> Matcher v
mkMatcher = mkLocalMatcher emptyAlphaEnv

-- | Compile a 'Query' into a 'Matcher' within a given local scope. Useful for
-- introducing local matchers which only match within a given local scope.
--
-- The template is built without 'NameMap' information; templates that
-- need to match by renamer-resolved 'Name' should be built via
-- 'mkLocalMatcherWithNames'.
mkLocalMatcher :: Matchable ast => AlphaEnv -> Query ast v -> Matcher v
mkLocalMatcher = mkLocalMatcherWithNames mempty

-- | Like 'mkLocalMatcher', but threads a 'NameMap' through the
-- template-building walk. Templates inserted via this entry point
-- also key their 'HsVar' positions by 'Unique', so a later 'runMatcher'
-- whose 'Context' carries a matching 'NameMap' can match qualified,
-- unqualified, and aliased references uniformly.
mkLocalMatcherWithNames
  :: Matchable ast => NameMap -> AlphaEnv -> Query ast v -> Matcher v
mkLocalMatcherWithNames nm env Query{..} = Matcher $
  I.singleton (alphaEnvOffset env) $
    insertMatch
      nm
      emptyAlphaEnv
      qQuantifiers
      (inject $ astA qPattern)
      qResult
      mEmpty

------------------------------------------------------------------------

-- | Run a 'Matcher' on an expression in the given 'AlphaEnv' and return the
-- results from any matches. Results are accompanied by a 'Substitution', which
-- maps 'Quantifiers' from the original 'Query' to the expressions they unified
-- with.
runMatcher
  :: (Matchable ast, MonadIO m)
  => Context
  -> Matcher v
  -> ast
  -> TransformT m [(Substitution, v)]
runMatcher Context{..} (Matcher m) ast = do
  seed <- get
  let
    matchEnv = ME ctxtInScope (\x -> unsafeMkA x seed) (riNameMap ctxtRenameInfo)
    uast = inject ast

  return
    [ match
    | (lvl, umap) <- I.toAscList m
    , match <- findMatch (pruneMatchEnv lvl matchEnv) uast umap
    ]

------------------------------------------------------------------------

-- | A 'Rewrite' is a 'Query' specialized to 'Template' results, which have
-- all the information necessary to replace one expression with another.
type Rewrite ast = Query ast (Template ast, MatchResultTransformer)

-- | Make a 'Rewrite' from given quantifiers and left- and right-hand sides.
mkRewrite :: Quantifiers -> Annotated ast -> Annotated ast -> Rewrite ast
mkRewrite qQuantifiers qPattern tTemplate = Query{..}
  where
    tImports = mempty
    tDependents = Nothing
    qResult = (Template{..}, defaultTransformer)

-- | Add imports to a 'Rewrite'. Whenever the 'Rewrite' successfully rewrites
-- an expression, the imports are inserted into the enclosing module.
addRewriteImports :: AnnotatedImports -> Rewrite ast -> Rewrite ast
addRewriteImports imports q = q { qResult = (newTemplate, transformer) }
  where
    (template, transformer) = qResult q
    newTemplate = template { tImports = imports <> tImports template }

-- | Set the 'MatchResultTransformer' for a 'Rewrite'.
setRewriteTransformer :: MatchResultTransformer -> Rewrite ast -> Rewrite ast
setRewriteTransformer transformer q =
  q { qResult = second (const transformer) (qResult q) }

-- | A 'Rewriter' is a complied 'Rewrite', much like a 'Matcher' is a compiled
-- 'Query'.
type Rewriter = Matcher (RewriterResult Universe)

-- | Compile a 'Rewrite' into a 'Rewriter'.
mkRewriter :: Matchable ast => Rewrite ast -> Rewriter
mkRewriter = mkLocalRewriter emptyAlphaEnv

-- | Compile a 'Rewrite' into a 'Rewriter' with a given local scope. Useful for
-- introducing local matchers which only match within a given local scope.
--
-- Templates built via this entry point do /not/ key by 'Name'. To
-- match qualified references by Name, build the rewriter with
-- 'mkLocalRewriterWithNames' and supply the same 'NameMap' used to
-- construct the rewrite's template.
mkLocalRewriter :: Matchable ast => AlphaEnv -> Rewrite ast -> Rewriter
mkLocalRewriter = mkLocalRewriterWithNames mempty

-- | Like 'mkLocalRewriter', but threads a 'NameMap' through the
-- template-building walk so the rewriter can match by renamer-resolved
-- 'Name'. See 'mkLocalMatcherWithNames'.
mkLocalRewriterWithNames
  :: Matchable ast => NameMap -> AlphaEnv -> Rewrite ast -> Rewriter
mkLocalRewriterWithNames nm env q@Query{..} =
  mkLocalMatcherWithNames nm env q { qResult = RewriterResult{..} }
  where
    rrOrigin = getOrigin $ astA qPattern
    rrQuantifiers = qQuantifiers
    (rrTemplate, rrTransformer) = first (fmap inject) qResult

-- | Wrapper that allows us to attach extra derived information to the
-- 'Template' supplied by the 'Rewrite'. Saves the user from specifying it.
data RewriterResult ast = RewriterResult
  { rrOrigin :: SrcSpan
  , rrQuantifiers :: Quantifiers
  , rrTransformer :: MatchResultTransformer
  , rrTemplate :: Template ast
  }
  deriving (Functor)

-- | A 'MatchResultTransformer' allows the user to specify custom logic to
-- modify the result of matching the left-hand side of a rewrite
-- (the 'MatchResult'). The 'MatchResult' generated by this function is used
-- to effect the resulting AST rewrite.
--
-- For example, this transformer looks at the matched expression to build
-- the resulting expression:
--
-- > fancyMigration :: MatchResultTransformer
-- > fancyMigration ctxt matchResult
-- >   | MatchResult sub t <- matchResult
-- >   , HoleExpr e <- lookupSubst sub "x" = do
-- >     e' <- ... some fancy IO computation using 'e' ...
-- >     return $ MatchResult (extendSubst sub "x" (HoleExpr e')) t
-- >   | otherwise = NoMatch
-- >
-- > main :: IO ()
-- > main = runScript $ \opts -> do
-- >   rrs <- parseRewrites opts [Adhoc "forall x. ... = ..."]
-- >   return $ apply
-- >     [ setRewriteTransformer fancyMigration rr | rr <- rrs ]
--
-- Since the 'MatchResultTransformer' can also modify the 'Template', you
-- can construct an entirely novel right-hand side, add additional imports,
-- or inject new dependent rewrites.
type MatchResultTransformer =
  Context -> MatchResult Universe -> IO (MatchResult Universe)

-- | The default transformer. Returns the 'MatchResult' unchanged.
defaultTransformer :: MatchResultTransformer
defaultTransformer = const return

-- | The right-hand side of a 'Rewrite'.
data Template ast = Template
  { tTemplate :: Annotated ast -- ^ The expression for the right-hand side.
  , tImports :: AnnotatedImports
    -- ^ Imports to add whenever a rewrite is successful.
  , tDependents :: Maybe [Rewrite Universe]
    -- ^ Dependent rewrites to introduce whenever a rewrite is successful.
    -- See Note [tDependents]
  }

instance Functor Template where
  fmap f Template{..} = Template { tTemplate = fmap f tTemplate, ..}

-- Note [tDependents]
-- Why Maybe [] instead of just []? We want to support two things:
--
-- 1. Ability to avoid putting most rewrites into ctxtDependents if possible,
-- so context updating doesn't require double-matching every rewrite. Dependent
-- rewrites are not the norm.
--
-- 2. Ability of tTransform to introduce new dependent rewrites. To support
-- this in conjunction with #1, we need some way to say "this should be in
-- ctxtDependents, even if the list is empty".
--
-- So:
--
-- * Nothing = don't include in ctxtDependents
-- * Just [] = include in ctxtDependents, but presumably tTransform will
--             introduce the actual dependent rewrites
-- * Just xs = include in ctxtDependents

-- | The result of matching the left-hand side of a 'Rewrite'.
data MatchResult ast
  = MatchResult Substitution (Template ast)
  | NoMatch

instance Functor MatchResult where
  fmap f (MatchResult s t) = MatchResult s (f <$> t)
  fmap _ NoMatch = NoMatch

------------------------------------------------------------------------

-- | Run a 'Rewriter' on an expression in the given 'AlphaEnv' and return the
-- 'MatchResult's from any matches. Takes an extra function for rewriting the
-- 'RewriterResult', which is run *before* the 'MatchResultTransformer' is run.
runRewriter
  :: forall ast m. (Matchable ast, MonadIO m)
  => (RewriterResult Universe -> RewriterResult Universe)
  -> Context
  -> Rewriter
  -> ast
  -> TransformT m (MatchResult ast)
runRewriter f ctxt rewriter =
  runMatcher ctxt rewriter >=> firstMatch ctxt . map (second f)

-- | Find the first 'valid' match.
-- Runs the user's 'MatchResultTransformer' and sanity checks the result.
firstMatch
  :: (Matchable ast, MonadIO m)
  => Context
  -> [(Substitution, RewriterResult Universe)]
  -> TransformT m (MatchResult ast)
firstMatch _ [] = return NoMatch
firstMatch ctxt ((sub, RewriterResult{..}):matchResults) = do
  -- 'firstMatch' is lazy in 'rrTransformer', only running it enough
  -- times to get the first valid MatchResult.
  matchResult <- TransformT $ lift $ liftIO $ rrTransformer ctxt (MatchResult sub rrTemplate)
  case matchResult of
    MatchResult sub' _
      -- Check that all quantifiers from the original rewrite have mappings
      -- in the resulting substitution. This is mostly to prevent a bad
      -- user-defined MatchResultTransformer from causing havok.
      | isJust $ sequence [ lookupSubst q sub' | q <- qList rrQuantifiers ] ->
        return $ project <$> matchResult
    _ -> firstMatch ctxt matchResults

------------------------------------------------------------------------

-- | Pretty-print a 'Rewrite' for debugging.
ppRewrite :: Rewrite Universe -> String
ppRewrite Query{..} =
  show (qList qQuantifiers) ++
    "\n" ++ printU qPattern ++
    "\n==>\n" ++ printU (tTemplate $ fst qResult)

-- | Inject a type-specific rewrite into the universal type.
toURewrite :: Matchable ast => Rewrite ast -> Rewrite Universe
toURewrite = bimap inject (first (fmap inject))

-- | Project a type-specific rewrite from the universal type.
fromURewrite :: Matchable ast => Rewrite Universe -> Rewrite ast
fromURewrite = bimap project (first (fmap project))

-- | Filter a list of rewrites for those that introduce dependent rewrites.
rewritesWithDependents :: [Rewrite ast] -> [Rewrite ast]
rewritesWithDependents = filter (isJust . tDependents . fst . qResult)
