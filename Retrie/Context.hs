-- Copyright (c) 2025 Andrew Farmer
-- Copyright (c) 2020-2024 Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Retrie.Context
  ( ContextUpdater
  , updateContext
  , emptyContext
  , emptyContextWithRenameInfo
  ) where

import Control.Monad.IO.Class
import Data.Char (isDigit)
import Data.Either (partitionEithers)
import Data.Function (on)
import Data.Generics hiding (Fixity)
#if __GLASGOW_HASKELL__ < 912
import Data.List
#else
import Data.List (nubBy)
#endif
import Data.Maybe

import Retrie.AlphaEnv
import Retrie.ExactPrint
import Retrie.Fixity
import Retrie.FreeVars
import Retrie.GHC
import Retrie.RenameInfo
import Retrie.Substitution
import Retrie.SYB
import Retrie.Types
import Retrie.Universe

-------------------------------------------------------------------------------

-- | Type of context update functions for 'apply'.
-- When defining your own 'ContextUpdater', you probably want to extend
-- 'updateContext' using SYB combinators such as 'mkQ' and 'extQ'.
type ContextUpdater = forall m. MonadIO m => GenericCU (TransformT m) Context

-- | Default context update function.
updateContext :: forall m. MonadIO m => GenericCU (TransformT m) Context
updateContext c i =
  const (return c)
    `extQ` (return . updExp)
    `extQ` (return . updType)
    `extQ` (return . updMatch)
    `extQ` (return . updGRHSs)
    `extQ` (return . updGRHS)
    `extQ` (return . updStmt)
    `extQ` (return . updPat)
    `extQ` updStmtList
    `extQ` (return . updHsBind)
    `extQ` (return . updTyClDecl)
  where
    neverParen = c { ctxtParentPrec = NeverParen }

    updExp :: HsExpr GhcPs -> Context
    updType :: HsType GhcPs -> Context

#if __GLASGOW_HASKELL__ < 912
    updType HsAppTy{} = withPrec c (SourceText "HsAppTy") (getPrec appPrec) InfixL i
    updType HsFunTy{} = withPrec c (SourceText "HsFunTy") (getPrec funPrec) InfixR (i - 1)
    updType _ = withPrec c (SourceText "HsType") (getPrec appPrec) InfixN i

    updExp HsApp{} = withPrec c (SourceText "HsApp") 10 InfixL i
    updExp (OpApp _ _ op _)
      | Fixity source prec dir <- lookupOp op $ ctxtFixityEnv c =
          withPrec c source prec dir i
    updExp (SectionL _ _ op)
      | Fixity source prec dir <- lookupOp op $ ctxtFixityEnv c =
          withPrec c source prec dir i
    updExp (SectionR _ op _)
      | Fixity source prec dir <- lookupOp op $ ctxtFixityEnv c =
          withPrec c source prec dir i

    updExp RecordUpd{}
      | i == firstChild = withPrec c (SourceText "RecordUpd") 11 InfixN i
    updExp (HsLet _ _ lbs _ _) = addInScope' neverParen $ resolvedLocalBinders c lbs
#else
    updType HsAppTy{} = withPrec c (getPrec appPrec) InfixL i
    updType HsFunTy{} = withPrec c (getPrec funPrec) InfixR (i - 1)
    updType _ = withPrec c (getPrec appPrec) InfixN i

    updExp HsApp{} = withPrec c 10 InfixL i
    updExp (OpApp _ _ op _)
      | Fixity prec dir <- lookupOp op $ ctxtFixityEnv c =
          withPrec c prec dir i
    updExp (SectionL _ _ op)
      | Fixity prec dir <- lookupOp op $ ctxtFixityEnv c =
          withPrec c prec dir i
    updExp (SectionR _ op _)
      | Fixity prec dir <- lookupOp op $ ctxtFixityEnv c =
          withPrec c prec dir i

    updExp RecordUpd{}
      | i == firstChild = withPrec c 11 InfixN i
    updExp (HsLet _ lbs _) = addInScope' neverParen $ resolvedLocalBinders c lbs
#endif
    updExp _ = neverParen

    updMatch :: Match GhcPs (LHsExpr GhcPs) -> Context
    updMatch m
      | i == 2  -- m_pats field
      = addInScope' c{ctxtParentPrec = IsLhs} (resolvedMatchBinders c m)
      | otherwise
      = addInScope' neverParen (resolvedMatchBinders c m)

    updGRHSs :: GRHSs GhcPs (LHsExpr GhcPs) -> Context
    updGRHSs grhss =
      addInScope' neverParen (resolvedLocalBinders c (grhssLocalBinds grhss))

    updGRHS :: GRHS GhcPs (LHsExpr GhcPs) -> Context
    updGRHS (GRHS _ gs _)
        -- binders are in scope over the body (right child) only
      | i > firstChild = addInScope' neverParen bs
      | otherwise = fst $ updateSubstitution neverParen (fst bs)
      where
        bs = foldMap (resolvedStmtBinders c) gs

    updStmt :: Stmt GhcPs (LHsExpr GhcPs) -> Context
    -- The body of a do-block statement sits where a leading 'let' would
    -- be parsed as a let-statement, so mark it: 'parenify' parenthesizes
    -- a spliced 'let ... in ...' there to keep it a single expression.
    updStmt BodyStmt{} | i == firstChild = c { ctxtParentPrec = IsBodyStmt }
    updStmt LastStmt{} | i == firstChild = c { ctxtParentPrec = IsBodyStmt }
    updStmt _ = neverParen

    updStmtList :: [LStmt GhcPs (LHsExpr GhcPs)] -> TransformT m Context
    updStmtList [] = return neverParen
    updStmtList (ls:_)
        -- binders are in scope over tail of list (right child)
      | i > 0 = insertDependentRewrites neverParen bs ls
        -- lets are recursive in do-blocks
      | L _ (LetStmt _ bnds) <- ls =
          return $ addInScope' neverParen $ resolvedLocalBinders c bnds
      | otherwise = return $ fst $ updateSubstitution neverParen (fst bs)
      where
        bs = resolvedStmtBinders c ls

    updHsBind :: HsBind GhcPs -> Context
    updHsBind FunBind{..} =
      let rdr = unLoc fun_id
      in addBinders (addInScope neverParen [rdr]) [rdr]
    updHsBind _ = neverParen

    updTyClDecl :: TyClDecl GhcPs -> Context
    updTyClDecl SynDecl{..} = addInScope neverParen [unLoc tcdLName]
    updTyClDecl DataDecl{..} = addInScope neverParen [unLoc tcdLName]
    updTyClDecl ClassDecl{..} = addInScope neverParen [unLoc tcdLName]
    updTyClDecl _ = neverParen

    updPat :: Pat GhcPs -> Context
    updPat _ = neverParen

getPrec :: PprPrec -> Int
getPrec (PprPrec prec) = prec

#if __GLASGOW_HASKELL__ < 912
withPrec :: Context -> SourceText -> Int -> FixityDirection -> Int -> Context
withPrec c source prec dir i = c{ ctxtParentPrec = HasPrec fixity }
  where
    fixity = Fixity source prec d
#else
withPrec :: Context -> Int -> FixityDirection -> Int -> Context
withPrec c prec dir i = c{ ctxtParentPrec = HasPrec fixity }
  where
    fixity = Fixity prec d
#endif
    d = case dir of
      InfixL
        | i == firstChild -> InfixL
        | otherwise -> InfixN
      InfixR
        | i == firstChild -> InfixN
        | otherwise -> InfixR
      InfixN -> InfixN

-- | Create an empty 'Context' with given 'FixityEnv', rewriter, and dependent
-- rewrite generator. 'ctxtRenameInfo' defaults to 'emptyRenameInfo';
-- use 'emptyContextWithRenameInfo' to supply one.
emptyContext :: FixityEnv -> Rewriter -> Rewriter -> Context
emptyContext fEnv rw deps =
  emptyContextWithRenameInfo fEnv emptyRenameInfo rw deps

-- | 'emptyContext' but additionally seeded with a 'RenameInfo' side
-- table so retrie can see wildcard- and pun-introduced binders.
emptyContextWithRenameInfo
  :: FixityEnv -> RenameInfo -> Rewriter -> Rewriter -> Context
emptyContextWithRenameInfo
  ctxtFixityEnv ctxtRenameInfo ctxtRewriter ctxtDependents = Context{..}
  where
    ctxtBinders = []
    ctxtInScope = emptyAlphaEnv
    ctxtParentPrec = NeverParen
    ctxtSubst = Nothing
    ctxtScopeNames = emptyFsEnv
    ctxtMatchSpan = Nothing

-- Deal with Trees-That-Grow adding extension points
-- as the first child everywhere.
firstChild :: Int
firstChild = 1

-- | Add dependent rewrites to 'ctxtRewriter' if necessary.
insertDependentRewrites
  :: (Matchable k, MonadIO m)
  => Context -> ([RdrName], [Name]) -> k -> TransformT m Context
insertDependentRewrites c bs x = do
  r <- runRewriter id c (ctxtDependents c) x
  let
    c' = addInScope' c bs
  case r of
    NoMatch -> return c'
    MatchResult _ Template{..} -> do
      let
        rrs = fromMaybe [] tDependents
        ds = rewritesWithDependents rrs
        f = foldMap $
          mkLocalRewriterWithNames
            (riNameMap $ ctxtRenameInfo c') (ctxtInScope c')
      return c'
        { ctxtRewriter = f rrs <> ctxtRewriter c'
        , ctxtDependents = f ds <> ctxtDependents c'
        }

-- | Add set of binders to 'ctxtInScope'.
addInScope :: Context -> [RdrName] -> Context
addInScope c bs =
  c' { ctxtInScope = foldr extendAlphaEnv (ctxtInScope c') bs' }
  where
    (c', bs') = updateSubstitution c bs

-- | 'addInScope', additionally recording the binders' renamer-resolved
-- 'Name's (when known) in 'ctxtScopeNames'. Later entries win over
-- earlier ones for the same occurrence string, so as the traversal
-- descends the innermost binder is the one recorded -- matching how
-- shadowing resolves.
addInScope' :: Context -> ([RdrName], [Name]) -> Context
addInScope' c (bs, ns) =
  (addInScope c bs)
    { ctxtScopeNames = extendFsEnvList (ctxtScopeNames c)
        [ (occNameFS (nameOccName n), n) | n <- ns ]
    }

-- | Local binders introduced by a 'HsLocalBinds', consulting any
-- 'RenameInfo' attached to the 'Context' first. Falls back to
-- parser-pass collection when no 'RenameInfo' was supplied (without
-- paying for the 'scopeKey' subtree traversal) or when it has no
-- entry for this node. The second component carries the
-- renamer-resolved 'Name's when known (empty on the parser-pass
-- fallback), feeding 'ctxtScopeNames'.
resolvedLocalBinders :: Context -> HsLocalBinds GhcPs -> ([RdrName], [Name])
resolvedLocalBinders c lbs
  | hasScopeEntries (ctxtRenameInfo c)
  , Just k <- scopeKey lbs
  , Just ns <- lookupScopeNames k (ctxtRenameInfo c)
  = (map nameToRdr ns, ns)
  | otherwise = (collectLocalBinders CollNoDictBinders lbs, [])

-- | Binders introduced by patterns: the given parser-pass collection,
-- extended with the renamer's view of every pattern node present
-- ('patBindersIn') -- which includes binders implicit in
-- @RecordWildCards@ and @NamedFieldPuns@ patterns. Resolution is per
-- pattern node by exact span, so a synthesized binding node
-- contributes exactly the binders of the original patterns it reuses:
-- the one-pattern lambda a section rewrite builds from
-- @add x y = ...@ resolves @x@'s pattern but never sees @y@, and a
-- tuple-dispatch case alternative wrapping original patterns resolves
-- each of them, wildcard binders included.
resolvedPatBinders
  :: Data a => Context -> a -> [RdrName] -> ([RdrName], [Name])
resolvedPatBinders c x defaultBs = (defaultBs ++ implicit, hits)
  where
    hits = patBindersIn x (ctxtRenameInfo c)
    defaultFSs = map rdrFS defaultBs
    implicit = nubBy ((==) `on` rdrFS)
      [ r | n <- hits, let r = nameToRdr n, rdrFS r `notElem` defaultFSs ]

-- | Pattern binders introduced by a 'Match'.
resolvedMatchBinders
  :: Context -> Match GhcPs (LHsExpr GhcPs) -> ([RdrName], [Name])
resolvedMatchBinders c m =
  resolvedPatBinders c pats (collectPatsBinders CollNoDictBinders pats)
  where
    pats = matchPats m

-- | Binders introduced by a statement (in a @do@ block or a pattern
-- guard). @let@ and @pat <- e@ statements can bind via
-- @RecordWildCards@, so both consult the 'RenameInfo'.
resolvedStmtBinders :: Context -> LStmt GhcPs (LHsExpr GhcPs) -> ([RdrName], [Name])
resolvedStmtBinders c ls = case unLoc ls of
  LetStmt _ lbs -> resolvedLocalBinders c lbs
  BindStmt _ pat _ ->
    resolvedPatBinders c pat (collectPatsBinders CollNoDictBinders [pat])
  -- The compound forms bind whatever their inner statements bind;
  -- resolve those recursively so a @rec@, parallel-comprehension, or
  -- @then group by@ binder carries its renamer Name too. Collecting
  -- only at the statement level mirrors 'collectStmtBinders': a
  -- generic pattern walk would also pick up lambda and case binders
  -- inside the statement bodies, which do not scope past them.
  RecStmt{recS_stmts = stmts} ->
    foldMap (resolvedStmtBinders c) (unLoc stmts)
  ParStmt _ blocks _ _ ->
    foldMap
      (\(ParStmtBlock _ stmts _ _) -> foldMap (resolvedStmtBinders c) stmts)
      blocks
  TransStmt{trS_stmts = stmts} ->
    foldMap (resolvedStmtBinders c) stmts
  _ -> (collectLStmtBinders CollNoDictBinders ls, [])

-- | Add set of binders to 'ctxtBinders'.
addBinders :: Context -> [RdrName] -> Context
addBinders c bs = c { ctxtBinders = bs ++ ctxtBinders c }

-- Capture-avoiding substitution
--------------------------------------------------------------------------------

-- | Update the Context's substitution appropriately for a set of binders.
-- Returns a new Context and a potentially alpha-renamed set of binders.
updateSubstitution :: Context -> [RdrName] -> (Context, [RdrName])
updateSubstitution c rdrs =
  case ctxtSubst c of
    Nothing -> (c, rdrs)
    Just sub ->
      let
        -- This prevents substituting for 'x' under a binding for 'x'.
        sub' = deleteSubst sub $ map rdrFS rdrs
        -- Compute free vars of substitution that could possibly be captured.
        fvs = substFVs sub'
        -- Partition binders into noncapturing and capturing.
        (noncapturing, capturing) =
          partitionEithers $ map (updateBinder fvs) rdrs
        -- Extend substitution with alpha-renamings.
        alphaSub = foldl' (uncurry . extendSubst) sub'
          [ (rdrFS rdr, HoleRdr rdr') | (rdr, rdr') <- capturing ]
        -- There are no telescopes in source Haskell, so order doesn't matter.
        -- Capturing should be rare, so put it first to avoid quadratic append.
        rdrs' = map snd capturing ++ noncapturing
      in (c { ctxtSubst = Just alphaSub }, rdrs')

-- | Check if RdrName is in FreeVars.
--
-- If so, return a pair of it and its new name (Right).
-- If not, return it unchanged (Left).
updateBinder :: FreeVars -> RdrName -> Either RdrName (RdrName, RdrName)
updateBinder fvs rdr
  | elemFVs rdr fvs = Right (rdr, renameBinder rdr fvs)
  | otherwise = Left rdr

-- | Given a RdrName, rename it to something not in given FreeVars.
--
--   x => x1
--   x1 => x2
--   x9 => x10
--
-- etc.
--
-- Only works on unqualified RdrNames. This is fine, as we only use this to
-- rename local binders.
renameBinder :: RdrName -> FreeVars -> RdrName
renameBinder rdr fvs = headNoWarn
  [ rdr'
  | i <- [n..]
  , let rdr' = mkVarUnqual $ mkFastString $ baseName ++ show i
  , not $ rdr' `elemFVs` fvs
  ]
  where
    (ds, rest) = span isDigit $ reverse $ occNameString $ occName rdr

    baseName = reverse rest

    -- We build with -Wall -Werror, and there is a warning about how `head` is
    -- partial. Using `head` is safe here because the list is infinite, so the
    -- nil case is impossible. Define our own to avoid the warning.
    headNoWarn (x:_) = x
    headNoWarn _ = error "headNoWarn: impossible!"

    n :: Int
    n | null ds = 1
      | otherwise = read (reverse ds) + 1
