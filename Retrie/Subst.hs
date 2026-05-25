-- Copyright (c) 2025 Andrew Farmer
-- Copyright (c) 2020-2024 Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}
module Retrie.Subst
  ( subst
  ) where

import Control.Monad.Writer.Strict
import Data.Generics
import Data.Maybe (mapMaybe)

import Retrie.Context
import Retrie.ExactPrint
import Retrie.Expr
import Retrie.GHC
import Retrie.RenameInfo (lookupWildcardInfo)
import Retrie.Substitution
import Retrie.SYB
import Retrie.Types

------------------------------------------------------------------------

-- | Perform the given 'Substitution' on an AST, avoiding variable capture
-- by alpha-renaming binders as needed.
subst
  :: (MonadIO m, Data ast)
  => Substitution
  -> Context
  -> ast
  -> TransformT m ast
subst sub ctxt =
  everywhereMWithContextBut bottomUp (const False) updateContext f ctxt'
  where
    ctxt' = ctxt { ctxtSubst = Just sub }
    f c =
      mkM (substExpr c)
        `extM` substPat c
        `extM` substType c
        `extM` substHsMatchContext c
        `extM` substBind c

lookupHoleVar :: RdrName -> Context -> Maybe HoleVal
lookupHoleVar rdr ctxt = do
  sub <- ctxtSubst ctxt
  lookupSubst (rdrFS rdr) sub

substExpr
  :: MonadIO m
  => Context
  -> LHsExpr GhcPs
  -> TransformT m (LHsExpr GhcPs)
substExpr ctxt e@(L l1 (HsVar x (L l2 v))) =
  case lookupHoleVar v ctxt of
    Just (HoleExpr eA) -> do
      -- lift $ liftIO $ debugPrint Loud "substExpr:HoleExpr:e" [showAst e]
      -- lift $ liftIO $ debugPrint Loud "substExpr:HoleExpr:eA" [showAst eA]
      e0 <- graftA (unparen <$> eA)
#if __GLASGOW_HASKELL__ < 912
      e1 <- if hasComments e0 then return e0 else transferEntryDP e e0
#else
      e1 <- if hasComments e0 then return e0 else return $ transferEntryDP e e0
#endif
      e2 <- transferAnnsT isComma e e1
      -- let e'' = setEntryDP e' (SameLine 1)
      -- lift $ liftIO $ debugPrint Loud "substExpr:HoleExpr:e2" [showAst e2]
      parenify ctxt e2
    Just (HoleRdr rdr) ->
      return $ L l1 $ HsVar x $ L l2 rdr
    _ -> return e
substExpr _ e = return e

substPat
  :: MonadIO m
  => Context
  -> LPat GhcPs
  -> TransformT m (LPat GhcPs)
substPat ctxt (dLPat -> Just p@(L l1 (VarPat x _vl@(L l2 v)))) = fmap cLPat $
  case lookupHoleVar v ctxt of
    Just (HolePat pA) -> do
      -- lift $ liftIO $ debugPrint Loud "substPat:HolePat:p" [showAst p]
      -- lift $ liftIO $ debugPrint Loud "substPat:HolePat:pA" [showAst pA]
      p' <- graftA (unparenP <$> pA)
      p0 <- transferEntryAnnsT isComma p p'
      -- the relevant entry delta is sometimes attached to
      -- the OccName and not to the VarPat.
      -- This seems to be the case only when the pattern comes from a lhs,
      -- whereas it has no annotations in patterns found in rhs's.
      -- tryTransferEntryDPT vl p'
      parenifyP ctxt p0
    Just (HoleRdr rdr) ->
      return $ L l1 $ VarPat x $ L l2 rdr
    _ -> return p
substPat ctxt (L l (ConPat ext con (RecCon recFields))) = do
  recFields' <- unpunRenamedFields ctxt recFields
  let p' = L l (ConPat ext con (RecCon recFields'))
  case getHasLoc l of
    RealSrcSpan sp _
      | Just wildInfo <- lookupWildcardInfo sp (ctxtRenameInfo ctxt) ->
          expandWildcardPat ctxt p' l ext con recFields' wildInfo
    _ -> return p'
substPat _ p = return p

-- | Un-pun any explicitly punned field whose binder was alpha-renamed
-- during capture-avoiding substitution: @C{x}@ whose binder was
-- renamed to @x1@ must print as @C{x = x1}@, since a pun can only
-- bind a variable spelled exactly like the label.
--
-- The parser fills a pun's right-hand side with an unprintable
-- placeholder 'VarPat' (a @pun-right-hand-side@ 'RdrName' with no
-- location), so the rename never lands inside the field; look the
-- label up in the substitution instead, and build the explicit
-- right-hand side from the renamed binder.
unpunRenamedFields
  :: Monad m
  => Context
  -> HsRecFields GhcPs (LPat GhcPs)
  -> TransformT m (HsRecFields GhcPs (LPat GhcPs))
unpunRenamedFields ctxt recFields = do
  flds' <- mapM unpun (rec_flds recFields)
  return recFields { rec_flds = flds' }
  where
    unpun (L l (HsFieldBind _ lbl _ True))
      | Just (HoleRdr binder') <- lookupHoleVar (unLoc (foLabel (unLoc lbl))) ctxt = do
#if __GLASGOW_HASKELL__ >= 912
          eqAnn <- Just . EpTok <$> mkAnchor (SameLine 1)
#else
          eqAnn <- mkEpAnn (SameLine 0) [AddEpAnn AnnEqual (EpaDelta (SameLine 1) [])]
#endif
          binderRdr <- mkLocA (SameLine 0) binder'
          rhs' <- mkVarPat binderRdr
          return $ L l (HsFieldBind eqAnn lbl rhs' False)
    unpun f = return f

-- | Rewrite @C{..}@ to @C{f = b', ..}@ for every wildcard binder
-- @f@ whose @b@ has been alpha-renamed to @b'@ during
-- capture-avoiding substitution. Untouched wildcard binders stay
-- under @..@, and the @..@ itself is always kept — even when every
-- binder it introduced was renamed — so the user's pattern is
-- perturbed as little as possible.
expandWildcardPat
  :: MonadIO m
  => Context
  -> LPat GhcPs
  -> SrcSpanAnnA
  -> XConPat GhcPs
  -> XRec GhcPs (ConLikeP GhcPs)
  -> HsRecFields GhcPs (LPat GhcPs)
  -> [(RdrName, RdrName)]
  -> TransformT m (LPat GhcPs)
expandWildcardPat ctxt orig l ext con recFields wildInfo = do
  let renamed = mapMaybe pickRenamed wildInfo
  case renamed of
    [] -> return orig
    _  -> do
      -- Every appended field needs a trailing comma: the @..@ always
      -- follows the last one.
      newFlds <- commaSeparate True
        =<< mapM (uncurry mkExplicitField) renamed
      let newRecFields = recFields
            { rec_flds   = rec_flds recFields ++ newFlds
            , rec_dotdot = spaceDotDot <$> rec_dotdot recFields
            }
      return $ L l (ConPat ext con (RecCon newRecFields))
  where
    pickRenamed :: (RdrName, RdrName) -> Maybe (RdrName, RdrName)
    pickRenamed (field, binder) =
      case lookupHoleVar binder ctxt of
        Just (HoleRdr binder') -> Just (field, binder')
        _                      -> Nothing

    -- The @..@ token originally sat flush against the opening brace;
    -- once explicit fields precede it, print it one space after the
    -- last field's trailing comma.
#if __GLASGOW_HASKELL__ >= 912
    spaceDotDot (L _ dots) = L (EpaDelta noSrcSpan (SameLine 1) []) dots
#else
    spaceDotDot = id
#endif

-- | Add a trailing comma annotation to every element but the last, and
-- to the last one too when something (e.g. a @..@) still follows it.
commaSeparate
  :: Monad m
  => Bool
  -> [LocatedA e]
  -> TransformT m [LocatedA e]
commaSeparate commaOnLast flds = case reverse flds of
  [] -> return []
  lastF:revInit -> do
    lastF' <- if commaOnLast then addTrailingComma lastF else return lastF
    revInit' <- mapM addTrailingComma revInit
    return $ reverse (lastF' : revInit')
  where
#if __GLASGOW_HASKELL__ >= 912
    addTrailingComma (L (EpAnn anc (AnnListItem ts) cs) e) = do
      comma <- AddCommaAnn . EpTok <$> mkAnchor (SameLine 0)
      return $ L (EpAnn anc (AnnListItem (ts ++ [comma])) cs) e
#else
    addTrailingComma (L (SrcSpanAnn an sp) e) = do
      let comma = AddCommaAnn (EpaDelta (SameLine 0) [])
          an' = case an of
            EpAnnNotUsed ->
              EpAnn (spanAsAnchor sp) (AnnListItem [comma]) emptyComments
            EpAnn anc (AnnListItem ts) cs ->
              EpAnn anc (AnnListItem (ts ++ [comma])) cs
      return $ L (SrcSpanAnn an' sp) e
#endif

-- | An explicit @field = binder@ record pattern field (no pun).
mkExplicitField
  :: Monad m
  => RdrName -- ^ field
  -> RdrName -- ^ binder
  -> TransformT m (LHsRecField GhcPs (LPat GhcPs))
mkExplicitField field binder = do
  fieldRdr <- mkLocA (SameLine 0) field
  let foc = FieldOcc noExtField fieldRdr
#if __GLASGOW_HASKELL__ >= 912
  focL <- mkLocA (SameLine 0) foc
#else
  -- 'FieldOcc' is annotated with 'NoEpAnns' here, which has no 'Monoid',
  -- so 'mkLocA' can't be used.
  s <- uniqueSrcSpanT
  an <- mkEpAnn (SameLine 0) NoEpAnns
  let focL = L (SrcSpanAnn an s) foc
#endif
  binderRdr <- mkLocA (SameLine 0) binder
  rhs <- mkVarPat binderRdr
#if __GLASGOW_HASKELL__ >= 912
  eqAnn <- Just . EpTok <$> mkAnchor (SameLine 1)
#else
  eqAnn <- mkEpAnn (SameLine 0) [AddEpAnn AnnEqual (EpaDelta (SameLine 1) [])]
#endif
  let hfb = HsFieldBind eqAnn focL rhs False
  mkLocA (SameLine 0) hfb

substType
  :: MonadIO m
  => Context
  -> LHsType GhcPs
  -> TransformT m (LHsType GhcPs)
substType ctxt ty
  | Just (L _ v) <- tyvarRdrName (unLoc ty)
  , Just (HoleType tyA) <- lookupHoleVar v ctxt = do
    -- lift $ liftIO $ debugPrint Loud "substType:HoleType:ty" [showAst ty]
    -- lift $ liftIO $ debugPrint Loud "substType:HoleType:tyA" [showAst tyA]
    ty' <- graftA (unparenT <$> tyA)
    ty0 <- transferEntryAnnsT isComma ty ty'
    parenifyT ctxt ty0
substType _ ty = return ty

-- You might reasonably think that we would replace the RdrName in FunBind...
-- but no, exactprint only cares about the RdrName in the MatchGroup matches,
-- which are here. In case that changes in the future, we define substBind too.
substHsMatchContext
  :: Monad m
  => Context
#if __GLASGOW_HASKELL__ < 912
  -> HsMatchContext GhcPs
  -> TransformT m (HsMatchContext GhcPs)
substHsMatchContext ctxt (FunRhs (L l v) f s)
  | Just (HoleRdr rdr) <- lookupHoleVar v ctxt
  = return $ FunRhs (L l rdr) f s
#else
  -> HsMatchContext (LIdP GhcPs)
  -> TransformT m (HsMatchContext (LIdP GhcPs))
substHsMatchContext ctxt (FunRhs (L l v) f s _)
  | Just (HoleRdr rdr) <- lookupHoleVar v ctxt
  = return $ FunRhs (L l rdr) f s (AnnFunRhs NoEpTok [] [])
#endif
substHsMatchContext _ other = return other

substBind
  :: Monad m
  => Context
  -> HsBind GhcPs
  -> TransformT m (HsBind GhcPs)
substBind ctxt fb@FunBind{}
  | L l v <- fun_id fb
  , Just (HoleRdr rdr) <- lookupHoleVar v ctxt =
    return fb { fun_id = L l rdr }
substBind _ other = return other
