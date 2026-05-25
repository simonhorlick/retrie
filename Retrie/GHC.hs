-- Copyright (c) 2025 Andrew Farmer
-- Copyright (c) 2020-2024 Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RecordWildCards #-}
module Retrie.GHC
  ( module Retrie.GHC
  , module GHC.Data.Bag
  , module GHC.Data.FastString
  , module GHC.Data.FastString.Env
  , module GHC.Driver.Errors
  , module GHC.Hs
  , module GHC.Hs.Expr
  , module GHC.Parser.Annotation
  , module GHC.Parser.Errors.Ppr
  , module GHC.Plugins
  , module GHC.Types.Basic
  , module GHC.Types.Error
  , module GHC.Types.Fixity
  , module GHC.Types.Name
  , module GHC.Types.Name.Occurrence
  , module GHC.Types.Name.Reader
  , module GHC.Types.SourceText
  , module GHC.Types.SrcLoc
  , module GHC.Types.Unique
  , module GHC.Types.Unique.FM
  , module GHC.Types.Unique.Set
  , module GHC.Unit.Module.Name
  , module GHC.Utils.Outputable
  ) where

import GHC
import GHC.Builtin.Names
import GHC.Data.Bag
import GHC.Data.FastString
import GHC.Data.FastString.Env
import GHC.Driver.Errors
import GHC.Hs
import GHC.Hs.Expr
import GHC.Parser.Annotation
import GHC.Parser.Errors.Ppr
import GHC.Plugins (showSDoc)
import GHC.Types.Basic hiding (EP)
import GHC.Types.Error
import GHC.Types.Fixity
import GHC.Types.Name
import GHC.Types.Name.Occurrence
import GHC.Types.Name.Reader
import GHC.Types.SourceText
import GHC.Types.SrcLoc
import GHC.Types.Unique
import GHC.Types.Unique.FM
import GHC.Types.Unique.Set
import Language.Haskell.Syntax.Basic as GHC.Unit.Module.Name
import GHC.Utils.Outputable (Outputable (ppr))

import Data.Bifunctor (second)
#if __GLASGOW_HASKELL__ < 914
#else
import qualified Data.List.NonEmpty as NE
#endif
import Data.Maybe

-- | The binds of a group as a list, across the 9.12 change of
-- 'LHsBinds' from a 'Bag' to a plain list.
hsBindsToList :: LHsBinds GhcPs -> [LHsBind GhcPs]
#if __GLASGOW_HASKELL__ < 912
hsBindsToList = bagToList
#else
hsBindsToList = id
#endif

cLPat :: LPat (GhcPass p) -> LPat (GhcPass p)
cLPat = id

-- | Only returns located pat if there is a genuine location available.
dLPat :: LPat (GhcPass p) -> Maybe (LPat (GhcPass p))
dLPat = Just

-- | Will always give a location, but it may be noSrcSpan.
dLPatUnsafe :: LPat (GhcPass p) -> LPat (GhcPass p)
dLPatUnsafe = id

rdrFS :: RdrName -> FastString
rdrFS (Qual m n) = mconcat [moduleNameFS m, fsDot, occNameFS n]
rdrFS rdr = occNameFS (occName rdr)

fsDot :: FastString
fsDot = mkFastString "."

#if __GLASGOW_HASKELL__ < 914
varRdrName :: HsExpr p -> Maybe (LIdP p)
#else
varRdrName :: HsExpr p -> Maybe (LIdOccP p)
#endif
varRdrName (HsVar _ n) = Just n
varRdrName _ = Nothing

#if __GLASGOW_HASKELL__ < 914
tyvarRdrName :: HsType p -> Maybe (LIdP p)
#else
tyvarRdrName :: HsType p -> Maybe (LIdOccP p)
#endif
tyvarRdrName (HsTyVar _ _ n) = Just n
tyvarRdrName _ = Nothing

-- | On GHC >= 9.14 constructor-pattern type arguments are invisible
-- patterns in the PrefixCon argument list rather than a separate tyargs
-- field. Retrie ignores them, as it ignored the tyargs field on older GHCs.
-- TODO: Handle this case properly.
dropInvisPats :: [LPat GhcPs] -> [LPat GhcPs]
#if __GLASGOW_HASKELL__ < 914
dropInvisPats = id
#else
dropInvisPats = dropHsConPatTyArgs
#endif

grhssList :: GRHSs GhcPs body -> [LGRHS GhcPs body]
#if __GLASGOW_HASKELL__ < 914
grhssList = grhssGRHSs
#else
grhssList = NE.toList . grhssGRHSs
#endif

-- | A guard-alternative list, as carried by 'HsMultiIf', as a plain
-- list across the 9.14 change to 'NonEmpty'.
#if __GLASGOW_HASKELL__ < 914
altsToList :: [a] -> [a]
altsToList = id
#else
altsToList :: NE.NonEmpty a -> [a]
altsToList = NE.toList
#endif

-- fixityDecls :: HsModule -> [(LIdP p, Fixity)]
fixityDecls :: HsModule GhcPs -> [(LocatedN RdrName, Fixity)]
fixityDecls m =
  [ (nm, fixity)
  | L _ (SigD _ (FixSig _ (FixitySig _ nms fixity))) <- hsmodDecls m
  , nm <- nms
  ]

ruleInfo :: RuleDecl GhcPs -> [RuleInfo]
#if __GLASGOW_HASKELL__ < 914
ruleInfo (HsRule _ (L _ riName) _ tyBs valBs riLHS riRHS) =
#else
ruleInfo (HsRule _ (L _ riName) _ (RuleBndrs _ tyBs valBs) riLHS riRHS) =
#endif
  let
    riQuantifiers =
      map unLoc (tyBindersToLocatedRdrNames (fromMaybe [] tyBs)) ++
      ruleBindersToQs valBs
  in [ RuleInfo{..} ]

ruleBindersToQs :: [LRuleBndr GhcPs] -> [RdrName]
ruleBindersToQs bs = catMaybes
  [ case b of
      RuleBndr _ (L _ v) -> Just v
      RuleBndrSig _ (L _ v) _ -> Just v
  | L _ b <- bs
  ]

tyBindersToLocatedRdrNames :: [LHsTyVarBndr s GhcPs] -> [LocatedN RdrName]
#if __GLASGOW_HASKELL__ < 912
tyBindersToLocatedRdrNames = map getTyVarLName
  where
    getTyVarLName (L _ (UserTyVar _ _ ln)) = ln
    getTyVarLName (L _ (KindedTyVar _ _ ln _)) = ln
    getTyVarLName (L _ (XTyVarBndr _)) = error "tyBindersToLocatedRdrNames: XTyVarBndr not supported"
#else
-- Note: we can't use 'hsLTyVarNames' here because it throws away the wildcards,
-- and we _must_ preserve the length of the list. Also can't use some of the
-- other single-binder variants of hsTyVarLName because they throw away the
-- location on the RdrName result.
tyBindersToLocatedRdrNames = map (fromMaybe mkWildcard . hsTyVarLName . unLoc)
  where
    mkWildcard = error "tyBindersToLocatedRdrNames: wildcard type binder not supported"
#endif

data RuleInfo = RuleInfo
  { riName :: RuleName
  , riQuantifiers :: [RdrName]
  , riLHS :: LHsExpr GhcPs
  , riRHS :: LHsExpr GhcPs
  }

overlaps :: SrcSpan -> SrcSpan -> Bool
overlaps (RealSrcSpan s1 _) (RealSrcSpan s2 _) =
     srcSpanFile s1 == srcSpanFile s2 &&
     ((srcSpanStartLine s1, srcSpanStartCol s1) `within` s2 ||
      (srcSpanEndLine s1, srcSpanEndCol s1) `within` s2)
overlaps _ _ = False

within :: (Int, Int) -> RealSrcSpan -> Bool
within (l,p) s =
  srcSpanStartLine s <= l &&
  srcSpanStartCol s <= p  &&
  srcSpanEndLine s >= l   &&
  srcSpanEndCol s >= p

lineCount :: [SrcSpan] -> Int
lineCount ss = sum
  [ srcSpanEndLine s - srcSpanStartLine s + 1
  | RealSrcSpan s _ <- ss
  ]

showRdrs :: [RdrName] -> String
showRdrs = show . map (occNameString . occName)

uniqBag :: Uniquable a => [(a,b)] -> UniqFM a [b]
uniqBag = listToUFM_C (++) . map (second pure)

getRealLoc :: SrcLoc -> Maybe RealSrcLoc
getRealLoc (RealSrcLoc l _) = Just l
getRealLoc _ = Nothing

getRealSpan :: SrcSpan -> Maybe RealSrcSpan
getRealSpan (RealSrcSpan s _) = Just s
getRealSpan _ = Nothing

-- | Extract @m_pats@ as a plain list, hiding the post-9.12 outer
-- 'Located' wrapper.
matchPats :: Match (GhcPass p) body -> [LPat (GhcPass p)]
#if __GLASGOW_HASKELL__ < 912
matchPats = m_pats
#else
matchPats = unLoc . m_pats
#endif

#if __GLASGOW_HASKELL__ < 912
-- | Compat shim for the 'HasLoc' class 'GHC.Parser.Annotation' gained
-- in GHC 9.10, covering the location types retrie uses it at.
class HasLoc a where
  getHasLoc :: a -> SrcSpan

instance HasLoc (SrcSpanAnn' ann) where
  getHasLoc = locA

instance HasLoc (GenLocated SrcSpan e) where
  getHasLoc = getLoc
#endif
