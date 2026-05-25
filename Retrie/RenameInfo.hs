-- Copyright (c) 2025 Andrew Farmer
-- Copyright (c) 2020-2024 Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Lets a user supply a 'RenamedSource' so retrie can see binders
-- introduced by features the parser pass cannot resolve, such as
-- @RecordWildCards@ and @NamedFieldPuns@.
--
-- See 'mkRenameInfo' and 'Retrie.Monad.applyWithRenameInfo'.
module Retrie.RenameInfo
  ( RenameInfo
  , emptyRenameInfo
  , mkRenameInfo
    -- * Name lookup
  , NameMap
  , riNameMap
  , lookupNameAt
    -- * Internal
  , lookupScopeNames
  , lookupWildcardInfo
  , hasScopeEntries
  , patBindersIn
  , scopeKey
  , nameToRdr
  ) where

import Data.Data (Data)
import Data.Generics (everything, extQ, listify, mkQ)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (mapMaybe)
import GHC (RenamedSource)

import Retrie.GHC

-- | Side-table derived from a 'RenamedSource'.
--
-- The 'riScope' map records, for each 'HsLocalBinds' lookup key
-- (derived via 'scopeKey'), the full list of binders the renamer sees
-- introduced by that binds block — including binders implicit in
-- @RecordWildCards@ and @NamedFieldPuns@ patterns.
--
-- The 'riPatBinders' map records, for every pattern node, the binders
-- the renamer sees that pattern introduce, keyed by the pattern's own
-- 'RealSrcSpan'. The exact-span keying is what lets binder resolution
-- survive rewrite synthesis: builders never invent binders, they
-- rearrange original pattern subtrees (which keep their spans), so a
-- consumer resolves exactly the patterns physically present in the
-- node it is looking at — no more (a one-pattern lambda a section
-- rewrite builds from @add x y = ...@ finds only @x@'s entry) and no
-- less (a tuple-dispatch case alternative wrapping original patterns
-- in a synthesized 'TuplePat' still finds each original pattern's
-- entry, including implicit wildcard binders).
--
-- The 'riWildcards' map records, for each @ConPat@ whose record fields
-- use a @..@ wildcard, the list of @(fieldName, binderName)@ pairs the
-- renamer expanded the wildcard to. Lets consumers (notably
-- 'Retrie.Subst.subst') rewrite a @C{..}@ pattern to an explicit
-- @C{ f = b' }@ form when a wildcard binder has been alpha-renamed
-- during capture-avoiding substitution.
--
-- 'RealSrcSpan' keys are filename-qualified, so a single 'RenameInfo'
-- can safely hold entries for many modules. Build one per module with
-- 'mkRenameInfo' and combine them with @('<>')@.
data RenameInfo = RenameInfo
  { riScope       :: Map RealSrcSpan [Name]
    -- ^ Binder 'Name's per 'HsLocalBinds' scope key. A binds block has
    -- no span of its own and is only ever consumed wholesale (a where
    -- clause travels with its body as one node), so the 'scopeKey'
    -- heuristic is a safe correlation for it. See 'lookupScopeNames'.
  , riPatBinders  :: Map RealSrcSpan [Name]
    -- ^ Binder 'Name's per pattern node, keyed by the pattern's exact
    -- span. Consumed via 'patBindersIn'.
  , riWildcards   :: Map RealSrcSpan [(RdrName, RdrName)]
  , riNameMap     :: NameMap
    -- ^ Map from the 'RealSrcSpan' of an 'LIdP' (variable reference
    -- or binder) to the renamer-resolved 'Name'. Lets retrie's
    -- matcher key variables by 'Unique' instead of textual 'RdrName',
    -- so that qualified, unqualified, and aliased references to the
    -- same definition are recognised as equal.
  }

-- | See 'riNameMap'.
type NameMap = Map RealSrcSpan Name

-- | Left-biased union. Distinct modules cannot collide (their spans
-- carry different filenames); if the same renamed source is supplied
-- twice the first copy wins.
instance Semigroup RenameInfo where
  RenameInfo a1 b1 c1 d1 <> RenameInfo a2 b2 c2 d2 =
    RenameInfo
      (Map.union a1 a2)
      (Map.union b1 b2)
      (Map.union c1 c2)
      (Map.union d1 d2)

instance Monoid RenameInfo where
  mempty = emptyRenameInfo

-- | No rename info. Retrie falls back to parser-pass binder collection,
-- which does not see wildcard-introduced binders.
emptyRenameInfo :: RenameInfo
emptyRenameInfo = RenameInfo Map.empty Map.empty Map.empty Map.empty

-- | Does this 'RenameInfo' carry any 'HsLocalBinds' scope entries?
-- Lets consumers skip computing a 'scopeKey' (a subtree traversal)
-- when no 'RenameInfo' was supplied, the common case.
hasScopeEntries :: RenameInfo -> Bool
hasScopeEntries = not . Map.null . riScope

-- | Look up the renamer-resolved 'Name' at a parser-pass 'SrcSpan'.
-- Returns 'Nothing' for spans not in the map (e.g. when no
-- 'RenameInfo' was supplied, or for synthesised AST nodes).
lookupNameAt :: SrcSpan -> NameMap -> Maybe Name
lookupNameAt sp m = getRealSpan sp >>= flip Map.lookup m

-- | Look up the binders the renamer sees a 'HsLocalBinds' introduce,
-- as renamer-resolved 'Name's. The key must be derived using
-- 'scopeKey'.
lookupScopeNames :: RealSrcSpan -> RenameInfo -> Maybe [Name]
lookupScopeNames k ri = Map.lookup k (riScope ri)

-- | The renamer-resolved binders of every pattern node inside the
-- given parser-pass value that has a 'riPatBinders' entry. Resolution
-- is per pattern node by exact span, so a synthesized pattern (no
-- real span, or a span the renamed source never saw) contributes only
-- through the original patterns it reuses, and each of those resolves
-- to exactly its own binders — including binders implicit in
-- @RecordWildCards@ and @NamedFieldPuns@ patterns, which parser-pass
-- collection cannot see.
patBindersIn :: Data a => a -> RenameInfo -> [Name]
patBindersIn x ri
  | Map.null (riPatBinders ri) = []
  | otherwise = concat
      [ ns
      | lp <- listify (\(_ :: LPat GhcPs) -> True) x
      , Just sp <- [getRealSpan (getLocA lp)]
      , Just ns <- [Map.lookup sp (riPatBinders ri)]
      ]

-- | Look up the @(field, binder)@ pairs the renamer expanded a
-- record-wildcard @ConPat@ into. The key is the @RealSrcSpan@ of the
-- @ConPat@ as it appears in the parsed source (preserved through
-- renaming).
lookupWildcardInfo :: RealSrcSpan -> RenameInfo -> Maybe [(RdrName, RdrName)]
lookupWildcardInfo k ri = Map.lookup k (riWildcards ri)

-- | Build a 'RenameInfo' from a 'RenamedSource'. The walk emits:
--
--   * one 'riScope' entry per 'HsLocalBinds' wherever it occurs
--     (@let@ expressions, @where@ clauses, @do@-block @let@
--     statements),
--   * one 'riPatBinders' entry per pattern node, keyed by the
--     pattern's exact span (this covers function\/lambda\/case clause
--     patterns and @do@-block\/guard pattern bindings, at every
--     nesting depth), and
--   * one 'riWildcards' entry per @ConPat@ that uses a record
--     wildcard (@C{..}@ or @C{f, ..}@), recording the @(field,
--     binder)@ pairs the renamer expanded the @..@ into.
--
-- The 'RenameInfo' must be built from the same source text as the
-- module retrie parses and rewrites: entries are correlated by
-- 'RealSrcSpan' (see 'scopeKey'), so a 'RenamedSource' from a stale
-- or edited copy of the file yields keys that silently miss (falling
-- back to parser-pass binder collection) or, worse, resolve to
-- binder lists that no longer reflect the code.
mkRenameInfo :: RenamedSource -> RenameInfo
#if __GLASGOW_HASKELL__ >= 912
mkRenameInfo (grp, _imports, _exports, _docs, _modName) =
#else
mkRenameInfo (grp, _imports, _exports, _docs) =
#endif
  RenameInfo
    { riScope = Map.fromList $ everything (++) (mkQ [] lbsEntry) grp
    , riPatBinders = Map.fromList $ everything (++) (mkQ [] patEntry) grp
    , riWildcards = Map.fromList $
        everything (++) (mkQ [] wildcardEntry) grp
    , riNameMap = Map.fromList nameEntries
    }
  where
    nameEntries =
      everything (++)
        (mkQ [] hsVarName `extQ` varPatName `extQ` funBindName) grp
    -- Record the renamer's 'Name' at every variable reference site.
    -- The key is the 'RealSrcSpan' of the 'LIdP', which is preserved
    -- through renaming so a parser-pass 'LIdP' at the same position
    -- gets the same key.
    hsVarName :: LHsExpr GhcRn -> [(RealSrcSpan, Name)]
    hsVarName (L _ (HsVar _ lident))
      | Just sp <- getRealSpan (getLocA lident)
        = [(sp, identNameRn lident)]
    -- A field-selector occurrence renames to an 'XExpr' extension node
    -- rather than an 'HsVar'. Record it too: a rewrite template that
    -- references a selector can have that reference captured by a
    -- call-site binder of the same occurrence string (e.g. a
    -- NamedFieldPuns pattern binder), and capture detection resolves
    -- the template's references through this map.
#if __GLASGOW_HASKELL__ >= 912
    hsVarName (L _ (XExpr (HsRecSelRn fo)))
#else
    hsVarName (L _ (HsRecSel _ fo))
#endif
      | Just sp <- getRealSpan (getLocA (foLabel fo))
        = [(sp, foName fo)]
    hsVarName _ = []

    varPatName :: LPat GhcRn -> [(RealSrcSpan, Name)]
    varPatName (L _ (VarPat _ ln))
      | Just sp <- getRealSpan (getLocA ln)
        = [(sp, unLoc ln)]
    varPatName _ = []

    funBindName :: HsBindLR GhcRn GhcRn -> [(RealSrcSpan, Name)]
    funBindName FunBind{fun_id = ln}
      | Just sp <- getRealSpan (getLocA ln)
        = [(sp, unLoc ln)]
    funBindName _ = []


    -- One entry per pattern node, keyed by the pattern's own span.
    -- Wherever a pattern binds -- clause, lambda, case alternative,
    -- @pat <- e@ statement, or nested inside another pattern -- its
    -- entry records exactly its own binders, so consumers resolve the
    -- patterns physically present in a node instead of correlating
    -- whole binding nodes (which rewrite synthesis recombines).
    patEntry :: LPat GhcRn -> [(RealSrcSpan, [Name])]
    patEntry lp = case getRealSpan (getLocA lp) of
      Just sp -> [(sp, collectPatBinders CollNoDictBinders lp)]
      Nothing -> []

    -- Covers every 'HsLocalBinds' in the module: @let@ expressions,
    -- @where@ clauses ('grhssLocalBinds'), and @do@-block @let@s.
    -- Local binds are only ever consumed wholesale (a where clause
    -- travels with the body as one node), so 'scopeKey' correlation
    -- is safe for them.
    lbsEntry :: HsLocalBinds GhcRn -> [(RealSrcSpan, [Name])]
    lbsEntry lbs = case scopeKey lbs of
      Just k -> [(k, collectLocalBinders CollNoDictBinders lbs)]
      Nothing -> []

    wildcardEntry
      :: LPat GhcRn -> [(RealSrcSpan, [(RdrName, RdrName)])]
    wildcardEntry lp = case (getRealSpan (getLocA lp), unLoc lp) of
      (Just sp, ConPat _ _ (RecCon flds))
        | Just (L _ _) <- rec_dotdot flds ->
            [(sp, wildcardFieldPairs flds)]
      _ -> []

-- | Extract the @(field, binder)@ pairs corresponding to fields the
-- renamer introduced from a @..@ wildcard. We identify wildcard-fed
-- fields by their 'hfbRHS' being a 'VarPat' located at the same
-- 'SrcSpan' as the field selector — i.e. the renamer synthesised the
-- binder from the field name. Any field with a distinct RHS location
-- was written explicitly by the user.
wildcardFieldPairs
  :: HsRecFields GhcRn (LPat GhcRn) -> [(RdrName, RdrName)]
wildcardFieldPairs HsRecFields{rec_flds, rec_dotdot} =
  case rec_dotdot of
    Nothing  -> []
    Just dot -> mapMaybe (toPair (getHasLoc dot)) rec_flds
  where
    toPair :: SrcSpan -> LHsRecField GhcRn (LPat GhcRn) -> Maybe (RdrName, RdrName)
    toPair dotLoc (L _ (HsFieldBind _ (L lhsLoc occ) rhs _pun))
      | getHasLoc lhsLoc == dotLoc
      , L _ (VarPat _ (L _ binder)) <- rhs
      = Just (nameToRdr (foName occ), nameToRdr binder)
    toPair _ _ = Nothing

-- | The renamer's 'Name' for a field-selector occurrence. GHC 9.12
-- moved the resolved 'Name' into @foLabel@, displacing the original
-- 'RdrName' into @foExt@; before that the 'Name' lived in @foExt@ and
-- @foLabel@ kept the 'RdrName'. Either way @foLabel@ carries the
-- location.
foName :: FieldOcc GhcRn -> Name
#if __GLASGOW_HASKELL__ >= 912
foName = unLoc . foLabel
#else
foName = foExt
#endif

-- | Extract the @Name@ from an @LIdP GhcRn@ on the rename pass. GHC
-- 9.14 changed the payload to a @WithUserRdr Name@; earlier versions
-- carried a bare @Name@.
#if __GLASGOW_HASKELL__ >= 913
identNameRn :: GenLocated l (WithUserRdr Name) -> Name
identNameRn = unLocWithUserRdr
#else
identNameRn :: GenLocated l Name -> Name
identNameRn = unLoc
#endif

-- | Convert a 'Name' to a local 'RdrName'. Retrie compares scope
-- binders by 'rdrFS', so an unqualified RdrName suffices.
nameToRdr :: Name -> RdrName
nameToRdr = mkVarUnqual . occNameFS . nameOccName

-- | Stable lookup key for a 'HsLocalBinds' (which has no span of its
-- own): the smallest span among its located bindings and signatures.
--
-- Only declaration spans participate; both the parser and the renamer
-- preserve them, so the key is invariant across passes. Annotation
-- spans must not: the parse tree carries the @where@ keyword's token
-- -- which precedes every declaration, and which
-- 'Retrie.Expr.inlineLocalBinds' strips when rewrite synthesis turns
-- a where clause into a template let -- and any comments attached
-- inside the block, which a 'RenamedSource' from a normal compile
-- does not share. Keying on either side of those would derive
-- different keys for the same block.
--
-- The correlation is positional: producer ('mkRenameInfo') and
-- consumer ('Retrie.Context', "Retrie.ContextCapture") must derive
-- keys from the same source text, and a key with no entry silently
-- falls back to parser-pass binder collection. Pattern binders do not
-- use this heuristic: they are keyed by the pattern node's exact span
-- (see 'riPatBinders'), which cannot alias.
scopeKey :: Data a => a -> Maybe RealSrcSpan
scopeKey = everything smaller query
  where
    smaller :: Maybe RealSrcSpan -> Maybe RealSrcSpan -> Maybe RealSrcSpan
    smaller (Just a) (Just b) = Just (min a b)
    smaller (Just a) Nothing  = Just a
    smaller Nothing  b        = b

    query :: Data b => b -> Maybe RealSrcSpan
    query =
      mkQ Nothing psBind `extQ` rnBind `extQ` psSig `extQ` rnSig

    psBind :: LHsBind GhcPs -> Maybe RealSrcSpan
    psBind = getRealSpan . getLocA

    rnBind :: LHsBind GhcRn -> Maybe RealSrcSpan
    rnBind = getRealSpan . getLocA

    psSig :: LSig GhcPs -> Maybe RealSrcSpan
    psSig = getRealSpan . getLocA

    rnSig :: LSig GhcRn -> Maybe RealSrcSpan
    rnSig = getRealSpan . getLocA
