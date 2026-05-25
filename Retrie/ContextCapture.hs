-- Copyright (c) 2025 Andrew Farmer
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE ScopedTypeVariables #-}

-- | Capture of a rewrite template's free variables by binders enclosing
-- the match site.
--
-- Substituting a template under a binder that shares an occurrence
-- string with one of the template's free variables would rebind the
-- spliced variable to the wrong thing:
--
-- > y = 0
-- > e x = x + y     -- rewrite: e a -> a + y
-- >
-- > f y = e (y + 1) -- graft site: (y + 1) + y  -- both y's now f's!
--
-- This module detects such captures using the renamer-resolved 'Name's
-- a 'RenameInfo' provides (capture is same occurrence string,
-- /different/ 'Name'); "Retrie.Replace" refuses the match when one is
-- found, leaving the call site untouched rather than changing its
-- meaning. Soaking real codebases showed fewer than 0.5% of sites
-- capture; repairing them by alpha-renaming the enclosing binder is
-- implemented on the @capture-rename@ branches, but does not pay for
-- its machinery on the main line.
--
-- Without a 'RenameInfo' nothing is detected and behaviour is
-- unchanged.
module Retrie.ContextCapture
  ( detectContextCaptures
  ) where

import Data.Data (Data)
import Data.Generics (listify)
import Data.Maybe (isJust, mapMaybe)

import Retrie.GHC
import Retrie.RenameInfo
import Retrie.Substitution
import Retrie.Types

-- | Detect free variables of the template that a binder enclosing the
-- match site would capture. Returns the capturing binders; non-empty
-- means the caller should refuse the match, since grafting anyway
-- would change the meaning of the program.
detectContextCaptures
  :: Data t
  => Context
  -> Substitution -- ^ the match's substitution; its keys are the quantifiers
  -> t            -- ^ the instantiated template AST (parser pass)
  -> [Name]
detectContextCaptures c sub tmpl
    -- fast path: nothing enclosing the site is known by Name, so no
    -- capture can be detected (in particular: no RenameInfo supplied)
  | isNullUFM (ctxtScopeNames c) = []
  | otherwise = capturingBinders
  where
    ri = ctxtRenameInfo c
    nm = riNameMap ri

    -- Free variables of the template, by renamer-resolved Name: every
    -- HsVar that is spelled bare, is not a quantifier, resolves in the
    -- NameMap (the template retains its defining module's spans), and
    -- is not bound within the template itself. A qualified reference
    -- keeps its qualifier in the spliced text and local binders have
    -- no qualified form, so it can never be captured -- even when its
    -- occurrence string matches a binder at the site.
    freeNames =
      [ n
      | L _ (HsVar _ lv) <- listify isHsVar tmpl
      , let rdr = unLoc lv
      , Unqual{} <- [rdr]
      , not (isJust (lookupSubst (rdrFS rdr) sub))
      , Just n <- [lookupNameAt (getLocA lv) nm]
      , not (n `elementOfUniqSet` boundInTemplate)
      ]

    isHsVar :: LHsExpr GhcPs -> Bool
    isHsVar (L _ HsVar{}) = True
    isHsVar _             = False

    -- Names bound inside the template (lambda/let/where binders that
    -- travel with it). A context binder sharing their occurrence
    -- string cannot capture them: the spliced binding shadows it.
    --
    -- Local binds resolve through 'riScope'; pattern binders resolve
    -- per pattern node by exact span ('patBindersIn'), so every
    -- original pattern the template carries -- wherever rewrite
    -- synthesis grafted it, e.g. inside a tuple-dispatch case
    -- alternative -- contributes its binders, including ones the
    -- parser pass cannot see, like RecordWildCards expansions.
    -- Missing them would misclassify the template's references to
    -- them as free and refuse the match over an innocent context
    -- binder instead of letting capture-avoiding substitution rename
    -- the template's own binder.
    boundInTemplate = mkUniqSet $ concat
      [ concat $ mapMaybe (\k -> lookupScopeNames k ri)
          [ k
          | lbs <- listify (\(_ :: HsLocalBinds GhcPs) -> True) tmpl
          , Just k <- [scopeKey lbs]
          ]
      , patBindersIn tmpl ri
      ]

    -- The binders that would capture a free variable: same occurrence
    -- string in scope at the site, different Name.
    capturingBinders = uniqueNames
      [ b
      | n <- freeNames
      , Just b <- [lookupFsEnv (ctxtScopeNames c) (occNameFS (nameOccName n))]
      , b /= n
      ]

-- | Dedup by Name while keeping first-seen order.
uniqueNames :: [Name] -> [Name]
uniqueNames = go emptyUniqSet
  where
    go _ [] = []
    go seen (n:ns)
      | n `elementOfUniqSet` seen = go seen ns
      | otherwise = n : go (addOneToUniqSet seen n) ns
