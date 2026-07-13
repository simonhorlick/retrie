-- Copyright (c) 2025 Andrew Farmer
-- Copyright (c) 2020-2024 Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Retrie.Replace
  ( replace
  , Replacement(..)
  , Change(..)
  ) where

import Control.Monad.Trans.Class
import Control.Monad.Writer.Strict
import Data.Char (isSpace)
import Data.Generics

import Retrie.ExactPrint
import Retrie.Expr
import Retrie.FreeVars
import Retrie.GHC
import Retrie.Subst
import Retrie.Types
import Retrie.Universe

------------------------------------------------------------------------

-- | Specializes 'replaceImpl' to each of the AST types that retrie supports.
replace
  :: (Data a, MonadIO m) => Context -> a -> TransformT (WriterT Change m) a
replace c =
  mkM (replaceImpl @(HsExpr GhcPs) c)
    `extM` (replaceImpl @(Stmt GhcPs (LHsExpr GhcPs)) c)
    `extM` (replaceImpl @(HsType GhcPs) c)
    `extM` replacePat c

replacePat :: MonadIO m => Context -> LPat GhcPs -> TransformT (WriterT Change m) (LPat GhcPs)
-- We need to ensure we have a location available at the top level so we can
-- transfer annotations. This ensures we don't try to rewrite a naked Pat.
replacePat c p
  | Just lp <- dLPat p = cLPat <$> replaceImpl c lp
  | otherwise = return p

-- | Generic replacement function. This is the thing that actually runs the
-- 'Rewriter' carried by the context, instantiates templates, handles parens
-- and other whitespace bookkeeping, and emits resulting 'Replacement's.
replaceImpl
  :: forall ast m. (Data ast, ExactPrint ast, Matchable (LocatedA ast), MonadIO m)
  => Context -> LocatedA ast -> TransformT (WriterT Change m) (LocatedA ast)
replaceImpl c e = do
  let
    -- Prevent rewriting source of the rewrite itself by refusing to
    -- match under a binding of something that appears in the template.
    f result@RewriterResult{..} = result
      { rrTransformer =
          fmap (fmap (check rrOrigin rrQuantifiers)) <$> rrTransformer
      }
    check origin quantifiers match
      | getLocA e `overlaps` origin = NoMatch
      | MatchResult _ Template{..} <- match
      , fvs <- freeVars quantifiers (astA tTemplate)
      , any (`elemFVs` fvs) (ctxtBinders c) = NoMatch
      | otherwise = match

  -- We want to match through HsPar so we can make a decision
  -- about whether to keep the parens or not based on the
  -- resulting expression, but we need to know the entry location
  -- of the parens, not the inner expression, so we have to
  -- keep both expressions around.
  match <- runRewriter f c (ctxtRewriter c) (getUnparened e)

  case match of
    NoMatch -> return e
    MatchResult sub Template{..} -> do
      -- graft template into target module
      t' <- graftA tTemplate
      -- substitute for quantifiers in grafted template
      r <- normalizeHangingLets . normalizeHangingComprehensions
             <$> subst sub c t'
      -- copy appropriate annotations from old expression to template
      r0 <- addAllAnnsT e r
      -- add parens to template if needed
      res <- (mkM (parenify c) `extM` parenifyT c `extM` parenifyP c) r0

      -- prune the resulting expression and log it with location
      orig <- printNoLeadingSpaces <$> pruneA e

      -- Zero the entry delta before printing: the replacement text is
      -- spliced at the match site's start column, so its first line must
      -- start at column one. Printing the entry whitespace and stripping
      -- it afterwards (printNoLeadingSpaces) would shift the first line
      -- left while later lines keep their columns, skewing a multi-line
      -- replacement's internal layout by the amount stripped.
      repl <- printNoLeadingSpaces <$> pruneA (setEntryDP res (SameLine 0))
      -- repl <- printA' <$> pruneA r
      -- repl <- printA' <$> pruneA res
      -- repl <- return $ showAst t'

      -- lift $ liftIO $ debugPrint Loud "replaceImpl:orig="  [orig]
      -- lift $ liftIO $ debugPrint Loud "replaceImpl:repl="  [repl]

      -- lift $ liftIO $ debugPrint Loud "replaceImpl:e="  [showAst e]
      -- lift $ liftIO $ debugPrint Loud "replaceImpl:r="  [showAst r]
      -- lift $ liftIO $ debugPrint Loud "replaceImpl:r0="  [showAst r0]
      -- lift $ liftIO $ debugPrint Loud "replaceImpl:t'=" [showAst t']
      -- lift $ liftIO $ debugPrint Loud "replaceImpl:res=" [showAst res]

      let replacement = Replacement (getLocA e) orig repl
      TransformT $ lift $ tell $ Change [replacement] [tImports]
      -- make the actual replacement
      return res

-- | Re-lay every \"hanging\" let in the grafted expression: one whose
-- bindings sit left of the @let@ keyword, so their column deltas are
-- negative relative to it (@f x = let@ at the end of a line with the
-- bindings and a dedented @in@ back at the equation's indentation).
-- Those deltas underflow when the graft lands at a column left of the
-- original keyword, printing the bindings at column zero and breaking
-- the layout. The canonical form -- first binding beside the keyword,
-- @in@ directly below it -- is valid at any column, so rewrite to that
-- exactly when a negative column delta is present.
normalizeHangingLets :: Data a => a -> a
normalizeHangingLets = everywhere (mkT fixLet)
  where
    fixLet :: HsExpr GhcPs -> HsExpr GhcPs
#if __GLASGOW_HASKELL__ >= 912
    fixLet (HsLet (tkLet, tkIn) binds body) =
      HsLet (tkLet, fixIn tkIn) (fixBinds binds) body
    fixLet x = x

    fixIn (EpTok (EpaDelta ss (DifferentLine n c) cs))
      | c < 0 = EpTok (EpaDelta ss (DifferentLine n 0) cs)
    fixIn t = t

    fixBinds (HsValBinds (EpAnn (EpaDelta ss (DifferentLine _ c) acs) a cs) vb)
      | c < 0 = HsValBinds (EpAnn (EpaDelta ss (SameLine 1) acs) a cs) vb
    fixBinds b = b
#else
    fixLet (HsLet an tkLet binds tkIn body) =
      HsLet an tkLet (fixBinds binds) (fixIn tkIn) body
    fixLet x = x

    fixIn (L (TokenLoc (EpaDelta (DifferentLine n c) cs)) tok)
      | c < 0 = L (TokenLoc (EpaDelta (DifferentLine n 0) cs)) tok
    fixIn t = t

    fixBinds (HsValBinds (EpAnn (Anchor r (MovedAnchor (DifferentLine _ c))) a cs) vb)
      | c < 0 = HsValBinds (EpAnn (Anchor r (MovedAnchor (SameLine 1))) a cs) vb
    fixBinds b = b
#endif

-- | Re-anchor comprehension lines that hang left of the head.
--
-- Brackets suspend GHC layout, so a parsed comprehension may carry
-- continuation lines left of its own first token -- the layout anchor
-- exact-print resolves their 'DifferentLine' columns against:
--
-- > gen = [ mk n s
-- >     | n <- ns
-- >     , let s = "!" ]
--
-- Those lines' column deltas are negative. Grafted where the head sits
-- at a shallower column than the original, they underflow: the lines
-- land at column zero, or left of an enclosing layout context, and the
-- module no longer parses. Clamping each negative delta to the anchor
-- itself is valid at any graft column, since the anchor is the
-- comprehension's own first token, which always sits legally within
-- the surrounding layout.
normalizeHangingComprehensions :: Data a => a -> a
normalizeHangingComprehensions = everywhere (mkT fixComp)
  where
    fixComp :: HsExpr GhcPs -> HsExpr GhcPs
    fixComp e@(HsDo _ flav _)
      | isComprehension flav = everywhere (mkT clamp) e
    fixComp e = e

    isComprehension ListComp  = True
    isComprehension MonadComp = True
    isComprehension _         = False

    clamp :: DeltaPos -> DeltaPos
    clamp (DifferentLine l c) | c < 0 = DifferentLine l 0
    clamp d                           = d

-- | Records a replacement made. In cases where we cannot use ghc-exactprint
-- to print the resulting AST (e.g. CPP modules), we fall back on splicing
-- strings. Can also be used by external tools (search, linters, etc).
data Replacement = Replacement
  { replLocation :: SrcSpan
  , replOriginal :: String
  , replReplacement :: String
  } deriving Show

-- | Used as the writer type during matching to indicate whether any change
-- to the module should be made.
data Change = NoChange | Change [Replacement] [AnnotatedImports]

instance Semigroup Change where
  NoChange         <> other            = other
  other            <> NoChange         = other
  (Change rs1 is1) <> (Change rs2 is2) =
    Change (rs1 <> rs2) (is1 <> is2)

instance Monoid Change where
  mempty = NoChange

-- The location of 'e' accurately points to the first non-space character
-- of 'e', but when we exactprint 'e', we might get some leading spaces (if
-- annEntryDelta of the first token is non-zero). This means we can't just
-- splice in the printed expression at the desired location and call it a day.
-- Unfortunately, its hard to find the right annEntryDelta (it may not be the
-- top of the redex) and zero it out. As janky as it seems, its easier to just
-- drop leading spaces like this.
printNoLeadingSpaces :: (Data k, ExactPrint k) => Annotated k -> String
printNoLeadingSpaces = dropWhile isSpace . printA
