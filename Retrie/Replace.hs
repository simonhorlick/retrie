-- Copyright (c) 2025 Andrew Farmer
-- Copyright (c) 2020-2024 Facebook, Inc. and its affiliates.
--
-- This source code is licensed under the MIT license found in the
-- LICENSE file in the root directory of this source tree.
--
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
import Data.List (intercalate)
import Data.Generics

import Retrie.ContextCapture
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
  match <- runRewriter f c{ctxtMatchSpan = Just (getLocA e)} (ctxtRewriter c) (getUnparened e)

  case match of
    NoMatch -> return e
    -- Free variables of the template must not be captured by binders
    -- enclosing the match site (same occurrence string resolving to a
    -- different Name). When they would be, refuse the match and leave
    -- the call site untouched.
    MatchResult sub Template{..} -> case detectContextCaptures c sub (astA tTemplate) of
     [] -> do
      -- graft template into target module
      t' <- graftA tTemplate
      -- substitute for quantifiers in grafted template
      r <- subst sub c t'
      -- add parens to template if needed
      resForPrint <- (mkM (parenify c) `extM` parenifyT c `extM` parenifyP c) r
      -- copy appropriate annotations from old expression to template
      res <- addAllAnnsT e resForPrint

      -- prune the resulting expression and log it with location
      orig <- printNoLeadingSpaces <$> pruneA e

      -- build the replacement text without the annotations as 'getLocA'
      -- doesn't include them in the range
      --
      -- The replacement is spliced textually at the column of 'e', but
      -- exactprint lays out the text for wherever the template sat in the
      -- rewrite definition: lines anchored to the expression follow its
      -- entry, delta-positioned lines print relative to the enclosing
      -- layout column. Mimic printing at the destination by setting the
      -- entry to the splice column's offset from the destination's layout
      -- column ('ctxtLayoutCol') and padding the layout-relative lines out
      -- to that column, which the standalone printer takes to be 1. (The
      -- leading newline and indent the entry introduces are stripped by
      -- 'printSpliceAt'.)
      let layoutCol = ctxtLayoutCol c
          spliceCol = maybe layoutCol srcSpanStartCol (getRealSpan (getLocA e))
      repl <- printSpliceAt layoutCol <$>
        pruneA (setEntryDP resForPrint
          (DifferentLine 1 (max 0 (spliceCol - layoutCol))))
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

      let replacement = Replacement
            { replLocation = getLocA e
            , replOriginal = orig
            , replReplacement = repl
            }
      TransformT $ lift $ tell $ Change [replacement] [tImports]
      -- make the actual replacement
      return res

     _capturing -> return e

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
  (Change rs1 is1) <> (Change rs2 is2) = Change (rs1 <> rs2) (is1 <> is2)

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

-- | Like 'printNoLeadingSpaces', but for text spliced into a layout group
-- at the given column. The standalone printer lays out delta-positioned
-- lines against layout column 1, so pad every line after the first by the
-- difference. Lines anchored to the expression itself already sit at their
-- destination columns, because the entry was set to the splice column's
-- offset from the same layout column before printing.
printSpliceAt :: (Data k, ExactPrint k) => Int -> Annotated k -> String
printSpliceAt layoutCol a = case lines (printNoLeadingSpaces a) of
  [] -> ""
  l1 : rest -> intercalate "\n" (l1 : map pad rest)
  where
    pad ln
      | all isSpace ln = ln -- keep blank lines blank
      | otherwise = replicate (layoutCol - 1) ' ' ++ ln
