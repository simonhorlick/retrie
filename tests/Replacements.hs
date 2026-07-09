{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The 'Replacement' texts a rewrite emits are spliced verbatim at
-- the replaced span, so a multi-line replacement must be internally
-- consistent: continuation lines indented relative to the first line,
-- which starts at column one. Printing the fragment's entry
-- whitespace and stripping it afterwards would shift the first line
-- left while later lines keep their columns, skewing the layout by
-- the amount stripped (an unfolded multi-line let body arrived two
-- columns too deep, a layout error at the splice point).
module Replacements (replacementsTest) where

import Control.Monad (forM)
import Data.Generics (everything, mkQ)
import Data.Monoid (First (..))
import Test.HUnit

import Retrie
import Retrie.CPP (CPP (NoCPP))
import Retrie.ExactPrint
import Retrie.Expr (mkLocatedHsVar)
import Retrie.Fixity (mkFixityEnv)
import Retrie.GHC
import Retrie.Monad (runRetrie)
import Retrie.Replace (Change (..), Replacement (..))
import Retrie.Rewrites.Function (matchToRewrites)
import Retrie.Types (Direction (LeftToRight))

replacementsTest :: LibDir -> Test
replacementsTest libdir =
  TestLabel "multi-line replacement text is internally aligned" $ TestCase $ do
    am <- parseContent libdir (mkFixityEnv []) "MultiLineSplice.hs" input
    let L _ m = astA am
    (fid, fms) <-
      case getFirst (everything (<>) (First Nothing `mkQ` matcher) m) of
        Nothing -> assertFailure "definition of mk not found"
        Just found -> pure found
    rewrites <- fmap astA $ transformA am $ \_ -> do
      fe <- mkLocatedHsVar fid
      concat <$> forM (unLoc (mg_alts fms)) (matchToRewrites fe mempty LeftToRight)
    (_, _, change) <-
      runRetrie (mkFixityEnv []) (apply (map toURewrite rewrites)) (NoCPP am)
    case change of
      NoChange -> assertFailure "expected the unfold to fire"
      Change reps _ ->
        case [replReplacement r | r <- reps, '\n' `elem` replReplacement r] of
          [repl] -> assertEqual "replacement keeps its internal layout" expected repl
          other -> assertFailure $
            "expected exactly one multi-line replacement, got: " ++ show other
  where
    matcher
      :: HsBind GhcPs
      -> First (LIdP GhcPs, MatchGroup GhcPs (LHsExpr GhcPs))
    matcher FunBind{fun_id, fun_matches}
      | occNameString (occName (unLoc fun_id)) == "mk" =
          First (Just (fun_id, fun_matches))
    matcher _ = First Nothing

    input = unlines
      [ "module MultiLineSplice where"
      , ""
      , "mk :: Int -> IO Int"
      , "mk x ="
      , "  let a = x + 1"
      , "      b = x + 2"
      , "  in pure (a + b)"
      , ""
      , "g :: IO Int"
      , "g ="
      , "  mk 4"
      ]

    -- The match site sits on its own line, so the replacement enters
    -- with a line break and an indent; printing that entry and then
    -- stripping it shifted the first line left while the continuation
    -- lines kept their columns, leaving them two deep.
    expected = init $ unlines
      [ "let a = 4 + 1"
      , "    b = 4 + 2"
      , "in pure (a + b)"
      ]
