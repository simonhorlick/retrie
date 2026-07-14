{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | End-to-end fixtures for the 'RenameInfo' pipeline: typecheck a
-- fixture module with the GHC API, build its 'RenameInfo' with
-- 'mkRenameInfo', and drive retrie's matcher with it. Everything here
-- turns on the 'RealSrcSpan' correlation between the renamed source
-- and retrie's own exact-print parse of the same text.
module RenameInfoTests (renameInfoTests) where

import Control.Monad (forM)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans (lift)
import Data.Data (Data)
import Data.IORef
import qualified Data.Map.Strict as Map
import Data.Generics (everything, listify, mkQ)
import Data.Monoid (First (..))
import System.Directory (canonicalizePath)
import System.FilePath ((</>))
import System.IO.Temp (withSystemTempDirectory)
import Test.HUnit

import qualified GHC
import GHC.Driver.Backend (noBackend)

import Retrie
import Retrie.AlphaEnv (emptyAlphaEnv)
import Retrie.Context (emptyContext, emptyContextWithRenameInfo)
import Retrie.CPP (CPP (NoCPP))
import Retrie.ExactPrint
import Retrie.Fixity (mkFixityEnv)
import Retrie.Monad (runRetrie)
import Retrie.RenameInfo (riNameMap)
import Retrie.Replace (Change (..), Replacement (..))
import Retrie.Rewrites.Function (matchToRewrites)
import Retrie.Types
  ( Direction (LeftToRight, RightToLeft)
  , mkLocalRewriterWithNames
  , mkRewriter
  , runMatcher
  )

renameInfoTests :: LibDir -> Test
renameInfoTests libdir = TestLabel "RenameInfo" $ TestList
  [ punLabelTest libdir
  , whereCaptureTest libdir
  , recCaptureTest libdir
  ]

-- | The renamer synthesizes a pun's right-hand side variable at the
-- field label's own span, so the 'NameMap' records the pun's
-- site-local value binder at the label position. Keying the label by
-- that Name filed the fold pattern under a Unique no other occurrence
-- can carry, and the pattern matched nowhere; labels must match by
-- occurrence string (see RFMap in "Retrie.PatternMap.Instances").
--
-- The match is driven through 'runMatcher' with an empty local scope
-- rather than a whole-module fold: a pun site necessarily has the
-- label's string in scope as a variable, and the (pre-existing)
-- shadowing rule diverts such labels independently of the NameMap.
punLabelTest :: LibDir -> Test
punLabelTest libdir =
  TestLabel "fold pattern with a record pun stays matchable under a RenameInfo" $
    TestCase $
      withFixture libdir $ \ri am -> do
        assertBool "NameMap resolves the pun label's span" $
          any ((== "px") . occNameString . nameOccName)
            (Map.elems (riNameMap ri))

        let L _ m = astA am
        (fid, fms) <- funBindOf "mkX" m
        (_, yms) <- funBindOf "mkY" m
        yBody <-
          case listify isRecordCon yms of
            [e] -> pure (e :: LHsExpr GhcPs)
            es -> assertFailure $
              "expected one record construction in mkY, got " ++ show (length es)

        matched <- newIORef (0 :: Int, 0 :: Int)
        _ <- transformA am $ \_ -> do
          fe <- mkLocatedHsVar fid
          rewrites <- map toURewrite . concat <$>
            forM (unLoc (mg_alts fms)) (matchToRewrites fe mempty RightToLeft)
          let
            withNames =
              foldMap (mkLocalRewriterWithNames (riNameMap ri) emptyAlphaEnv) rewrites
            withoutNames = foldMap mkRewriter rewrites
          named <- runMatcher
            (emptyContextWithRenameInfo (mkFixityEnv []) ri withNames mempty)
            withNames yBody
          bare <- runMatcher
            (emptyContext (mkFixityEnv []) withoutNames mempty)
            withoutNames yBody
          lift $ writeIORef matched (length named, length bare)
          return m

        (named, bare) <- readIORef matched
        assertBool "matches without a RenameInfo (legacy string path)" (bare > 0)
        assertBool "matches with the RenameInfo (pun label keyed by string)" (named > 0)
  where
    isRecordCon :: LHsExpr GhcPs -> Bool
    isRecordCon (L _ RecordCon{}) = True
    isRecordCon _ = False

-- | Unfolding a definition with a @where@ clause must not be refused
-- at a call site that binds one of the where-clause's names.
-- 'Retrie.Expr.inlineLocalBinds' turns the template's where clause
-- into a let, stripping the @where@ keyword token; 'scopeKey' must
-- still derive the same key the renamed source produced, or the
-- template's own binders are misclassified as free variables and
-- capture detection refuses the match over a binder the spliced let
-- would shadow anyway.
whereCaptureTest :: LibDir -> Test
whereCaptureTest libdir =
  TestLabel "unfolding a where-bodied definition under a same-named binder" $
    TestCase $
      withFixture libdir $ \ri am -> do
        let L _ m = astA am
        (fid, fms) <- funBindOf "compute" m
        rewrites <- fmap astA $ transformA am $ \_ -> do
          fe <- mkLocatedHsVar fid
          concat <$>
            forM (unLoc (mg_alts fms)) (matchToRewrites fe mempty LeftToRight)
        (_, _, change) <-
          runRetrie
            (mkFixityEnv [])
            (applyWithRenameInfo ri (map toURewrite rewrites))
            (NoCPP am)
        case change of
          NoChange -> assertFailure "expected the unfold to fire"
          -- the unfold firing at the site is also the no-refusal check:
          -- a capture refusal would have left the site untouched
          Change reps _ -> do
            assertEqual "unfolds the call under the go binder"
              ["compute n"] (map replOriginal reps)
            assertEqual "splices a let carrying the where binding"
              ["let go y = y + 1\n      in go n"] (map replReplacement reps)

-- | A @rec@ statement's binders must be visible to capture detection.
-- Unfolding @use@ splices its template's free variable @boost@; at
-- recSite a rec-bound @boost@ (a different Name) is in scope over the
-- statement tail, so the match must be refused, while the unshadowed
-- plainSite still unfolds. The rec binder reaches 'ctxtScopeNames'
-- through 'resolvedStmtBinders' recursing into the compound
-- statement's inner statements.
recCaptureTest :: LibDir -> Test
recCaptureTest libdir =
  TestLabel "rec-bound binders shadow name-keyed unfolds" $
    TestCase $
      withFixture libdir $ \ri am -> do
        let L _ m = astA am
        (fid, fms) <- funBindOf "use" m
        rewrites <- fmap astA $ transformA am $ \_ -> do
          fe <- mkLocatedHsVar fid
          concat <$>
            forM (unLoc (mg_alts fms)) (matchToRewrites fe mempty LeftToRight)
        (_, _, change) <-
          runRetrie
            (mkFixityEnv [])
            (applyWithRenameInfo ri (map toURewrite rewrites))
            (NoCPP am)
        case change of
          NoChange -> assertFailure "expected the plain site to unfold"
          Change reps _ -> do
            assertEqual "only the unshadowed site unfolds"
              ["use 7"] (map replOriginal reps)
            assertEqual "and it splices the top-level boost"
              ["boost 7"] (map replReplacement reps)

-- | The named function's binder and match group, from anywhere in the
-- given AST.
funBindOf
  :: Data a
  => String -> a -> IO (LIdP GhcPs, MatchGroup GhcPs (LHsExpr GhcPs))
funBindOf name m =
  case getFirst (everything (<>) (First Nothing `mkQ` matcher) m) of
    Nothing -> assertFailure $ "definition of " ++ name ++ " not found"
    Just found -> pure found
  where
    matcher
      :: HsBind GhcPs
      -> First (LIdP GhcPs, MatchGroup GhcPs (LHsExpr GhcPs))
    matcher FunBind{fun_id, fun_matches}
      | occNameString (occName (unLoc fun_id)) == name =
          First (Just (fun_id, fun_matches))
    matcher _ = First Nothing

-- | Shared fixture: write the module, typecheck it for its
-- 'RenameInfo', parse it with retrie, and hand both to the test. The
-- coverage assertion guards the span correlation: entries must speak
-- about the same filename retrie's parse uses, or the NameMap
-- resolves nothing and every test here degrades to the string path.
withFixture
  :: LibDir
  -> (RenameInfo -> AnnotatedModule -> Assertion)
  -> Assertion
withFixture libdir k =
  withSystemTempDirectory "retrie-renameinfo" $ \tmp0 -> do
    tmp <- canonicalizePath tmp0
    let path = tmp </> "Points.hs"
    writeFile path input
    ri <- mkRenameInfo <$> getRenamed libdir path
    assertBool "RenameInfo covers the fixture file" $
      any ((== mkFastString path) . srcSpanFile)
        (Map.keys (riNameMap ri))
    am <- parseContent libdir (mkFixityEnv []) path input
    k ri am
  where
    -- mkX and mkY construct the same punned record at different
    -- sites: the NameMap resolves mkX's pun label to mkX's parameter
    -- and mkY's to its where-binder, so a label keyed by Name at
    -- insertion cannot be found from the other site. compute's body
    -- lives in a where clause whose binder, go, is rebound by caller
    -- at the call site.
    input = unlines
      [ "{-# LANGUAGE NamedFieldPuns #-}"
      , "{-# LANGUAGE RecursiveDo #-}"
      , "module Points where"
      , ""
      , "data Point = Point { px :: Int, py :: Int }"
      , ""
      , "mkX :: Int -> Point"
      , "mkX px = Point { px, py = 0 }"
      , ""
      , "mkY :: Int -> Point"
      , "mkY q = Point { px, py = 0 }"
      , "  where px = q"
      , ""
      , "compute :: Int -> Int"
      , "compute x = go x"
      , "  where go y = y + 1"
      , ""
      , "caller :: (Int -> Int) -> Int -> Int"
      , "caller go n = compute n"
      , ""
      , "boost :: Int -> Int"
      , "boost v = v + 1"
      , ""
      , "use :: Int -> Int"
      , "use x = boost x"
      , ""
      , "plainSite :: Int"
      , "plainSite = use 7"
      , ""
      , "recSite :: IO Int"
      , "recSite = do"
      , "  rec boost <- pure (\\v -> v * (2 :: Int))"
      , "  pure (use 5)"
      ]

-- | Load and typecheck the fixture with the GHC API, returning its
-- 'RenamedSource'. No code is generated; the point is the renamer's
-- side of the span correlation 'mkRenameInfo' documents.
getRenamed :: LibDir -> FilePath -> IO GHC.RenamedSource
getRenamed libdir path =
  GHC.runGhc (Just libdir) $ do
    dflags <- GHC.getSessionDynFlags
    _ <- GHC.setSessionDynFlags dflags
      { GHC.backend = noBackend
      , GHC.ghcLink = GHC.NoLink
      }
    target <- GHC.guessTarget path Nothing Nothing
    GHC.setTargets [target]
    _ <- GHC.load GHC.LoadAllTargets
    graph <- GHC.getModuleGraph
    ms <- case [ s | s <- GHC.mgModSummaries graph
                   , GHC.moduleNameString (GHC.moduleName (GHC.ms_mod s)) == "Points"
                   ] of
      [s] -> return s
      _ -> liftIO $ assertFailure "fixture module not in module graph"
    tm <- GHC.typecheckModule =<< GHC.parseModule ms
    case GHC.tm_renamed_source tm of
      Just rn -> return rn
      Nothing -> liftIO $ assertFailure "typecheckModule kept no renamed source"
