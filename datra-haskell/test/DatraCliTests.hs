module Main (main) where

import Control.Exception (bracket)
import Control.Monad (when)
import Data.List (isInfixOf)
import System.Directory
  ( doesFileExist
  , findExecutable
  , getTemporaryDirectory
  , removeFile
  )
import System.Environment (getEnvironment)
import System.Exit (ExitCode (ExitFailure, ExitSuccess))
import System.IO (hClose, openTempFile)
import System.Process
  ( CreateProcess (env)
  , proc
  , readCreateProcessWithExitCode
  )
import Test.Tasty (defaultMain, testGroup)
import Test.Tasty.HUnit
  ( Assertion
  , assertBool
  , assertEqual
  , assertFailure
  , testCase
  )

main :: IO ()
main = defaultMain $ testGroup "Datra CLI"
  [ testCase "ast matches its golden file" testAstGolden
  , testCase "interpret consumes the golden AST" testInterpretGolden
  , testCase "build writes the same AST and interpreted value" testBuildGolden
  , testCase "build reports a forward-reference error" testBuildFailure
  , testCase "production mode omits soft assertions" testProductionAssertions
  , testCase "production mode keeps hard assertions" testHardProductionAssertion
  , testCase "invalid mode uses a structured diagnostic" testInvalidMode
  , testCase "invalid locale uses a structured diagnostic" testInvalidLocale
  , testCase "no-std runs a self-contained program" testNoStandardLibrary
  , testCase "no-std does not expose standard names" testNoStandardLibraryNames
  ]

fixtureBase :: FilePath
fixtureBase = "test/fixtures/cli/functions_and_types"

testAstGolden :: Assertion
testAstGolden = do
  expected <- readFile (fixtureBase <> ".ast")
  (_, output, errors) <- runDatra
    ["ast", "--input", fixtureBase <> ".datra", "--output", "-"]
  assertEqual "stderr" "" errors
  assertEqual "canonical AST" expected output

testInterpretGolden :: Assertion
testInterpretGolden = do
  expected <- readFile (fixtureBase <> ".out")
  (_, output, errors) <- runDatra
    ["interpret", "--input", fixtureBase <> ".ast", "--output", "-"]
  assertEqual "stderr" "" errors
  assertEqual "interpreted value" expected output

testBuildGolden :: Assertion
testBuildGolden = withTemporaryPath "datra-cli.ast" $ \astPath ->
  withTemporaryPath "datra-cli.out" $ \outputPath -> do
    expectedAst <- readFile (fixtureBase <> ".ast")
    expectedOutput <- readFile (fixtureBase <> ".out")
    (_, stdoutText, errors) <- runDatra
      [ "build"
      , "--input", fixtureBase <> ".datra"
      , "--ast-output", astPath
      , "--output", outputPath
      ]
    actualAst <- readFile astPath
    actualOutput <- readFile outputPath
    assertEqual "stdout" "" stdoutText
    assertEqual "stderr" "" errors
    assertEqual "written canonical AST" expectedAst actualAst
    assertEqual "written interpreted value" expectedOutput actualOutput

testBuildFailure :: Assertion
testBuildFailure = do
  (status, _, errors) <- runDatra
    [ "build"
    , "--source", "a := b\nb := 1\nyield a"
    , "--ast-output", "-"
    , "--output", "-"
    ]
  case status of
    ExitSuccess -> assertFailure "forward reference unexpectedly succeeded"
    ExitFailure _ ->
      assertBool ("unexpected diagnostic: " <> errors)
        ("identifier is not imported in this scope" `isInfixOf` errors
          && "identifier: b" `isInfixOf` errors)

testProductionAssertions :: Assertion
testProductionAssertions =
  withTemporaryPath "datra-cli-mode.ast" $ \astPath -> do
    (status, output, errors) <- runDatra
      [ "build"
      , "--source", "assert false"
      , "--mode", "prod"
      , "--ast-output", astPath
      , "--output", "-"
      ]
    assertEqual "exit status" ExitSuccess status
    assertEqual "implicit unit result" "()\n" output
    assertEqual "stderr" "" errors

testHardProductionAssertion :: Assertion
testHardProductionAssertion =
  withTemporaryPath "datra-cli-hard-mode.ast" $ \astPath -> do
    (status, _, errors) <- runDatra
      [ "build"
      , "--source", "assert hard false"
      , "--mode", "prod"
      , "--ast-output", astPath
      , "--output", "-"
      ]
    case status of
      ExitSuccess -> assertFailure "hard production assertion unexpectedly succeeded"
      ExitFailure _ ->
        assertBool ("unexpected diagnostic: " <> errors)
          ("assertion failed" `isInfixOf` errors)

testInvalidMode :: Assertion
testInvalidMode = do
  (status, _, errors) <- runDatra
    [ "build"
    , "--source", "yield 1"
    , "--mode", "fast"
    , "--ast-output", "-"
    , "--output", "-"
    ]
  case status of
    ExitSuccess -> assertFailure "invalid evaluation mode unexpectedly succeeded"
    ExitFailure _ ->
      assertBool ("unexpected diagnostic: " <> errors)
        ("evaluation mode is not supported" `isInfixOf` errors
          && "given mode: fast" `isInfixOf` errors)

testInvalidLocale :: Assertion
testInvalidLocale = do
  (status, _, errors) <- runDatra
    [ "build"
    , "--source", "yield 1"
    , "--locale", "klingon"
    , "--ast-output", "-"
    , "--output", "-"
    ]
  case status of
    ExitSuccess -> assertFailure "invalid diagnostic locale unexpectedly succeeded"
    ExitFailure _ ->
      assertBool ("unexpected diagnostic: " <> errors)
        ("diagnostic locale is not supported" `isInfixOf` errors
          && "given locale: klingon" `isInfixOf` errors)

testNoStandardLibrary :: Assertion
testNoStandardLibrary = do
  (status, output, errors) <- runDatra
    [ "build"
    , "--no-std"
    , "--source", "yield 7"
    , "--ast-output", "-"
    , "--output", "-"
    ]
  assertEqual "exit status" ExitSuccess status
  assertBool "canonical AST is still emitted" ("(program" `isInfixOf` output)
  assertBool "interpreted value is emitted" ("7\n" `isInfixOf` output)
  assertEqual "stderr" "" errors

testNoStandardLibraryNames :: Assertion
testNoStandardLibraryNames = do
  (status, _, errors) <- runDatra
    [ "build"
    , "--no-std"
    , "--source", "yield Int"
    , "--ast-output", "-"
    , "--output", "-"
    ]
  case status of
    ExitSuccess -> assertFailure "Int unexpectedly remained available without Std"
    ExitFailure _ ->
      assertBool ("unexpected diagnostic: " <> errors)
        ("identifier is not imported in this scope" `isInfixOf` errors
          && "identifier: Int" `isInfixOf` errors)

runDatra :: [String] -> IO (ExitCode, String, String)
runDatra arguments = do
  executable <- findExecutable "datra-haskell"
  case executable of
    Nothing -> assertFailure "Cabal did not expose the datra-haskell executable" >> undefined
    Just path -> withUnusedTemporaryPath "datra-executable.tix" $ \tixPath -> do
      environment <- getEnvironment
      let isolatedEnvironment =
            ("HPCTIXFILE", tixPath)
              : filter ((/= "HPCTIXFILE") . fst) environment
      readCreateProcessWithExitCode
        ((proc path arguments) {env = Just isolatedEnvironment}) ""

withTemporaryPath :: String -> (FilePath -> IO value) -> IO value
withTemporaryPath template = bracket create removeFile
  where
    create = do
      directory <- getTemporaryDirectory
      (path, handle) <- openTempFile directory template
      hClose handle
      pure path

withUnusedTemporaryPath :: String -> (FilePath -> IO value) -> IO value
withUnusedTemporaryPath template = bracket create cleanup
  where
    create = do
      directory <- getTemporaryDirectory
      (path, handle) <- openTempFile directory template
      hClose handle
      removeFile path
      pure path
    cleanup path = do
      exists <- doesFileExist path
      when exists (removeFile path)
