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
  , testCase "qualified-std runs a self-contained program" testQualifiedStandardLibrary
  , testCase "qualified-std does not expose bare names" testQualifiedStandardLibraryNames
  , testCase "qualified-std exposes Std" testQualifiedStandardLibraryModule
  , testCase "qualified-std round trips qualified syntax through AST" testQualifiedStandardLibraryAst
  , testCase "qualified-std interpret rejects bare names" testQualifiedStandardLibraryInterpretNames
  , testCase "qualified-std does not open syntax" testQualifiedStandardLibrarySyntax
  , testCase "qualified-std discovers qualified imports" testQualifiedStandardLibraryImports
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

testQualifiedStandardLibrary :: Assertion
testQualifiedStandardLibrary = do
  (status, output, errors) <- runDatra
    [ "build"
    , "--qualified-std"
    , "--source", "(7)"
    , "--ast-output", "-"
    , "--output", "-"
    ]
  assertEqual "exit status" ExitSuccess status
  assertEqual "canonical AST and interpreted value are emitted" "7\n7\n" output
  assertEqual "stderr" "" errors

testQualifiedStandardLibraryNames :: Assertion
testQualifiedStandardLibraryNames = do
  (status, _, errors) <- runDatra
    [ "build"
    , "--qualified-std"
    , "--source", "(Int)"
    , "--ast-output", "-"
    , "--output", "-"
    ]
  case status of
    ExitSuccess -> assertFailure "Int unexpectedly remained available without qualification"
    ExitFailure _ ->
      assertBool ("unexpected diagnostic: " <> errors)
        ("identifier is not imported in this scope" `isInfixOf` errors
          && "identifier: Int" `isInfixOf` errors)

testQualifiedStandardLibraryModule :: Assertion
testQualifiedStandardLibraryModule =
  withTemporaryPath "datra-cli-std.ast" $ \astPath -> do
    (status, output, errors) <- runDatra
      [ "build", "--qualified-std", "--source", "(Std.(Int))"
      , "--ast-output", astPath, "--output", "-"
      ]
    assertEqual "exit status" ExitSuccess status
    assertEqual "stderr" "" errors
    assertEqual "qualified module value" "Std.Int\n" output

testQualifiedStandardLibraryAst :: Assertion
testQualifiedStandardLibraryAst = do
  (parseStatus, ast, parseErrors) <- runDatra
    [ "ast", "--qualified-std"
    , "--source", "(Std.(if false then 1 else 11))"
    , "--output", "-"
    ]
  assertEqual "parse exit status" ExitSuccess parseStatus
  assertEqual "parse stderr" "" parseErrors
  (status, output, errors) <- runDatra
    [ "interpret", "--qualified-std", "--ast", ast, "--output", "-" ]
  assertEqual "interpret exit status" ExitSuccess status
  assertEqual "interpreted value" "11\n" output
  assertEqual "interpret stderr" "" errors

testQualifiedStandardLibraryInterpretNames :: Assertion
testQualifiedStandardLibraryInterpretNames = do
  (parseStatus, ast, _) <- runDatra
    [ "ast", "--source", "yield Int", "--output", "-" ]
  assertEqual "parse exit status" ExitSuccess parseStatus
  (status, _, errors) <- runDatra
    [ "interpret", "--qualified-std", "--ast", ast, "--output", "-" ]
  case status of
    ExitSuccess -> assertFailure "interpret unexpectedly opened Std"
    ExitFailure _ ->
      assertBool ("unexpected diagnostic: " <> errors)
        ("identifier: Int" `isInfixOf` errors)

testQualifiedStandardLibrarySyntax :: Assertion
testQualifiedStandardLibrarySyntax =
  withTemporaryPath "datra-cli-syntax.ast" $ \astPath -> do
    (status, _, errors) <- runDatra
      [ "build", "--qualified-std"
      , "--source", "(if Std.false then 1 else 11)"
      , "--ast-output", astPath, "--output", "-"
      ]
    case status of
      ExitSuccess -> assertFailure "unqualified if syntax unexpectedly remained available"
      ExitFailure _ ->
        assertBool ("unexpected diagnostic: " <> errors)
          ("identifier: if" `isInfixOf` errors)

testQualifiedStandardLibraryImports :: Assertion
testQualifiedStandardLibraryImports =
  withTemporaryPath "datra-cli-module.datra" $ \modulePath ->
  withTemporaryPath "datra-cli-import.ast" $ \astPath -> do
    writeFile modulePath "Std.(yield Answer := 42)\n"
    (status, output, errors) <- runDatra
      [ "build", "--qualified-std"
      , "--source", "(Std.(import " <> show modulePath
          <> " do yield Answer + 0))"
      , "--ast-output", astPath, "--output", "-"
      ]
    assertEqual ("exit status; stderr: " <> errors) ExitSuccess status
    assertEqual "imported value" "42\n" output
    assertEqual "stderr" "" errors

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
