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
