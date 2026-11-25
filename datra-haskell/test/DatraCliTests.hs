module Main (main) where

import Control.Exception (bracket)
import Control.Monad (when)
import Data.List (isInfixOf)
import System.Directory
  ( doesFileExist
  , findExecutable
  , getPermissions
  , getTemporaryDirectory
  , removeFile
  , setOwnerReadable
  , setPermissions
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
  , testCase "invalid locale uses a structured diagnostic" testInvalidLocale
  , testCase "qualified-std runs a self-contained program" testQualifiedStandardLibrary
  , testCase "qualified-std does not expose bare names" testQualifiedStandardLibraryNames
  , testCase "qualified-std exposes Std" testQualifiedStandardLibraryModule
  , testCase "qualified-std round trips qualified syntax through AST" testQualifiedStandardLibraryAst
  , testCase "qualified-std interpret rejects bare names" testQualifiedStandardLibraryInterpretNames
  , testCase "qualified-std does not open syntax" testQualifiedStandardLibrarySyntax
  , testCase "no-std disables automatic Std" testNoStandardLibrary
  , testCase "module provides a qualified value" testQualifiedModuleValue
  , testCase "module private members stay hidden" testPrivateModuleMember
  , testCase "module namespace is independent of filename" testDeclaredModuleNamespace
  , testCase "multiple and repeated modules are deterministic" testMultipleModules
  , testCase "module-owned syntax remains qualified" testQualifiedModuleSyntax
  , testCase "with opens explicit modules" testWithModules
  , testCase "module private closure state is retained" testModuleClosure
  , testCase "module AST requires the same interpret input" testModuleAstRoundTrip
  , testCase "bundled modules are explicit inputs" testBundledModules
  , testCase "module inputs establish ordered dependencies" testOrderedModuleDependencies
  , testCase "integration fixtures receive modules from the CLI" testComposedModuleFixture
  , testCase "later overlapping module namespaces take precedence"
      testModuleNamespacePrecedence
  , testCase "missing modules identify the requested path" testMissingModule
  , testCase "unreadable modules fail during setup" testUnreadableModule
  , testCase "malformed modules fail during setup" testMalformedModule
  , testCase "lexical import syntax is absent" testLexicalImportRemoved
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
        ("identifier is not available in this scope" `isInfixOf` errors
          && "identifier: b" `isInfixOf` errors)

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
        ("identifier is not available in this scope" `isInfixOf` errors
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

testNoStandardLibrary :: Assertion
testNoStandardLibrary = do
  (status, _, errors) <- runDatra
    [ "build", "--no-std", "--source", "Std"
    , "--ast-output", "-", "--output", "-"
    ]
  case status of
    ExitSuccess -> assertFailure "Std unexpectedly remained available"
    ExitFailure _ -> assertBool ("unexpected diagnostic: " <> errors)
      ("identifier: Std" `isInfixOf` errors)

moduleFixture :: String -> FilePath
moduleFixture name = "test/fixtures/modules/" <> name <> ".datra"

testQualifiedModuleValue :: Assertion
testQualifiedModuleValue = do
  (status, output, errors) <- runDatra
    [ "build", "--qualified-std"
    , "--module", moduleFixture "library_one"
    , "--source", "(Std.(yield LibraryOne.x + 0))"
    , "--ast-output", "/dev/null", "--output", "-"
    ]
  assertEqual ("exit status; stderr: " <> errors) ExitSuccess status
  assertEqual "qualified value" "7\n" output
  assertEqual "stderr" "" errors

testPrivateModuleMember :: Assertion
testPrivateModuleMember = do
  (status, _, errors) <- runDatra
    [ "build", "--qualified-std"
    , "--module", moduleFixture "library_one"
    , "--source", "(Std.(yield LibraryOne._offset))"
    , "--ast-output", "/dev/null", "--output", "-"
    ]
  case status of
    ExitSuccess -> assertFailure "private module member unexpectedly escaped"
    ExitFailure _ -> assertBool ("unexpected diagnostic: " <> errors)
      ("identifier: _offset" `isInfixOf` errors)

testDeclaredModuleNamespace :: Assertion
testDeclaredModuleNamespace = do
  (status, output, errors) <- runDatra
    [ "build", "--qualified-std"
    , "--module", moduleFixture "different_filename"
    , "--source", "(Std.(yield DeclaredName.x + 0))"
    , "--ast-output", "/dev/null", "--output", "-"
    ]
  assertEqual ("exit status; stderr: " <> errors) ExitSuccess status
  assertEqual "declared namespace" "12\n" output

testMultipleModules :: Assertion
testMultipleModules = do
  (status, output, errors) <- runDatra
    [ "build", "--qualified-std"
    , "--module", moduleFixture "library_one"
    , "--module", moduleFixture "library_one"
    , "--module", moduleFixture "library_two"
    , "--source", "(Std.(yield LibraryOne.x + LibraryTwo.x))"
    , "--ast-output", "/dev/null", "--output", "-"
    ]
  assertEqual ("exit status; stderr: " <> errors) ExitSuccess status
  assertEqual "combined qualified values" "16\n" output

testQualifiedModuleSyntax :: Assertion
testQualifiedModuleSyntax = do
  (status, output, errors) <- runDatra
    [ "build", "--qualified-std"
    , "--module", moduleFixture "library_one"
    , "--source", "(LibraryOne.(shift 7))"
    , "--ast-output", "/dev/null", "--output", "-"
    ]
  assertEqual ("exit status; stderr: " <> errors) ExitSuccess status
  assertEqual "qualified syntax result" "11\n" output

testWithModules :: Assertion
testWithModules = do
  (status, output, errors) <- runDatra
    [ "build", "--qualified-std"
    , "--module", moduleFixture "multiple_exports"
    , "--source", "(Std.(with First; Second do yield x + shift second 3))"
    , "--ast-output", "/dev/null", "--output", "-"
    ]
  assertEqual ("exit status; stderr: " <> errors) ExitSuccess status
  assertEqual "opened module result" "10\n" output

testModuleClosure :: Assertion
testModuleClosure = do
  (status, output, errors) <- runDatra
    [ "build", "--qualified-std"
    , "--module", moduleFixture "library_one"
    , "--source", "(Std.(yield LibraryOne.increment 7))"
    , "--ast-output", "/dev/null", "--output", "-"
    ]
  assertEqual ("exit status; stderr: " <> errors) ExitSuccess status
  assertEqual "private helper result" "11\n" output

testModuleAstRoundTrip :: Assertion
testModuleAstRoundTrip = do
  (astStatus, ast, astErrors) <- runDatra
    [ "ast", "--qualified-std"
    , "--module", moduleFixture "library_one"
    , "--source", "(LibraryOne.(shift 7))"
    , "--output", "-"
    ]
  assertEqual ("AST exit status; stderr: " <> astErrors) ExitSuccess astStatus
  (status, output, errors) <- runDatra
    [ "interpret", "--qualified-std"
    , "--module", moduleFixture "library_one"
    , "--ast", ast, "--output", "-"
    ]
  assertEqual ("interpret exit status; stderr: " <> errors) ExitSuccess status
  assertEqual "interpreted module AST" "11\n" output

testBundledModules :: Assertion
testBundledModules = do
  (ordinalStatus, ordinalOutput, ordinalErrors) <- runDatra
    [ "build", "--qualified-std"
    , "--module", "ordinals"
    , "--source", "(Std.(yield Ordinals.sum(...; 2)))"
    , "--ast-output", "/dev/null", "--output", "-"
    ]
  assertEqual ("ordinal exit status; stderr: " <> ordinalErrors)
    ExitSuccess ordinalStatus
  assertEqual "bundled ordinal result" "... + 2\n" ordinalOutput
  (numberStatus, numberOutput, numberErrors) <- runDatra
    [ "build", "--qualified-std"
    , "--module", "numbers"
    , "--source", "(Std.(yield Numbers.max (1; 4; 2)))"
    , "--ast-output", "/dev/null", "--output", "-"
    ]
  assertEqual ("number exit status; stderr: " <> numberErrors)
    ExitSuccess numberStatus
  assertEqual "bundled number result" "4\n" numberOutput

testOrderedModuleDependencies :: Assertion
testOrderedModuleDependencies = do
  (status, output, errors) <- runDatra
    [ "build", "--qualified-std"
    , "--module", moduleFixture "library_one"
    , "--module", moduleFixture "nested"
    , "--source", "(Std.(yield Nested.x + 0))"
    , "--ast-output", "/dev/null", "--output", "-"
    ]
  assertEqual ("exit status; stderr: " <> errors) ExitSuccess status
  assertEqual "ordered dependency result" "8\n" output

testComposedModuleFixture :: Assertion
testComposedModuleFixture = do
  (status, output, errors) <- runDatra
    [ "build", "--qualified-std"
    , "--module", "ordinals"
    , "--input", "test/fixtures/integration/composed_features.datra"
    , "--ast-output", "/dev/null", "--output", "-"
    ]
  assertEqual ("exit status; stderr: " <> errors) ExitSuccess status
  assertEqual "composed integration result"
    "(true; true; true; true; true; true; true; true)\n" output

testModuleNamespacePrecedence :: Assertion
testModuleNamespacePrecedence = do
  (status, _, errors) <- runDatra
    [ "ast", "--qualified-std"
    , "--module", moduleFixture "overlap_one"
    , "--module", moduleFixture "overlap_two"
    , "--source", "Shared", "--output", "-"
    ]
  assertEqual ("exit status; stderr: " <> errors) ExitSuccess status

testMissingModule :: Assertion
testMissingModule = do
  (status, _, errors) <- runDatra
    [ "ast", "--module", "definitely-missing-module"
    , "--source", "1", "--output", "-"
    ]
  case status of
    ExitSuccess -> assertFailure "missing module unexpectedly succeeded"
    ExitFailure _ -> assertBool ("unexpected diagnostic: " <> errors)
      ("module: definitely-missing-module" `isInfixOf` errors)

testUnreadableModule :: Assertion
testUnreadableModule =
  withTemporaryPath "datra-cli-unreadable.datra" $ \modulePath -> do
    writeFile modulePath "yield Hidden : 1"
    permissions <- getPermissions modulePath
    setPermissions modulePath (setOwnerReadable False permissions)
    (status, _, errors) <- runDatra
      [ "ast", "--module", modulePath
      , "--source", "1", "--output", "-"
      ]
    case status of
      ExitSuccess -> assertFailure "unreadable module unexpectedly succeeded"
      ExitFailure _ -> assertBool ("unexpected diagnostic: " <> errors)
        ("module could not be read" `isInfixOf` errors)

testMalformedModule :: Assertion
testMalformedModule =
  withTemporaryPath "datra-cli-malformed.datra" $ \modulePath -> do
    writeFile modulePath "this is not a complete module ("
    (status, _, errors) <- runDatra
      [ "ast", "--module", modulePath
      , "--source", "1", "--output", "-"
      ]
    case status of
      ExitSuccess -> assertFailure "malformed module unexpectedly succeeded"
      ExitFailure _ -> assertBool ("unexpected diagnostic: " <> errors)
        ("module could not be parsed" `isInfixOf` errors)

testLexicalImportRemoved :: Assertion
testLexicalImportRemoved = do
  (status, _, errors) <- runDatra
    [ "build", "--qualified-std"
    , "--source", "(Std.(import \"ordinals\" do yield 1))"
    , "--ast-output", "/dev/null", "--output", "-"
    ]
  case status of
    ExitSuccess -> assertFailure "lexical import unexpectedly remained available"
    ExitFailure _ -> assertBool ("unexpected diagnostic: " <> errors)
      ("identifier: import" `isInfixOf` errors)

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
