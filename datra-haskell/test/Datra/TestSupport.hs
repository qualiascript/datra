module Datra.TestSupport
  ( ModuleFailure (..)
  , SourceFailure (..)
  , expressionCase
  , expressionFailureCase
  , moduleCase
  , moduleFailureCase
  , programCase
  , programFileCase
  , programFailureCase
  , programCaseInMode
  , programFailureCaseInMode
  , runExpression
  , runModuleProgram
  , runProgram
  ) where

import DatraLanguage.Diagnostics (Located (locatedValue))
import DatraTypes (InterpretedValue, InterpretingError)
import Interpreting
  ( EvaluationMode
  , interpretExpressionReason
  , interpretWithImports
  , interpretWithImportsInMode
  )
import ModuleLoading (importSyntax, loadImports)
import Parsing
  ( parseDatra
  , parseDatraLocatedWithSyntaxImports
  )
import Rendering (renderInterpretedValue)
import Test.Tasty (TestName, TestTree)
import Test.Tasty.HUnit
  ( Assertion
  , assertEqual
  , assertFailure
  , testCase
  )

data SourceFailure
  = SourceParseFailure String
  | SourceEvaluationFailure InterpretingError
  deriving (Eq, Show)

data ModuleFailure
  = ModuleLoadingFailure String
  | ModuleParseFailure String
  | ModuleEvaluationFailure InterpretingError
  deriving (Eq, Show)

runExpression :: String -> Either SourceFailure InterpretedValue
runExpression source = do
  expression <- first SourceParseFailure (parseDatra ("(" <> source <> "\n)"))
  first SourceEvaluationFailure (interpretExpressionReason expression)

runProgram :: String -> Either SourceFailure InterpretedValue
runProgram source = do
  expression <- first SourceParseFailure (parseDatra source)
  first SourceEvaluationFailure (interpretExpressionReason expression)

runProgramInMode
  :: EvaluationMode
  -> String
  -> Either SourceFailure InterpretedValue
runProgramInMode mode source = do
  expression <- first SourceParseFailure (parseDatra source)
  first SourceEvaluationFailure
    (interpretWithImportsInMode mode [] expression)

runModuleProgram :: FilePath -> String -> IO (Either ModuleFailure InterpretedValue)
runModuleProgram origin source = do
  loaded <- loadImports origin source
  case loaded of
    Left failure -> pure (Left (ModuleLoadingFailure failure))
    Right imports ->
      case parseDatraLocatedWithSyntaxImports
          (importSyntax imports) origin source of
        Left failure -> pure (Left (ModuleParseFailure failure))
        Right located ->
          pure
            (first ModuleEvaluationFailure
              (interpretWithImports imports (locatedValue located)))

expressionCase :: TestName -> String -> String -> TestTree
expressionCase name source expected =
  testCase name (assertRendered expected (runExpression source))

programCase :: TestName -> String -> String -> TestTree
programCase name source expected =
  testCase name (assertRendered expected (runProgram source))

programFileCase
  :: Int
  -> TestName
  -> FilePath
  -> String
  -> TestTree
programFileCase expectedLineCount name path expected = testCase name $ do
  source <- readFile path
  assertEqual
    (name <> " line count")
    expectedLineCount
    (length (lines source))
  assertRendered expected (runProgram source)

programCaseInMode
  :: EvaluationMode
  -> TestName
  -> String
  -> String
  -> TestTree
programCaseInMode mode name source expected =
  testCase name (assertRendered expected (runProgramInMode mode source))

moduleCase :: FilePath -> TestName -> String -> String -> TestTree
moduleCase origin name source expected = testCase name $ do
  result <- runModuleProgram origin source
  assertRendered expected result

expressionFailureCase
  :: TestName
  -> String
  -> SourceFailure
  -> TestTree
expressionFailureCase name source expected =
  testCase name (assertFailureResult name expected (runExpression source))

programFailureCase
  :: TestName
  -> String
  -> SourceFailure
  -> TestTree
programFailureCase name source expected =
  testCase name (assertFailureResult name expected (runProgram source))

programFailureCaseInMode
  :: EvaluationMode
  -> TestName
  -> String
  -> SourceFailure
  -> TestTree
programFailureCaseInMode mode name source expected =
  testCase name
    (assertFailureResult name expected (runProgramInMode mode source))

moduleFailureCase
  :: FilePath
  -> TestName
  -> String
  -> (ModuleFailure -> Bool)
  -> TestTree
moduleFailureCase origin name source matches = testCase name $ do
  result <- runModuleProgram origin source
  case result of
    Left failure
      | matches failure -> pure ()
      | otherwise -> assertFailure
          (name <> ": unexpected failure: " <> show failure)
    Right value -> assertFailure
      (name <> ": unexpectedly produced " <> renderInterpretedValue value)

assertRendered
  :: Show failure
  => String
  -> Either failure InterpretedValue
  -> Assertion
assertRendered expected result =
  case result of
    Left failure -> assertFailure ("unexpected failure: " <> show failure)
    Right value -> assertEqual "rendered Datra value"
      expected (renderInterpretedValue value)

assertFailureResult
  :: (Eq failure, Show failure)
  => String
  -> failure
  -> Either failure InterpretedValue
  -> Assertion
assertFailureResult label expected result =
  case result of
    Left failure -> assertEqual label expected failure
    Right value -> assertFailure
      (label <> ": unexpectedly produced " <> renderInterpretedValue value)

first :: (left -> right) -> Either left value -> Either right value
first transform = either (Left . transform) Right
