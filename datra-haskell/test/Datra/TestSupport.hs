module Datra.TestSupport
  ( SourceFailure (..)
  , expressionCase
  , expressionFailureCase
  , programCase
  , programFailureCase
  , runExpression
  , runProgram
  ) where

import DatraLanguage.Diagnostics (Located (locatedValue))
import DatraLanguage.Diagnostics.Application (ParseFailure)
import DatraTypes (InterpretedValue, InterpretingError)
import Interpreting
  ( StandardLibraryVisibility (AllStandardLibrary)
  , emptyPreparedModules
  , interpretExpressionReason
  , interpretWithModules
  , parseDatraSourceLocatedWithModulesAndStandardLibraryVisibility
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
  = SourceParseFailure ParseFailure
  | SourceEvaluationFailure InterpretingError
  deriving (Eq, Show)

runExpression :: String -> Either SourceFailure InterpretedValue
runExpression source = do
  expression <- first SourceParseFailure
    (locatedValue <$> parseDatraSourceLocatedWithModulesAndStandardLibraryVisibility
      AllStandardLibrary emptyPreparedModules
      "test/Datra/TestSupport.hs" ("(" <> source <> "\n)"))
  first SourceEvaluationFailure (interpretExpressionReason expression)

runProgram :: String -> Either SourceFailure InterpretedValue
runProgram source = do
  expression <- first SourceParseFailure
    (locatedValue <$> parseDatraSourceLocatedWithModulesAndStandardLibraryVisibility
      AllStandardLibrary emptyPreparedModules
      "test/Datra/TestSupport.hs" source)
  first SourceEvaluationFailure
    (interpretWithModules emptyPreparedModules expression)

expressionCase :: TestName -> String -> String -> TestTree
expressionCase name source expected =
  testCase name (assertRendered expected (runExpression source))

programCase :: TestName -> String -> String -> TestTree
programCase name source expected =
  testCase name (assertRendered expected (runProgram source))

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
