module Datra.Interpreter.DatraTypeLawTests
  ( datraTypeLawTests
  ) where

import Datra.TestSupport
import DatraTypes
  ( AtlasMapFederationRefutation
      (AtlasMapFederationSpecificationHasNoMatchingMember)
  , FunctionFailure (NoApplicableFunctionAlternative)
  , InterpretedValue
  , InterpretingError (..)
  , datraCanonicalType
  , interpretedCanonicalResult
  , interpretedDatraType
  , interpretedTypeIsTotal
  , toStringValue
  )
import Interpreting (canonicalStringCodec)
import Rendering (renderInterpretedValue)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit
  ( Assertion
  , assertBool
  , assertEqual
  , assertFailure
  , testCase
  )

data ExpectedStringCapability
  = CanonicalString
  | NonCanonicalString

data DatraTypeExample = DatraTypeExample
  { exampleName :: String
  , exampleSource :: String
  , exampleStringCapability :: ExpectedStringCapability
  }

datraTypeLawTests :: TestTree
datraTypeLawTests =
  testGroup "Datra type laws"
    [ testGroup "standard-library declarations"
        (map datraTypeExampleTests standardLibraryTypeExamples)
    , testGroup "composite capability propagation"
        (map datraTypeExampleTests compositeTypeExamples)
    , extensionalEqualityTests
    , skipCoercionTests
    , neverLawsTests
    , totalBlockTests
    ]

-- Adding a standard-library type requires placing it in this table.  The
-- shared checks make specification and subfederation mandatory and force an
-- explicit decision about whether its string representation is canonical.
standardLibraryTypeExamples :: [DatraTypeExample]
standardLibraryTypeExamples =
  [ canonical "Any" "Any"
  , canonical "Never" "Never"
  , canonical "Nat" "Nat"
  , canonical "Int" "Int"
  , canonical "Str" "Str"
  , canonical "IdenStr" "IdenStr"
  , canonical "Bool" "Bool"
  , noncanonical "AST" "!~\"datra.AST\""
  , noncanonical "private Expr primitive" "!~\"datra.Expr\""
  , noncanonical "private Block primitive" "!~\"datra.Block\""
  , noncanonical "NatRange" "NatRange"
  , noncanonical "IntRange" "IntRange"
  , noncanonical "NatValRange" "NatValRange"
  , noncanonical "IntValRange" "IntValRange"
  , canonical "Template" "Template"
  , noncanonical "private SyntaxTemplate primitive" "!~\"datra.SyntaxTemplate\""
  ]

compositeTypeExamples :: [DatraTypeExample]
compositeTypeExamples =
  [ canonical "ordered canonical map" "(Nat; Int)"
  , canonical "positional skip sentinel" "*"
  , canonical "overlapping coalition sequence"
      "(from 2 to 5; from 4 to 8)"
  , canonical "canonical federation" "Nat | Str"
  , canonical "simple identifier" "value : Nat"
  , canonical "total begin/yield block" "begin yield 11"
  , canonical "function" "Nat -> Nat"
  , noncanonical "map containing a noncanonical type" "(Nat; (!~\"datra.AST\"))"
  , canonical "federation containing a function" "Nat | (Nat -> Nat)"
  ]

canonical :: String -> String -> DatraTypeExample
canonical name source = DatraTypeExample name source CanonicalString

noncanonical :: String -> String -> DatraTypeExample
noncanonical name source = DatraTypeExample name source NonCanonicalString

datraTypeExampleTests :: DatraTypeExample -> TestTree
datraTypeExampleTests example =
  testGroup (exampleName example)
    [ programCase "reflexive subfederation and self-specification"
        (unlines
          [ "assert (" <> source <> ") of (" <> source <> ")"
          , "assert ((" <> source <> ") ~> (" <> source
              <> ")) of (" <> source <> ")"
          ])
        "()"
    , testCase "string capability" $ do
        value <- requireExpression source
        assertStringCapability (exampleStringCapability example) value
    ]
  where
    source = exampleSource example

assertStringCapability
  :: ExpectedStringCapability
  -> InterpretedValue
  -> Assertion
assertStringCapability expected value =
  case expected of
    CanonicalString -> do
      assertBool "canonical value embeds CanonicalType"
        (case datraCanonicalType (interpretedDatraType value) of
          Just _ -> True
          Nothing -> False)
      case toStringValue canonicalStringCodec value of
        Left rejection ->
          assertFailure ("canonical toString failed: " <> show rejection)
        Right _ -> assertCanonicalRoundTrip value
    NonCanonicalString -> do
      assertBool "noncanonical value is still a DatraType"
        (case datraCanonicalType (interpretedDatraType value) of
          Nothing -> True
          Just _ -> False)
      case toStringValue canonicalStringCodec value of
        Left NonInjectiveStringInterpolation -> pure ()
        Left rejection ->
          assertFailure ("unexpected canonical toString failure: "
            <> show rejection)
        Right rendered ->
          assertFailure ("noncanonical value gained canonical toString: "
            <> renderInterpretedValue rendered)

assertCanonicalRoundTrip :: InterpretedValue -> Assertion
assertCanonicalRoundTrip original = do
  let rendered = renderInterpretedValue original
  roundTripped <- requireExpression rendered
  assertEqual
    ("canonical rendering changed meaning: " <> rendered)
    (interpretedCanonicalResult original)
    (interpretedCanonicalResult roundTripped)

extensionalEqualityTests :: TestTree
extensionalEqualityTests =
  testGroup "ordinary equality is mutual subfederation"
    [ testCase name (assertEqualityLaw left right expectedLeft expectedRight)
    | (name, left, right, expectedLeft, expectedRight) <-
        [ ("reordered federation", "0 | 1", "1 | 0", True, True)
        , ("proper numerical subtype", "from 0 to 3", "from 0 to 5", True, False)
        , ("disjoint primitive types", "Nat", "Str", False, False)
        , ("function signature", "Nat -> Nat", "Nat -> Nat", True, True)
        , ("block and yielded value", "begin yield 5", "5", True, True)
        ]
    ]


skipCoercionTests :: TestTree
skipCoercionTests =
  testGroup "skip numerical coercion"
    [ expressionCase "skip has numerical value one"
        "* + 0 = 1"
        "true"
    , expressionCase "coercion does not erase skip typing identity"
        "not (* of Nat) and not (1 of *)"
        "true"
    ]

neverLawsTests :: TestTree
neverLawsTests =
  testGroup "Never laws"
    [ expressionCase "Never is a subfederation of every type"
        "Never of (Nat; Str; (Nat -> Str))"
        "true"
    , expressionCase "ordinary types are not subfederations of Never"
        "not (Nat of Never)"
        "true"
    , expressionCase "Never is the identity of federation union"
        "(Nat | Never) = Nat"
        "true"
    , expressionFailureCase "ordinary values cannot specify to Never"
        "1 ~> Never"
        (SourceEvaluationFailure
          (FunctionEvaluationFailed NoApplicableFunctionAlternative))
    ]

assertEqualityLaw
  :: String
  -> String
  -> Bool
  -> Bool
  -> Assertion
assertEqualityLaw left right expectedLeft expectedRight = do
  leftInRight <- requireBoolean (parenthesize left <> " of " <> parenthesize right)
  rightInLeft <- requireBoolean (parenthesize right <> " of " <> parenthesize left)
  equal <- requireBoolean (parenthesize left <> " = " <> parenthesize right)
  assertEqual "left-to-right inclusion" expectedLeft leftInRight
  assertEqual "right-to-left inclusion" expectedRight rightInLeft
  assertEqual "equality agrees with mutual inclusion"
    (leftInRight && rightInLeft) equal

totalBlockTests :: TestTree
totalBlockTests =
  testGroup "total begin/yield blocks"
    [ testCase "totality follows the block, not the yielded federation" $ do
        value <- requireExpression "begin yield Nat"
        assertBool "begin/yield block is total" (interpretedTypeIsTotal value)
    , expressionCase "its yielded value is its only member"
        "(5 of (begin yield 5)) and not (6 of (begin yield 5))"
        "true"
    , expressionCase "equal source specifies it"
        "5 ~> (begin yield 5)"
        "5 <~ begin yield 5"
    , expressionFailureCase "unequal source cannot specify it"
        "6 ~> (begin yield 5)"
        (SourceEvaluationFailure
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationSpecificationHasNoMatchingMember))
    ]

requireExpression :: String -> IO InterpretedValue
requireExpression source =
  case runExpression source of
    Left failure -> assertFailure
      ("expression failed: " <> source <> ": " <> show failure)
    Right value -> pure value

requireBoolean :: String -> IO Bool
requireBoolean source = do
  value <- requireExpression source
  case renderInterpretedValue value of
    "true" -> pure True
    "false" -> pure False
    rendered -> assertFailure
      ("expected Boolean result from " <> source <> ", got " <> rendered)

parenthesize :: String -> String
parenthesize source = "(" <> source <> ")"
