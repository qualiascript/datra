module Datra.Interpreter.DatraTypeLawTests
  ( datraTypeLawTests
  ) where

import Datra.TestSupport
import DatraTypes
  ( AtlasMapFederationRefutation
      (AtlasMapFederationSpecificationHasNoMatchingMember)
  , InterpretedValue
  , InterpretingError (..)
  , StringRepresentation (..)
  , datraCanonicalType
  , datraStringRepresentation
  , interpretedCanonicalResult
  , interpretedDatraType
  , interpretedTypeIsTotal
  , toStringValue
  , weakToStringValue
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
  | WeakStringOnly

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
    , totalBlockTests
    ]

-- Adding a standard-library type requires placing it in this table.  The
-- shared checks make specification and subfederation mandatory and force an
-- explicit decision about whether its string representation is canonical.
standardLibraryTypeExamples :: [DatraTypeExample]
standardLibraryTypeExamples =
  [ canonical "Nat" "Nat"
  , canonical "Int" "Int"
  , canonical "String" "String"
  , canonical "Iden" "Iden"
  , canonical "Bool" "Bool"
  , weak "AST" "AST"
  , weak "Expr" "Expr"
  , weak "Block" "Block"
  , weak "Pages" "Pages"
  , weak "NatRange" "NatRange"
  , weak "IntRange" "IntRange"
  , weak "StringTemplate" "StringTemplate"
  ]

compositeTypeExamples :: [DatraTypeExample]
compositeTypeExamples =
  [ canonical "ordered canonical map" "(Nat; Int)"
  , canonical "overlapping coalition sequence"
      "(from 2 to 5; from 4 to 8)"
  , canonical "canonical federation" "Nat | String"
  , canonical "simple identifier" "value : Nat"
  , canonical "total begin/yield block" "begin yield 11"
  , weak "function" "Nat -> Nat"
  , weak "map containing a noncanonical type" "(Nat; AST)"
  , weak "federation containing a function" "Nat | (Nat -> Nat)"
  ]

canonical :: String -> String -> DatraTypeExample
canonical name source = DatraTypeExample name source CanonicalString

weak :: String -> String -> DatraTypeExample
weak name source = DatraTypeExample name source WeakStringOnly

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
      assertEqual "canonical string capability"
        CanonicalStringRepresentation
        (datraStringRepresentation (interpretedDatraType value))
      case toStringValue canonicalStringCodec value of
        Left rejection ->
          assertFailure ("canonical toString failed: " <> show rejection)
        Right _ -> assertCanonicalRoundTrip value
    WeakStringOnly -> do
      assertBool "weak-only value is still a DatraType"
        (case datraCanonicalType (interpretedDatraType value) of
          Nothing -> True
          Just _ -> False)
      assertEqual "weak string capability"
        WeakStringRepresentation
        (datraStringRepresentation (interpretedDatraType value))
      case toStringValue canonicalStringCodec value of
        Left NonInjectiveStringInterpolation -> pure ()
        Left rejection ->
          assertFailure ("unexpected canonical toString failure: "
            <> show rejection)
        Right rendered ->
          assertFailure ("weak-only value gained canonical toString: "
            <> renderInterpretedValue rendered)
      case weakToStringValue canonicalStringCodec value of
        Left rejection ->
          assertFailure ("weakToString failed: " <> show rejection)
        Right _ -> pure ()

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
  testGroup "equality is mutual subfederation"
    [ testCase name (assertEqualityLaw left right expectedLeft expectedRight)
    | (name, left, right, expectedLeft, expectedRight) <-
        [ ("reordered federation", "0 | 1", "1 | 0", True, True)
        , ("numerical coalition sequence and concatenation",
            "(Nat; Int)", "Nat, Int", True, True)
        , ("proper numerical subtype", "from 0 to 3", "from 0 to 5", True, False)
        , ("disjoint primitive types", "Nat", "String", False, False)
        , ("function signature", "Nat -> Nat", "Nat -> Nat", True, True)
        , ("block and yielded value", "begin yield 5", "5", True, True)
        ]
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
        "5 <~ begin\nyield 5"
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
