{-# LANGUAGE PostfixOperators #-}

module DatraInterpretingTests (main) where

import DatraLanguage.AST (Expression (..))
import DatraLanguage.AST.Syntax
  ( natural
  , (...)
  , (<:>)
  , (<+>)
  , (<..>)
  , (..+)
  , (..-)
  , (<.>)
  , (<@>)
  , (<~>)
  )
import DatraLanguage.AST.Syntax qualified as AST
import Interpreting
  ( InterpretedValue
  , InterpretedValueKind (..)
  , InterpretingError (..)
  , OperandSide (..)
  , interpretExpressionReason
  , interpretLocatedExpression
  , interpretedExplicitOrdinal
  , interpretedFormulationLevel
  , interpretedMap
  , interpretedMapCardinality
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  , interpretedRangeDescription
  , interpretedValueKind
  )
import DatraLanguage.Diagnostics.Interpreter
  ( AtlasMapFederationOperation (..)
  , AtlasMapFederationRefutation (..)
  , AtlasMapFederationUncertainty (..)
  )
import Rendering
  ( renderInterpretedValue
  , renderInterpretedValueAsNewlineMap
  )
import DatraOrdinal
  ( finiteOrdinal
  , naturalAtOrdinal
  , omega
  , ordinal
  )
import DatraLanguage.Diagnostics
  ( DatraError (DatraError)
  , Located (Located)
  , SourcePosition (SourcePosition)
  , SourceSpan (SourceSpan)
  )
import DatraLanguage.Diagnostics.Localization
  ( Locale (English, Romanian)
  , renderDatraError
  )
import MapOperators.AccessOperator
  ( AccessError
      ( AccessInsertionRankExceedsMap
      , AccessPositionOutOfBounds
      )
  )
import Numeric.Natural (Natural)
import Hedgehog qualified as H
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import SuperEllipsisRange
  ( SuperEllipsisRangeConcatError (SuperEllipsisRangesOverlap)
  , SuperEllipsisRangeDescription (SuperEllipsisRangeDescription)
  , SuperEllipsisRangeTarget (GivenTarget, MinusSign, PlusSign)
  )
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.Hedgehog (testProperty)
import Test.Tasty.HUnit (assertBool, testCase)

main :: IO ()
main = defaultMain testTree

testTree :: TestTree
testTree =
  testGroup "Datra interpreter"
    [ testGroup "examples"
        [ testCase "literals and arithmetic" testLiteralsAndArithmetic
        , testCase "ranges" testRanges
        , testCase "canonical results" testCanonicalResults
        , testCase "rendering" testRendering
        , testCase "maps" testMaps
        , testCase "atlas-map federations" testAtlasMapFederations
        , testCase "access" testAccess
        , testCase "specification" testSpecification
        , testCase "typed rejections" testTypedRejections
        , testCase "located rejection" testLocatedRejection
        ]
    , testGroup "properties"
        [ testProperty "natural addition agrees with Haskell" propNaturalAddition
        , testProperty "natural multiplication agrees with Haskell" propNaturalMultiplication
        , testProperty "natural exponentiation agrees with Haskell" propNaturalExponentiation
        ]
    ]

assert :: String -> Bool -> IO ()
assert = assertBool

propNaturalAddition :: H.Property
propNaturalAddition = H.property $ do
  left <- H.forAll naturalGen
  right <- H.forAll naturalGen
  interpretedNatural (Addition (EllipsisNatural left) (EllipsisNatural right))
    H.=== Just (left + right)

propNaturalMultiplication :: H.Property
propNaturalMultiplication = H.property $ do
  left <- H.forAll naturalGen
  right <- H.forAll naturalGen
  interpretedNatural
      (Multiplication (EllipsisNatural left) (EllipsisNatural right))
    H.=== Just (left * right)

propNaturalExponentiation :: H.Property
propNaturalExponentiation = H.property $ do
  base <- H.forAll (Gen.integral (Range.linear 0 12))
  exponentValue <- H.forAll (Gen.integral (Range.linear 0 8))
  interpretedNatural
      (Exponentiation (EllipsisNatural base) (EllipsisNatural exponentValue))
    H.=== Just (base ^ exponentValue)

naturalGen :: H.Gen Natural
naturalGen = Gen.integral (Range.linear 0 10000)

interpretedNatural :: Expression -> Maybe Natural
interpretedNatural expressionValue =
  case interpretExpressionReason expressionValue of
    Left _ -> Nothing
    Right value -> naturalOrdinal value

expectValue :: String -> Expression -> (InterpretedValue -> IO ()) -> IO ()
expectValue label expressionValue check =
  case interpretExpressionReason expressionValue of
    Left rejection ->
      fail (label <> ": unexpected rejection: " <> show rejection)
    Right value -> check value

naturalOrdinal :: InterpretedValue -> Maybe Natural
naturalOrdinal value = do
  (level, ordinalValue) <- interpretedExplicitOrdinal value
  if level == 1
    then naturalAtOrdinal ordinalValue
    else Nothing

testLiteralsAndArithmetic :: IO ()
testLiteralsAndArithmetic = do
  expectValue "ASCII string literal" (AsciiStringLiteral "a\255a") $ \value -> do
    let valueMap = interpretedMap value
        characterCodes =
          map
            (\position ->
              interpretedMapValueAt valueMap (finiteOrdinal position)
                >>= naturalOrdinal)
            [0 .. 3]
    assert "ASCII strings retain their map shape and character order"
      ( interpretedValueKind value == AsciiStringValueKind
        && interpretedMapCardinality valueMap == 2
        && interpretedMapFinalOrderType valueMap == finiteOrdinal 3
        && characterCodes == map Just [97, 255, 97] <> [Nothing]
        && renderInterpretedValue value == "\"a\\FFa\""
      )
  expectValue "empty ASCII string" (AsciiStringLiteral "") $ \value ->
    assert "the empty ASCII string retains its literal while using an empty map"
      ( interpretedValueKind value == AsciiStringValueKind
        && interpretedMapCardinality (interpretedMap value) == 0
        && renderInterpretedValue value == "\"\""
      )
  expectValue "natural literal" (natural 10) $ \value ->
    assert "naturals remain typed rank-one explicit values"
      ( interpretedValueKind value == NaturalValueKind
        && interpretedExplicitOrdinal value
          == Just (1, finiteOrdinal 10)
      )
  expectValue "Ellipsis literal" (...) $ \value ->
    assert "Ellipsis remains a formulation rather than an explicit ordinal"
      (interpretedFormulationLevel value == Just 1)
  expectValue
      "arithmetic precedence AST"
      ((AST.+)
        (natural 1)
        ((AST.*) (natural 2) (natural 3))) $ \value ->
    assert "natural arithmetic evaluates through ordinal operators"
      (interpretedExplicitOrdinal value == Just (1, finiteOrdinal 7))
  expectValue
      "Ellipsis soft coercion"
      ((AST.+) (...) (natural 0)) $ \value ->
    assert "adding zero coerces Ellipsis to an explicit rank-two omega"
      (interpretedExplicitOrdinal value == Just (2, omega))
  expectValue
      "formulation multiplication"
      ((AST.*) (...) (...)) $ \value ->
    assert "multiplying two Ellipsis formulations produces level two"
      (interpretedFormulationLevel value == Just 2)
  expectValue
      "zero formulation exponent"
      ((AST.^) (...) (natural 0)) $ \value ->
    assert "Ellipsis to zero evaluates to Dot"
      (interpretedFormulationLevel value == Just 0)
  expectValue
      "second formulation exponent"
      ((AST.^) (...) (natural 2)) $ \value ->
    assert "Ellipsis squared evaluates to a level-two formulation"
      (interpretedFormulationLevel value == Just 2)
  expectValue
      "ordinal multiplication order"
      ((AST.*)
        ((AST.+) (...) (natural 1))
        (natural 2)) $ \value ->
    assert "ordinal multiplication preserves noncommutative order"
      (interpretedExplicitOrdinal value
        == Just (2, ordinal [2, 1]))

testRanges :: IO ()
testRanges = do
  expectValue
      "inclusive natural range"
      (NaturalRange 2 5) $ \value ->
    assert "natural ranges retain their inclusive canonical form"
      ( interpretedRangeDescription value
          == Just
            (SuperEllipsisRangeDescription
              omega
              (finiteOrdinal 2)
              (GivenTarget (finiteOrdinal 6)))
        && renderInterpretedValue value == "from 2 to 5"
      )
  expectValue
      "descending inclusive natural range"
      (NaturalRange 5 0) $ \value ->
    assert "zero-target natural ranges use the descending open boundary"
      ( interpretedRangeDescription value
          == Just
            (SuperEllipsisRangeDescription
              omega
              (finiteOrdinal 5)
              MinusSign)
        && renderInterpretedValue value == "from 5 to 0"
      )
  expectValue
      "upwards natural range"
      (NaturalRangeUpwards 2) $ \value ->
    assert "upwards natural ranges retain their canonical keyword"
      ( interpretedRangeDescription value
          == Just
            (SuperEllipsisRangeDescription
              omega
              (finiteOrdinal 2)
              PlusSign)
        && renderInterpretedValue value == "from 2 upwards"
      )
  expectValue
      "inclusive valued natural range"
      (ValuedNaturalRange 2 5) $ \value ->
    assert "valued natural ranges retain within syntax"
      ( interpretedRangeDescription value
          == Just
            (SuperEllipsisRangeDescription
              omega
              (finiteOrdinal 2)
              (GivenTarget (finiteOrdinal 6)))
        && renderInterpretedValue value == "within 2 to 5"
      )
  expectValue
      "descending valued natural range"
      (ValuedNaturalRange 5 2) $ \value ->
    assert "descending valued ranges retain within syntax"
      (renderInterpretedValue value == "within 5 to 2")
  expectValue
      "upwards valued natural range"
      (ValuedNaturalRangeUpwards 2) $ \value ->
    assert "upwards valued ranges retain within syntax"
      (renderInterpretedValue value == "within 2 upwards")
  expectValue "NaturalType" NaturalType $ \value ->
    assert "Nat is canonically distinct from its expanded synonym"
      ( interpretedRangeDescription value
          == Just
            (SuperEllipsisRangeDescription
              omega
              (finiteOrdinal 0)
              PlusSign)
        && renderInterpretedValue value == "Nat"
      )
  expectValue
      "bounded range"
      ((<..>) (natural 2) (natural 5)) $ \value ->
    assert "bounded range retains its typed description"
      (interpretedRangeDescription value
        == Just
          (SuperEllipsisRangeDescription
            omega
            (finiteOrdinal 2)
            (GivenTarget (finiteOrdinal 5))))
  expectValue
      "open range"
      ((..+) (natural 2)) $ \value ->
    assert "postfix range retains its open target"
      (interpretedRangeDescription value
        == Just
          (SuperEllipsisRangeDescription
            omega
            (finiteOrdinal 2)
            PlusSign))
  expectValue
      "parenthesized Ellipsis range semantics"
      ((..+) (...)) $ \value ->
    assert "Ellipsis range endpoint is silently promoted to rank two"
      (interpretedRangeDescription value
        == Just
          (SuperEllipsisRangeDescription
            (ordinal [1, 0, 0])
            omega
            PlusSign))
  expectValue
      "descending range"
      ((..-) (natural 2)) $ \value ->
    assert "descending range syntax retains its target"
      (interpretedRangeDescription value
        == Just
          (SuperEllipsisRangeDescription
            omega
            (finiteOrdinal 2)
            MinusSign))

testCanonicalResults :: IO ()
testCanonicalResults = do
  expectValue
      "adjacent ascending ranges"
      ((<.>)
        ((<..>) (natural 2) (natural 5))
        ((..+) (natural 5))) $ \value ->
    assert "adjacent ascending ranges canonicalize to one open range"
      (renderInterpretedValue value == "2..")
  expectValue
      "adjacent descending ranges"
      ((<.>)
        ((<..>) (natural 9) (natural 5))
        ((<..>) (natural 5) (natural 2))) $ \value ->
    assert "adjacent descending ranges canonicalize in traversal order"
      (renderInterpretedValue value == "9..2")
  let levelTwoFormulation =
        (AST.^) (...) (natural 2)
  expectValue
      "adjacent cross-rank ranges"
      ((<.>)
        ((<..>) (natural 2) (natural 5))
        ((<..>) (natural 5) levelTwoFormulation)) $ \value ->
    assert "contiguous cross-rank ranges widen to the larger range"
      (renderInterpretedValue value == "2..(...^2)")
  expectValue
      "disjoint ranges"
      ((<.>)
        ((<..>) (natural 2) (natural 5))
        ((..+) (natural 8))) $ \value ->
    assert "disjoint ranges retain their ordered concatenation"
      (renderInterpretedValue value == "2..5, 8..")
  expectValue
      "empty then nonempty range"
      ((<.>)
        ((<..>) (natural 2) (natural 2))
        ((..+) (natural 5))) $ \value ->
    assert "empty ranges are canonical concatenation identities"
      (renderInterpretedValue value == "5..")
  expectValue
      "overlapping range value"
      ((<.>)
        ((..+) (natural 3))
        ((..+) (natural 4))) $ \value ->
    assert "overlapping ranges remain an ordered map result"
      (renderInterpretedValue value == "3.., 4..")

testRendering :: IO ()
testRendering = do
  expectValue
      "root map rendering modes"
      (AtlasMap [natural 1, natural 2]) $ \value ->
    assert "only newline mode removes the root map brackets"
      ( renderInterpretedValue value == "[1; 2]"
        && renderInterpretedValueAsNewlineMap value == "1\n2"
      )
  expectValue
      "newline map rendering disambiguates an open range"
      (AtlasMap [(..+) (natural 1), natural 10]) $ \value ->
    assert "an open range keeps a semicolon before the next line"
      (renderInterpretedValueAsNewlineMap value == "1..;\n10")
  expectValue
      "singleton arithmetic map"
      (AtlasMap [(AST.+) (natural 2) (natural 2)]) $ \value ->
    assert "singleton maps render as their sole canonical value"
      (renderInterpretedValue value == "4")
  expectValue "formulation Ellipsis" (...) $ \value ->
    assert "literal Ellipsis retains formulation syntax"
      (renderInterpretedValue value == "...")
  expectValue
      "explicit omega"
      ((AST.+) (...) (natural 0)) $ \value ->
    assert "explicit omega is distinguished from the formulation"
      (renderInterpretedValue value == "... + 0")
  expectValue
      "Dot formulation"
      ((AST.^) (...) (natural 0)) $ \value ->
    assert "Dot uses the agreed formulation syntax"
      (renderInterpretedValue value == "...^0")
  expectValue
      "second super-ellipsis formulation"
      ((AST.^) (...) (natural 2)) $ \value ->
    assert "higher formulations render by kind"
      (renderInterpretedValue value == "...^2")
  expectValue
      "zero multiplication"
      ((AST.+)
        ((AST.*) (...) (natural 0))
        (natural 2)) $ \value ->
    assert "arithmetic results return to their minimal rank"
      (renderInterpretedValue value == "2")
  expectValue
      "map containing a canonical range"
      (AtlasMap
        [ (<.>)
            ((<..>) (natural 2) (natural 5))
            ((..+) (natural 5))
        ]) $ \value ->
    assert "singleton range maps render without enumeration or brackets"
      (renderInterpretedValue value == "2..")

testMaps :: IO ()
testMaps = do
  expectValue
      "ASCII-string concatenation"
      ((<.>) (AsciiStringLiteral "ab") (AsciiStringLiteral "_1")) $ \value ->
    assert "ordinary concatenation remembers its ASCII-string result"
      ( interpretedValueKind value == AsciiStringValueKind
        && interpretedMapCardinality (interpretedMap value) == 2
        && interpretedMapFinalOrderType (interpretedMap value)
          == finiteOrdinal 4
        && renderInterpretedValue value == "$ab_1"
      )
  expectValue
      "empty ASCII-string concatenation"
      ((<.>) (AsciiStringLiteral "") (AsciiStringLiteral "")) $ \value ->
    assert "concatenating empty strings remains an empty ASCII string"
      ( interpretedValueKind value == AsciiStringValueKind
        && interpretedMapCardinality (interpretedMap value) == 0
        && renderInterpretedValue value == "\"\""
      )
  expectValue
      "operator sequence"
      (natural 1 <:> natural 2) $ \value ->
    assert "sequential AST syntax constructs a two-position map"
      ( interpretedMapCardinality (interpretedMap value) == 2
        && interpretedMapFinalOrderType (interpretedMap value)
          == finiteOrdinal 2
      )
  let compoundSequence =
        MapSequence
          [ (<..>) (natural 1) (natural 4)
          , AsciiStringLiteral "ab"
          ]
  expectValue "sequence preserves compound operands" compoundSequence $ \value ->
    assert "each sequence operand occupies exactly one final-page position"
      ( interpretedMapFinalOrderType (interpretedMap value)
          == finiteOrdinal 2
        && renderInterpretedValue value == "[1..4; $ab]"
      )
  expectValue
      "sequence access returns a compound operand intact"
      ((<@>) compoundSequence (natural 0)) $ \value ->
    assert "access does not flatten the selected sequence operand"
      (renderInterpretedValue value == "1..4")
  expectValue
      "concatenation flattens compound operands"
      ((<.>)
        ((<..>) (natural 1) (natural 4))
        (AsciiStringLiteral "ab")) $ \value ->
    assert "concatenation appends operand final-page contents"
      (interpretedMapFinalOrderType (interpretedMap value)
        == finiteOrdinal 5)
  expectValue
      "operator expansion"
      ((natural 1 <:> natural 2) <+> (natural 3 <:> natural 4)) $ \value ->
    assert "expansion AST syntax introduces one additional map level"
      (interpretedMapCardinality (interpretedMap value) == 3)
  let nested =
        AtlasMap
          [ AtlasMap [natural 1, natural 2]
          , AtlasMap [natural 3, natural 4]
          ]
  expectValue "nested map" nested $ \value -> do
    let valueMap = interpretedMap value
        values =
          map
            (\position ->
              renderInterpretedValue
                <$> interpretedMapValueAt valueMap (finiteOrdinal position))
            [0 .. 2]
    assert "nested map has the requested three-page cardinality"
      (interpretedMapCardinality valueMap == 3)
    assert "nested sequence operands remain distinct final-page values"
      (values == [Just "[1; 2]", Just "[3; 4]", Nothing])
    assert "nested maps retain their sequence boundaries when rendered"
      (renderInterpretedValue value == "[[[1; 2]; [3; 4]]]")
  expectValue
      "map concatenation"
      ((<.>)
        (AtlasMap [natural 1, natural 2])
        (AtlasMap [natural 3])) $ \value ->
    assert "map concatenation appends final-page order types"
      (interpretedMapFinalOrderType (interpretedMap value)
        == finiteOrdinal 3)

testAtlasMapFederations :: IO ()
testAtlasMapFederations = do
  expectValue
      "a structured map retains NaturalRange syntax"
      (AtlasMap [natural 2, NaturalRange 2 10]) $ \value ->
    assert "NaturalRange structure survives a sequential product"
      (renderInterpretedValue value == "[2; from 2 to 10]")
  expectValue
      "disjoint NaturalRange concatenation"
      ((<.>) (NaturalRange 2 5) (NaturalRange 6 9)) $ \value ->
    assert "disjoint finite NaturalRanges form a federation"
      (renderInterpretedValue value
        == "from 2 to 5, from 6 to 9")
  expectValue
      "descending disjoint NaturalRange concatenation"
      ((<.>) (NaturalRange 9 6) (NaturalRange 5 2)) $ \value ->
    assert "NaturalRange disjointness ignores traversal direction"
      (renderInterpretedValue value
        == "from 9 to 6, from 5 to 2")
  expectValue
      "finite then disjoint upwards NaturalRange"
      ((<.>) (NaturalRange 2 5) (NaturalRangeUpwards 6)) $ \value ->
    assert "a finite domain below an upwards domain is disjoint"
      (renderInterpretedValue value
        == "from 2 to 5, from 6 upwards")
  assert "overlapping finite NaturalRanges have a collision witness"
    (case interpretExpressionReason
        ((<.>) (NaturalRange 2 5) (NaturalRange 3 6)) of
      Left
          (AtlasMapFederationOperationRefuted
            (AtlasMapFederationConcatenationCollision 3)) -> True
      _ -> False)
  assert "a shared NaturalRange endpoint is overlap"
    (case interpretExpressionReason
        ((<.>) (NaturalRange 2 5) (NaturalRangeUpwards 5)) of
      Left
          (AtlasMapFederationOperationRefuted
            (AtlasMapFederationConcatenationCollision 5)) -> True
      _ -> False)
  assert "two upwards NaturalRanges always overlap"
    (case interpretExpressionReason
        ((<.>)
          (NaturalRangeUpwards 2)
          (NaturalRangeUpwards 20)) of
      Left
          (AtlasMapFederationOperationRefuted
            (AtlasMapFederationConcatenationCollision 20)) -> True
      _ -> False)
  expectValue
      "disjoint ValuedNaturalRange concatenation"
      ((<.>) (ValuedNaturalRange 2 5) (ValuedNaturalRange 6 9)) $ \value ->
    assert "disjoint valued ranges form a federation"
      (renderInterpretedValue value
        == "within 2 to 5, within 6 to 9")
  assert "overlapping ValuedNaturalRanges have a collision witness"
    (case interpretExpressionReason
        ((<.>) (ValuedNaturalRange 2 5) (ValuedNaturalRange 4 8)) of
      Left
          (AtlasMapFederationOperationRefuted
            (AtlasMapFederationConcatenationCollision 4)) -> True
      _ -> False)
  assert "NaturalRange and ValuedNaturalRange singleton Atlases can collide"
    (case interpretExpressionReason
        ((<.>) (NaturalRange 2 5) (ValuedNaturalRange 5 8)) of
      Left
          (AtlasMapFederationOperationRefuted
            (AtlasMapFederationConcatenationCollision 5)) -> True
      _ -> False)
  assert "unknown structured concatenation is undecidable, not refuted"
    (case interpretExpressionReason
        ((<.>)
          (NaturalRange 2 4 <:> NaturalRange 8 10)
          (NaturalRange 20 22 <:> NaturalRange 30 32)) of
      Left
          (AtlasMapFederationOperationUndecidable
            (NoAtlasMapFederationDecisionProcedure
              AtlasMapFederationConcatenation)) -> True
      _ -> False)

testAccess :: IO ()
testAccess = do
  let threeValues =
        (<.>)
          (natural 1)
          ((<.>) (natural 2) (natural 3))
      sequenceSpecification =
        (<~>)
          (AtlasMap [natural 2, natural 3])
          (AtlasMap [NaturalType, NaturalType])
      expectRangeAccess label expectedKind sourceValue selectionValue expected =
        expectValue label ((<@>) sourceValue selectionValue) $ \value ->
          assert label
            ( interpretedValueKind value == expectedKind
              && renderInterpretedValue value == expected
            )
  expectValue
      "access projects one specification fiber"
      ((<@>) sequenceSpecification (natural 0)) $ \value ->
    assert "the selected source and target remain related"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value == "2 ~> Nat"
      )
  expectValue
      "range access projects specification fibers"
      ((<@>)
        sequenceSpecification
        ((<..>) (natural 0) (natural 2))) $ \value ->
    assert "a specification range retains both selected fibers"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value == "[2; 3] ~> [Nat; Nat]"
      )
  expectValue
      "natural upwards range access"
      ((<@>) threeValues (NaturalRangeUpwards 1)) $ \value ->
    assert "natural range access clips upwards to the largest fitting range"
      (renderInterpretedValue value == "[2; 3]")
  expectValue
      "bounded natural range access"
      ((<@>) threeValues (NaturalRange 1 10)) $ \value ->
    assert "bounded natural range access clips its inclusive target"
      (renderInterpretedValue value == "[2; 3]")
  expectValue
      "descending natural range access"
      ((<@>) threeValues (NaturalRange 10 0)) $ \value ->
    assert "descending natural range access clips its inclusive origin"
      (renderInterpretedValue value == "[3; 2; 1]")
  expectValue
      "empty natural range access"
      ((<@>) threeValues (NaturalRangeUpwards 10)) $ \value ->
    assert "natural range access always has its empty federation member"
      (renderInterpretedValue value == "[]")
  let stableConcatenationPrefix =
        (<.>)
          (natural 1)
          ((<.>)
            (natural 2)
            ((<.>) (natural 3) (NaturalRange 5 20)))
  expectValue
      "access stays within a total concatenation prefix"
      ((<@>)
        stableConcatenationPrefix
        ((<..>) (natural 0) (natural 3))) $ \value ->
    assert "an uncertain suffix does not obscure a known prefix"
      (renderInterpretedValue value == "[1; 2; 3]")
  expectValue
      "NaturalRange access stays within a total concatenation prefix"
      ((<@>) stableConcatenationPrefix (NaturalRange 0 2)) $ \value ->
    assert "federated selections use the same accessible regions"
      (renderInterpretedValue value == "[1; 2; 3]")
  expectValue
      "atomic coalition access lifts through concatenation"
      ((<@>)
        ((<.>) (ValuedNaturalRange 1 3) (NaturalRange 5 20))
        (natural 0)) $ \value ->
    assert "a fixed-width coalition remains one accessible region"
      (renderInterpretedValue value == "within 1 to 3")
  assert "access crossing an uncertain concatenation suffix is undecidable"
    (case interpretExpressionReason
        ((<@>)
          stableConcatenationPrefix
          ((<..>) (natural 0) (natural 4))) of
      Left
          (AtlasMapFederationOperationUndecidable
            (NoAtlasMapFederationDecisionProcedure
              AtlasMapFederationAccess)) -> True
      _ -> False)
  let valuedCoalitionSequence =
        AtlasMap
          [ natural 2
          , natural 3
          , ValuedNaturalRange 1 20
          , natural 5
          ]
  expectValue
      "a sequence containing a valued-range coalition supports open access"
      ((<@>) valuedCoalitionSequence (NaturalRangeUpwards 0)) $ \value ->
    assert "open access preserves the valued-range coalition as one position"
      ( interpretedMapFinalOrderType (interpretedMap value) == finiteOrdinal 4
        && renderInterpretedValue value == "[2; 3; within 1 to 20; 5]"
      )
  expectValue
      "bounded access slices a sequence of coalitions"
      ((<@>) valuedCoalitionSequence (NaturalRange 1 2)) $ \value ->
    assert "bounded access retains the selected valued-range coalition"
      (renderInterpretedValue value == "[3; within 1 to 20]")
  expectValue
      "singleton access selects a valued-range coalition"
      ((<@>) valuedCoalitionSequence (natural 2)) $ \value ->
    assert "singleton access returns the selected coalition"
      (renderInterpretedValue value == "within 1 to 20")
  expectValue
      "a valued range is its own coalition"
      ((<@>) (ValuedNaturalRange 1 20) (NaturalRangeUpwards 0)) $ \value ->
    assert "access preserves a standalone valued-range coalition"
      (renderInterpretedValue value == "within 1 to 20")
  expectRangeAccess
    "natural upwards access canonicalizes a bounded source range"
    RangeValueKind
    ((<..>) (natural 100) (natural 123))
    (NaturalRangeUpwards 5)
    "105..123"
  expectRangeAccess
    "bounded natural access canonicalizes a source range"
    RangeValueKind
    ((<..>) (natural 100) (natural 123))
    (NaturalRange 5 10)
    "105..111"
  expectRangeAccess
    "descending natural access canonicalizes a source range"
    RangeValueKind
    ((<..>) (natural 100) (natural 123))
    (NaturalRange 10 5)
    "110..104"
  expectRangeAccess
    "natural upwards access preserves source range gaps"
    RangeConcatenationValueKind
    ((<.>)
      ((<..>) (natural 2) (natural 5))
      ((<..>) (natural 10) (natural 14)))
    (NaturalRangeUpwards 1)
    "3..5, 10..14"
  expectRangeAccess
    "natural upwards access canonicalizes an open source range"
    RangeValueKind
    ((..+) (natural 10))
    (NaturalRangeUpwards 5)
    "15.."
  expectRangeAccess
    "open range access stays an open range"
    RangeValueKind
    ((..+) (natural 10))
    ((..+) (natural 5))
    "15.."
  expectRangeAccess
    "bounded range access canonicalizes selected runs"
    RangeConcatenationValueKind
    ((<..>) (natural 2) (natural 20))
    ((<.>)
      ((<..>) (natural 3) (natural 8))
      ((<..>) (natural 11) (natural 13)))
    "5..10, 13..15"
  expectRangeAccess
    "an open selector crosses a finite source prefix"
    RangeValueKind
    ((<.>)
      ((<..>) (natural 2) (natural 4))
      ((..+) (natural 10)))
    ((..+) (natural 2))
    "10.."
  expectRangeAccess
    "source and selector concatenations stay range concatenations"
    RangeConcatenationValueKind
    ((<.>)
      ((<..>) (natural 2) (natural 4))
      ((..+) (natural 10)))
    ((<.>)
      ((<..>) (natural 2) (natural 5))
      ((..+) (natural 8)))
    "10..13, 16.."
  expectRangeAccess
    "ascending source with descending selection"
    RangeValueKind
    ((<..>) (natural 2) (natural 20))
    ((<..>) (natural 8) (natural 3))
    "10..5"
  expectRangeAccess
    "descending source with ascending selections"
    RangeConcatenationValueKind
    ((<..>) (natural 20) (natural 2))
    ((<.>)
      ((<..>) (natural 3) (natural 8))
      ((<..>) (natural 11) (natural 13)))
    "17..12, 9..7"
  expectRangeAccess
    "descending source and selection compose to ascending"
    RangeValueKind
    ((<..>) (natural 20) (natural 2))
    ((<..>) (natural 8) (natural 3))
    "12..17"
  expectRangeAccess
    "descending selection reverses source-component order"
    RangeConcatenationValueKind
    ((<.>)
      ((<..>) (natural 2) (natural 5))
      ((<..>) (natural 10) (natural 14)))
    ((<..>) (natural 6) (natural 1))
    "13..9, 4..3"
  expectRangeAccess
    "a descending result ending at zero uses the minus form"
    RangeValueKind
    ((<..>) (natural 0) (natural 10))
    ((..-) (natural 5))
    "5..-"
  expectRangeAccess
    "a selection crossing source ranges splits at the value gap"
    RangeConcatenationValueKind
    ((<.>)
      ((<..>) (natural 2) (natural 5))
      ((<..>) (natural 10) (natural 14)))
    ((<..>) (natural 1) (natural 6))
    "3..5, 10..13"
  expectRangeAccess
    "empty range-on-range access stays empty"
    MapValueKind
    ((<..>) (natural 2) (natural 20))
    ((<..>) (natural 5) (natural 5))
    "[]"
  expectRangeAccess
    "bounded transfinite range access remains symbolic"
    RangeValueKind
    ((<..>) (natural 2) (...))
    ((<..>) (natural 3) (...))
    "5..(...)"
  expectRangeAccess
    "open transfinite range access computes its limit boundary"
    RangeValueKind
    ((..+) ((AST.+) (...) (natural 2)))
    ((..+) (natural 3))
    "(... + 5)..(... * 2 + 0)"
  expectRangeAccess
    "selection can begin after an infinite source component"
    RangeValueKind
    ((<.>)
      ((..+) (natural 2))
      ((..+) ((AST.+) (...) (natural 10))))
    ((..+) (...))
    "(... + 10).."
  expectRangeAccess
    "descending transfinite selection preserves finite-tail arithmetic"
    RangeValueKind
    ((<.>)
      ((..+) (natural 2))
      ((..+) ((AST.+) (...) (natural 10))))
    ((<..>)
      ((AST.+) (...) (natural 2))
      ((AST.+) (...) (natural 0)))
    "(... + 12)..(... + 10)"
  expectRangeAccess
    "a computed range result remains reusable as an insertion"
    RangeValueKind
    ((..+) (natural 0))
    ((<@>) ((..+) (natural 10)) ((..+) (natural 5)))
    "15.."
  expectValue
      "ASCII-string singleton access"
      ((<@>) (AsciiStringLiteral "abcd") (natural 2)) $ \value ->
    assert "ordinary access remembers its ASCII-string result"
      ( interpretedValueKind value == AsciiStringValueKind
        && interpretedMapFinalOrderType (interpretedMap value)
          == finiteOrdinal 1
        && renderInterpretedValue value == "$c"
      )
  expectValue
      "ASCII-string range access"
      ((<@>)
        (AsciiStringLiteral "abcd")
        ((<..>) (natural 1) (natural 3))) $ \value ->
    assert "range access retains the selected ASCII string"
      ( interpretedValueKind value == AsciiStringValueKind
        && renderInterpretedValue value == "$bc"
      )
  expectValue
      "empty ASCII-string access"
      ((<@>)
        (AsciiStringLiteral "abcd")
        ((<..>) (natural 1) (natural 1))) $ \value ->
    assert "empty access remains an empty ASCII string"
      ( interpretedValueKind value == AsciiStringValueKind
        && interpretedMapCardinality (interpretedMap value) == 0
        && renderInterpretedValue value == "\"\""
      )
  let source = AtlasMap (map natural [0 .. 9])
      insertion =
        (<.>)
          ((<..>) (natural 2) (natural 5))
          ((<..>) (natural 5) (natural 8))
  expectValue "range-concatenation access" ((<@>) source insertion) $ \value -> do
    let valueMap = interpretedMap value
        selected =
          map
            (\position ->
              interpretedMapValueAt valueMap (finiteOrdinal position)
                >>= naturalOrdinal)
            [0 .. 6]
    assert "access follows concatenated insertion order"
      (selected == map Just [2 .. 7] <> [Nothing])
    assert "finite access renders its selected result values"
      (renderInterpretedValue value == "[2; 3; 4; 5; 6; 7]")
  let levelTwoFormulation =
        (AST.^) (...) (natural 2)
      mixedRankInsertion =
        (<.>)
          ((<..>) (natural 2) (natural 5))
          ((<..>) (natural 5) levelTwoFormulation)
  expectValue "mixed-rank range access"
      ((<@>) levelTwoFormulation mixedRankInsertion) $ \value ->
    assert "a cofinal mixed-rank selection canonicalizes as a formulation"
      ( interpretedValueKind value == FormulationValueKind
        && renderInterpretedValue value == "...^2"
      )
  expectValue
      "empty access"
      ((<@>)
        (AtlasMap [])
        ((<..>) (natural 3) (natural 3))) $ \value ->
    assert "empty maps and ranges are accepted by access"
      ( interpretedMapCardinality (interpretedMap value) == 0
        && interpretedMapFinalOrderType (interpretedMap value)
          == finiteOrdinal 0
      )
  expectValue
      "symbolic access result"
      ((<@>) (...) (...)) $ \value ->
    assert "full formulation access remains the same formulation"
      ( interpretedValueKind value == FormulationValueKind
        && renderInterpretedValue value == "..."
      )
  expectValue
      "cofinal formulation range access"
      ((<@>) (...) ((..+) (natural 5))) $ \value ->
    assert "a cofinal formulation tail canonicalizes as the formulation"
      ( interpretedValueKind value == FormulationValueKind
        && renderInterpretedValue value == "..."
      )
  expectRangeAccess
    "a formulation acts as a full-prefix range selector"
    RangeValueKind
    ((..+) (natural 10))
    (...)
    "10.."
  expectValue
      "a sequence wrapper preserves its range operand"
      ((<@>)
        (AtlasMap [((..+) (natural 2))])
        (NaturalRangeUpwards 0)) $ \value ->
    assert "sequence access returns the range operand without flattening it"
      (renderInterpretedValue value == "2..")
  assert "an infinite insertion cannot enter a sequence operand"
    (case interpretExpressionReason
        ((<@>)
          (AtlasMap [natural 42, ((..+) (natural 2))])
          ((..+) (natural 5))) of
      Left
          (AccessRejected
            (AccessInsertionRankExceedsMap insertionLimit mapOrderType)) ->
        insertionLimit == omega && mapOrderType == finiteOrdinal 2
      _ -> False)
  expectValue
      "NaturalRange accessed by NaturalRange"
      ((<@>) (NaturalRange 2 10) (NaturalRangeUpwards 1)) $ \value ->
    assert "NaturalRange access returns a NaturalRange"
      (renderInterpretedValue value == "from 3 to 10")
  expectValue
      "upwards NaturalRange accessed by NaturalRange"
      ((<@>)
        (NaturalRangeUpwards 2)
        (NaturalRangeUpwards 5)) $ \value ->
    assert "open NaturalRange access stays open"
      (renderInterpretedValue value == "from 7 upwards")
  expectValue
      "descending NaturalRange accessed in reverse"
      ((<@>) (NaturalRange 10 2) (NaturalRange 3 1)) $ \value ->
    assert "NaturalRange access composes traversal directions"
      (renderInterpretedValue value == "from 7 to 9")
  expectValue
      "NaturalRange access with no fitting member"
      ((<@>)
        (NaturalRange 2 4)
        (NaturalRangeUpwards 10)) $ \value ->
    assert "the empty result is the common NaturalRange access member"
      (renderInterpretedValue value == "[]")
  expectValue
      "NaturalRange accessed by empty ordinary range"
      ((<@>)
        (NaturalRange 2 10)
        ((<..>) (natural 0) (natural 0))) $ \value ->
    assert "empty selection succeeds on every federation member"
      (renderInterpretedValue value == "[]")
  assert "nonempty ordinary access is refuted by the empty member"
    (case interpretExpressionReason
        ((<@>)
          (NaturalRange 2 10)
          ((<..>) (natural 0) (natural 1))) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationAccessHasEmptyCounterexample) -> True
      _ -> False)
  let concatenatedNaturalRanges =
        (<.>) (NaturalRange 1 10) (NaturalRange 20 30)
  assert "nonempty access into concatenated NaturalRanges is refuted explicitly"
    (case interpretExpressionReason
        ((<@>) concatenatedNaturalRanges (natural 5)) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationAccessHasEmptyCounterexample) -> True
      _ -> False)
  assert "NaturalRange access into concatenated NaturalRanges is refuted explicitly"
    (case interpretExpressionReason
        ((<@>) concatenatedNaturalRanges (NaturalRangeUpwards 0)) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationAccessHasEmptyCounterexample) -> True
      _ -> False)
  expectValue
      "empty access into concatenated NaturalRanges still succeeds"
      ((<@>)
        concatenatedNaturalRanges
        ((<..>) (natural 0) (natural 0))) $ \value ->
    assert "empty selection succeeds on every concatenated federation member"
      (renderInterpretedValue value == "[]")
  expectValue
      "sequence access preserves structured federation operands"
      ((<@>)
        (NaturalRange 2 5 <:> NaturalRange 8 10)
        ((<..>) (natural 0) (natural 2))) $ \value ->
    assert "sequence access never flattens operand federations"
      (renderInterpretedValue value
        == "[from 2 to 5; from 8 to 10]")

testSpecification :: IO ()
testSpecification = do
  let expectSpecification label source target expected =
        expectValue label ((<~>) source target) $ \value ->
          assert label
            ( interpretedValueKind value == SpecificationValueKind
              && renderInterpretedValue value == expected
            )
      expectNoMember label source target =
        assert label
          (case interpretExpressionReason ((<~>) source target) of
            Left
                (AtlasMapFederationOperationRefuted
                  AtlasMapFederationSpecificationHasNoMatchingMember) -> True
            _ -> False)
      boundedRange = (<..>) (natural 2) (natural 5)
      rangeConcatenation =
        (<.>) boundedRange ((..+) (natural 8))
      rangeSequence =
        AtlasMap [boundedRange, AsciiStringLiteral "a"]
      compositeSequenceSource =
        AtlasMap [AsciiStringLiteral "a", natural 50]
      compositeSequenceTarget =
        AtlasMap [AsciiStringLiteral "a", NaturalType]
      compositeSequenceIntermediate =
        AtlasMap
          [ AsciiStringLiteral "a"
          , ValuedNaturalRange 1 100
          ]
      compositeExpansionSource =
        MapExpansion
          (AtlasMap [AsciiStringLiteral "a"])
          (AtlasMap [natural 50])
      compositeExpansionTarget =
        MapExpansion
          (AtlasMap [AsciiStringLiteral "a"])
          (AtlasMap [NaturalType])
      compositeExpansionIntermediate =
        MapExpansion
          (AtlasMap [AsciiStringLiteral "a"])
          (AtlasMap [ValuedNaturalRange 1 100])
      concatenate = foldr1 (<.>)
      compositeConcatenationSource =
        concatenate
          [ AsciiStringLiteral "a"
          , natural 3
          , natural 4
          , natural 5
          ]
      compositeConcatenationTarget =
        (<.>)
          (AsciiStringLiteral "a")
          (NaturalRange 1 10)
      compositeConcatenationWidenedTarget =
        (<.>)
          (AsciiStringLiteral "a")
          (NaturalRangeUpwards 0)
  expectSpecification
    "ASCII string self-specification"
    (AsciiStringLiteral "a")
    (AsciiStringLiteral "a")
    "$a ~> $a"
  expectSpecification
    "natural self-specification"
    (natural 2)
    (natural 2)
    "2 ~> 2"
  expectSpecification
    "range self-specification"
    boundedRange
    boundedRange
    "2..5 ~> 2..5"
  expectSpecification
    "range concatenation self-specification"
    rangeConcatenation
    rangeConcatenation
    "2..5, 8.. ~> 2..5, 8.."
  expectSpecification
    "sequence self-specification"
    rangeSequence
    rangeSequence
    "[2..5; $a] ~> [2..5; $a]"
  expectNoMember
    "different singleton total maps do not specify each other"
    (AsciiStringLiteral "a")
    (AsciiStringLiteral "b")
  expectSpecification
    "sequence federation selects members pointwise"
    compositeSequenceSource
    compositeSequenceTarget
    "[$a; 50] ~> [$a; Nat]"
  expectSpecification
    "concatenated federation partitions and selects members"
    compositeConcatenationSource
    compositeConcatenationTarget
    "[$a; 3; 4; 5] ~> $a, from 1 to 10"
  expectValue
      "expansion federation selects members pointwise"
      ((<~>) compositeExpansionSource compositeExpansionTarget) $ \value ->
    assert "expansion specification is defined"
      (interpretedValueKind value == SpecificationValueKind)
  expectValue
      "sequence subfederations compose pointwise"
      ((<~>)
        ((<~>) compositeSequenceSource compositeSequenceIntermediate)
        compositeSequenceTarget) $ \value ->
    assert "sequence composition retains the final target"
      (renderInterpretedValue value == "[$a; 50] ~> [$a; Nat]")
  expectValue
      "concatenated subfederations compose pointwise"
      ((<~>)
        ((<~>)
          compositeConcatenationSource
          compositeConcatenationTarget)
        compositeConcatenationWidenedTarget) $ \value ->
    assert "concatenation composition retains the final target"
      (renderInterpretedValue value
        == "[$a; 3; 4; 5] ~> $a, from 0 upwards")
  expectValue
      "expansion subfederations compose pointwise"
      ((<~>)
        ((<~>) compositeExpansionSource compositeExpansionIntermediate)
        compositeExpansionTarget) $ \value ->
    assert "expansion composition retains a specification"
      (interpretedValueKind value == SpecificationValueKind)
  assert "composite subfederations report a missing component"
    (case interpretExpressionReason
        ((<~>)
          ((<~>) compositeSequenceSource compositeSequenceIntermediate)
          (AtlasMap [AsciiStringLiteral "b", NaturalType])) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationSubfederationHasMissingMember) -> True
      _ -> False)
  expectSpecification
    "bounded ascending range specification"
    boundedRange
    (NaturalRange 0 10)
    "2..5 ~> from 0 to 10"
  expectSpecification
    "bounded descending range specification"
    ((<..>) (natural 5) (natural 2))
    (NaturalRange 10 0)
    "5..2 ~> from 10 to 0"
  expectSpecification
    "open range specification"
    ((..+) (natural 2))
    (NaturalRangeUpwards 0)
    "2.. ~> from 0 upwards"
  expectSpecification
    "empty range specification"
    ((<..>) (natural 0) (natural 0))
    (NaturalRange 5 8)
    "0..0 ~> from 5 to 8"
  expectSpecification
    "flat total Atlas map specification"
    (AtlasMap [natural 2, natural 3, natural 4])
    (NaturalRange 0 10)
    "[2; 3; 4] ~> from 0 to 10"
  expectSpecification
    "EllipsisNatural specification into a ValuedNaturalRange"
    (natural 2)
    (ValuedNaturalRange 0 5)
    "2 ~> within 0 to 5"
  expectSpecification
    "computed EllipsisNatural specification into a ValuedNaturalRange"
    ((AST.+) (natural 1) (natural 1))
    (ValuedNaturalRange 0 5)
    "2 ~> within 0 to 5"
  expectSpecification
    "EllipsisNatural specification into a descending ValuedNaturalRange"
    (natural 2)
    (ValuedNaturalRange 5 0)
    "2 ~> within 5 to 0"
  expectSpecification
    "EllipsisNatural specification into Nat"
    (natural 2)
    NaturalType
    "2 ~> Nat"
  expectValue
      "ValuedNaturalRange subfederation specification composition"
      ((<~>)
        ((<~>) (natural 2) (ValuedNaturalRange 2 5))
        NaturalType) $ \value ->
    assert "Nat composition erases the intermediate valued range"
      (renderInterpretedValue value == "2 ~> Nat")
  expectValue
      "ValuedNaturalRange inclusion ignores traversal direction"
      ((<~>)
        ((<~>) (natural 2) (ValuedNaturalRange 2 5))
        (ValuedNaturalRange 5 0)) $ \value ->
    assert "valued subfederation composition retains the final direction"
      (renderInterpretedValue value == "2 ~> within 5 to 0")
  expectValue
      "NaturalRange subfederation specification composition"
      ((<~>)
        ((<~>)
          ((<..>) (natural 2) (natural 3))
          (NaturalRange 2 5))
        (NaturalRange 2 8)) $ \value ->
    assert "composition erases the intermediate subfederation"
      ( interpretedValueKind value == SpecificationValueKind
        && renderInterpretedValue value == "2..3 ~> from 2 to 8"
      )
  expectValue
      "finite NaturalRange subfederation of an upwards NaturalRange"
      ((<~>)
        ((<~>)
          ((<..>) (natural 3) (natural 5))
          (NaturalRange 2 5))
        (NaturalRangeUpwards 0)) $ \value ->
    assert "finite-to-upwards composition is canonicalized"
      (renderInterpretedValue value == "3..5 ~> from 0 upwards")
  expectValue
      "upwards NaturalRange subfederation composition"
      ((<~>)
        ((<~>)
          ((..+) (natural 3))
          (NaturalRangeUpwards 2))
        (NaturalRangeUpwards 0)) $ \value ->
    assert "upwards-to-upwards composition is canonicalized"
      (renderInterpretedValue value == "3.. ~> from 0 upwards")
  expectValue
      "descending NaturalRange subfederation composition"
      ((<~>)
        ((<~>)
          ((<..>) (natural 5) (natural 2))
          (NaturalRange 6 1))
        (NaturalRange 8 0)) $ \value ->
    assert "descending composition preserves the original source"
      (renderInterpretedValue value == "5..2 ~> from 8 to 0")
  expectValue
      "singleton NaturalRange subfederation changes direction"
      ((<~>)
        ((<~>)
          ((<..>) (natural 2) (natural 3))
          (NaturalRange 2 2))
        (NaturalRange 5 0)) $ \value ->
    assert "a singleton federation belongs to either direction"
      (renderInterpretedValue value == "2..3 ~> from 5 to 0")
  expectNoMember
    "range outside the target NaturalRange is a counterexample"
    ((<..>) (natural 2) (natural 5))
    (NaturalRange 3 10)
  expectNoMember
    "open range cannot select a finite NaturalRange member"
    ((..+) (natural 2))
    (NaturalRange 0 10)
  expectNoMember
    "a noncontiguous total map has no NaturalRange member"
    (AtlasMap [natural 2, natural 4])
    (NaturalRange 0 10)
  expectNoMember
    "a one-page natural has no identity-pagination NaturalRange member"
    (natural 2)
    (NaturalRange 0 10)
  expectNoMember
    "a value outside a ValuedNaturalRange is a counterexample"
    (natural 6)
    (ValuedNaturalRange 0 5)
  expectNoMember
    "a range is not an EllipsisNatural value member"
    ((<..>) (natural 2) (natural 3))
    (ValuedNaturalRange 0 5)
  assert "a NaturalRange federation is not itself a TotalAtlasMap"
    (case interpretExpressionReason
        ((<~>) (NaturalRange 2 5) (NaturalRange 0 10)) of
      Left (ExpectedTotalAtlasMap RangeValueKind) -> True
      _ -> False)
  expectNoMember
    "a different singleton total target has no matching member"
    ((<..>) (natural 2) (natural 5))
    ((<..>) (natural 0) (natural 10))
  assert "composition rejects an intermediate federation with a missing member"
    (case interpretExpressionReason
        ((<~>)
          ((<~>)
            ((<..>) (natural 2) (natural 4))
            (NaturalRange 2 5))
          (NaturalRange 2 3)) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationSubfederationHasMissingMember) -> True
      _ -> False)
  assert "composition rejects incompatible NaturalRange directions"
    (case interpretExpressionReason
        ((<~>)
          ((<~>)
            ((<..>) (natural 2) (natural 3))
            (NaturalRange 2 5))
          (NaturalRange 5 2)) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationSubfederationHasMissingMember) -> True
      _ -> False)
  assert "an upwards intermediate federation is not finite"
    (case interpretExpressionReason
        ((<~>)
          ((<~>)
            ((..+) (natural 3))
            (NaturalRangeUpwards 2))
          (NaturalRange 0 10)) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationSubfederationHasMissingMember) -> True
      _ -> False)
  assert "an unknown subfederation relation remains undecided"
    (case interpretExpressionReason
        ((<~>)
          ((<~>)
            ((<..>) (natural 2) (natural 3))
            (NaturalRange 2 5))
          ((<..>) (natural 0) (natural 10))) of
      Left
          (AtlasMapFederationOperationUndecidable
            (NoAtlasMapFederationDecisionProcedure
              AtlasMapFederationSubfederation)) -> True
      _ -> False)
  assert "NaturalRange and ValuedNaturalRange are distinct federation families"
    (case interpretExpressionReason
        ((<~>)
          ((<~>) (natural 2) (ValuedNaturalRange 0 5))
          (NaturalRange 0 5)) of
      Left
          (AtlasMapFederationOperationRefuted
            AtlasMapFederationSubfederationHasMissingMember) -> True
      _ -> False)

testTypedRejections :: IO ()
testTypedRejections = do
  assert "non-ASCII programmatic string literals are rejected"
    (case interpretExpressionReason (AsciiStringLiteral "λ") of
      Left (InvalidAsciiStringCharacter 'λ') -> True
      _ -> False)
  assert "maps are rejected as numerical operands with a specific side"
    (case interpretExpressionReason
        ((AST.+) (AtlasMap []) (natural 1)) of
      Left (ExpectedNumericalOperand LeftOperand MapValueKind) -> True
      _ -> False)
  assert "computed non-natural values are rejected as exponents"
    (case interpretExpressionReason
        ((AST.^)
          (natural 2)
          ((AST.+) (...) (natural 0))) of
      Left (ExpectedNaturalExponent ExplicitOrdinalValueKind) -> True
      _ -> False)
  assert "out-of-bounds access reports the first invalid position"
    (case interpretExpressionReason
        ((<@>)
          (AtlasMap (map natural [0 .. 2]))
          ((<..>)
            (natural 2)
            (natural 5))) of
      Left
          (AccessRejected
            (AccessPositionOutOfBounds position orderType)) ->
        position == finiteOrdinal 3 && orderType == finiteOrdinal 3
      _ -> False)
  assert "infinite-rank access reports the map order type"
    (case interpretExpressionReason
        ((<@>)
          (AtlasMap (map natural [0 .. 2]))
          (...)) of
      Left
          (AccessRejected
            (AccessInsertionRankExceedsMap insertionLimit mapOrderType)) ->
        insertionLimit == omega && mapOrderType == finiteOrdinal 3
      _ -> False)
  assert "ordinary open ranges still fail instead of clipping"
    (case interpretExpressionReason
        ((<@>)
          ((<.>)
            (natural 1)
            ((<.>) (natural 2) (natural 3)))
          ((..+) (natural 1))) of
      Left
          (AccessRejected
            (AccessInsertionRankExceedsMap insertionLimit mapOrderType)) ->
        insertionLimit == omega && mapOrderType == finiteOrdinal 3
      _ -> False)
  assert "overlapping access ranges retain the exact overlap rejection"
    (case interpretExpressionReason
        ((<@>)
          (AtlasMap (map natural [0 .. 9]))
          ((<.>)
            ((<..>)
              (natural 2)
              (natural 5))
            ((<..>)
              (natural 4)
              (natural 7)))) of
      Left
          (RangeConcatenationRejected
            (SuperEllipsisRangesOverlap _ _ lower upper)) ->
        lower == finiteOrdinal 4 && upper == finiteOrdinal 5
      _ -> False)

testLocatedRejection :: IO ()
testLocatedRejection = do
  let sourceSpan =
        SourceSpan
          "<test>"
          (SourcePosition 4 1 5)
          (SourcePosition 10 1 11)
      expressionValue = (AST.+) (AtlasMap []) (natural 1)
  assert "typed interpretation errors retain their supplied source span"
    (case interpretLocatedExpression (Located sourceSpan expressionValue) of
      Left
          (DatraError
            (Just actualSpan)
            (ExpectedNumericalOperand LeftOperand MapValueKind)) ->
        actualSpan == sourceSpan
      _ -> False)
  assert "English interpretation errors are localized only at display time"
    (case interpretLocatedExpression (Located sourceSpan expressionValue) of
      Left valueError ->
        renderDatraError English valueError
          == "<test>:1:5: left operand must be numerical\n"
              <> "  actual value kind: map"
      Right _ -> False)
  assert "Romanian interpretation errors are localized only at display time"
    (case interpretLocatedExpression (Located sourceSpan expressionValue) of
      Left valueError ->
        renderDatraError Romanian valueError
          == "<test>:1:5: operandul stâng trebuie să fie numeric\n"
              <> "  tipul efectiv al valorii: hartă"
      Right _ -> False)
  let overlapExpression =
        (<@>)
          (AtlasMap (map natural [0 .. 9]))
          ((<.>)
            ((<..>)
              (natural 2)
              (natural 5))
            ((<..>)
              (natural 4)
              (natural 7)))
  assert "overlap diagnostics use source range notation and half-open bounds"
    (case interpretLocatedExpression (Located sourceSpan overlapExpression) of
      Left valueError ->
        renderDatraError English valueError
          == "<test>:1:5: cannot use overlapping ranges to access a map\n"
              <> "  first range: 2..5\n"
              <> "  second range: 4..7\n"
              <> "  overlap: 4..5 (upper bound excluded)"
      Right _ -> False)
  assert "Romanian overlap diagnostics use Datra range notation"
    (case interpretLocatedExpression (Located sourceSpan overlapExpression) of
      Left valueError ->
        renderDatraError Romanian valueError
          == "<test>:1:5: intervalele suprapuse nu pot fi folosite pentru a accesa o hartă\n"
              <> "  primul interval: 2..5\n"
              <> "  al doilea interval: 4..7\n"
              <> "  suprapunere: 4..5 (limita superioară este exclusă)"
      Right _ -> False)
