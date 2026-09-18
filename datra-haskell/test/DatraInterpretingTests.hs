module DatraInterpretingTests (main) where

import Datra.AST (Expression (..))
import Datra.Interpreting
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
import Datra.Rendering (renderInterpretedValue)
import DatraOrdinal
  ( finiteOrdinal
  , naturalAtOrdinal
  , omega
  , ordinal
  )
import Diagnostics
  ( DatraError (DatraError)
  , Located (Located)
  , SourcePosition (SourcePosition)
  , SourceSpan (SourceSpan)
  )
import Diagnostics.Localization
  ( Locale (English)
  , renderDatraError
  )
import MapOperators.AccessOperator
  ( AccessError
      ( AccessInsertionRankExceedsMap
      , AccessPositionOutOfBounds
      )
  )
import Numeric.Natural (Natural)
import SuperEllipsisRange
  ( SuperEllipsisRangeConcatError (SuperEllipsisRangesOverlap)
  , SuperEllipsisRangeDescription (SuperEllipsisRangeDescription)
  , SuperEllipsisRangeTarget (GivenTarget, PlusSign)
  )

main :: IO ()
main = do
  testLiteralsAndArithmetic
  testRanges
  testCanonicalResults
  testRendering
  testMaps
  testAccess
  testTypedRejections
  testLocatedRejection

assert :: String -> Bool -> IO ()
assert label condition
  | condition = pure ()
  | otherwise = fail ("test failed: " <> label)

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
  expectValue "natural literal" (EllipsisNatural 10) $ \value ->
    assert "naturals remain typed rank-one explicit values"
      ( interpretedValueKind value == NaturalValueKind
        && interpretedExplicitOrdinal value
          == Just (1, finiteOrdinal 10)
      )
  expectValue "Ellipsis literal" EllipsisLiteral $ \value ->
    assert "Ellipsis remains a formulation rather than an explicit ordinal"
      (interpretedFormulationLevel value == Just 1)
  expectValue
      "arithmetic precedence AST"
      (Addition
        (EllipsisNatural 1)
        (Multiplication (EllipsisNatural 2) (EllipsisNatural 3))) $ \value ->
    assert "natural arithmetic evaluates through ordinal operators"
      (interpretedExplicitOrdinal value == Just (1, finiteOrdinal 7))
  expectValue
      "Ellipsis soft coercion"
      (Addition EllipsisLiteral (EllipsisNatural 0)) $ \value ->
    assert "adding zero coerces Ellipsis to an explicit rank-two omega"
      (interpretedExplicitOrdinal value == Just (2, omega))
  expectValue
      "formulation multiplication"
      (Multiplication EllipsisLiteral EllipsisLiteral) $ \value ->
    assert "multiplying two Ellipsis formulations produces level two"
      (interpretedFormulationLevel value == Just 2)
  expectValue
      "zero formulation exponent"
      (Exponentiation EllipsisLiteral (EllipsisNatural 0)) $ \value ->
    assert "Ellipsis to zero evaluates to Dot"
      (interpretedFormulationLevel value == Just 0)
  expectValue
      "second formulation exponent"
      (Exponentiation EllipsisLiteral (EllipsisNatural 2)) $ \value ->
    assert "Ellipsis squared evaluates to a level-two formulation"
      (interpretedFormulationLevel value == Just 2)
  expectValue
      "ordinal multiplication order"
      (Multiplication
        (Addition EllipsisLiteral (EllipsisNatural 1))
        (EllipsisNatural 2)) $ \value ->
    assert "ordinal multiplication preserves noncommutative order"
      (interpretedExplicitOrdinal value
        == Just (2, ordinal [2, 1]))

testRanges :: IO ()
testRanges = do
  expectValue
      "bounded range"
      (SuperEllipsisRange (EllipsisNatural 2) (EllipsisNatural 5)) $ \value ->
    assert "bounded range retains its typed description"
      (interpretedRangeDescription value
        == Just
          (SuperEllipsisRangeDescription
            omega
            (finiteOrdinal 2)
            (GivenTarget (finiteOrdinal 5))))
  expectValue
      "open range"
      (SuperEllipsisRangePlus (EllipsisNatural 2)) $ \value ->
    assert "postfix range retains its open target"
      (interpretedRangeDescription value
        == Just
          (SuperEllipsisRangeDescription
            omega
            (finiteOrdinal 2)
            PlusSign))
  expectValue
      "parenthesized Ellipsis range semantics"
      (SuperEllipsisRangePlus EllipsisLiteral) $ \value ->
    assert "Ellipsis range endpoint is silently promoted to rank two"
      (interpretedRangeDescription value
        == Just
          (SuperEllipsisRangeDescription
            (ordinal [1, 0, 0])
            omega
            PlusSign))

testCanonicalResults :: IO ()
testCanonicalResults = do
  expectValue
      "adjacent ascending ranges"
      (MapConcatenation
        (SuperEllipsisRange (EllipsisNatural 2) (EllipsisNatural 5))
        (SuperEllipsisRangePlus (EllipsisNatural 5))) $ \value ->
    assert "adjacent ascending ranges canonicalize to one open range"
      (renderInterpretedValue value == "2..")
  expectValue
      "adjacent descending ranges"
      (MapConcatenation
        (SuperEllipsisRange (EllipsisNatural 9) (EllipsisNatural 5))
        (SuperEllipsisRange (EllipsisNatural 5) (EllipsisNatural 2))) $ \value ->
    assert "adjacent descending ranges canonicalize in traversal order"
      (renderInterpretedValue value == "9..2")
  let rankTwoFive =
        Addition
          (Multiplication EllipsisLiteral (EllipsisNatural 0))
          (EllipsisNatural 5)
  expectValue
      "adjacent mixed-rank ranges"
      (MapConcatenation
        (SuperEllipsisRange (EllipsisNatural 2) (EllipsisNatural 5))
        (SuperEllipsisRangePlus rankTwoFive)) $ \value ->
    assert "canonicalization happens after promotion to the common rank"
      (renderInterpretedValue value == "(... * 0 + 2)..")
  expectValue
      "disjoint ranges"
      (MapConcatenation
        (SuperEllipsisRange (EllipsisNatural 2) (EllipsisNatural 5))
        (SuperEllipsisRangePlus (EllipsisNatural 8))) $ \value ->
    assert "disjoint ranges retain their ordered concatenation"
      (renderInterpretedValue value == "2..5, 8..")
  expectValue
      "empty then nonempty range"
      (MapConcatenation
        (SuperEllipsisRange (EllipsisNatural 2) (EllipsisNatural 2))
        (SuperEllipsisRangePlus (EllipsisNatural 5))) $ \value ->
    assert "empty ranges are canonical concatenation identities"
      (renderInterpretedValue value == "5..")
  expectValue
      "overlapping range value"
      (MapConcatenation
        (SuperEllipsisRangePlus (EllipsisNatural 3))
        (SuperEllipsisRangePlus (EllipsisNatural 4))) $ \value ->
    assert "overlapping ranges remain an ordered map result"
      (renderInterpretedValue value == "3.., 4..")

testRendering :: IO ()
testRendering = do
  expectValue "formulation Ellipsis" EllipsisLiteral $ \value ->
    assert "literal Ellipsis retains formulation syntax"
      (renderInterpretedValue value == "...")
  expectValue
      "explicit omega"
      (Addition EllipsisLiteral (EllipsisNatural 0)) $ \value ->
    assert "explicit omega is distinguished from the formulation"
      (renderInterpretedValue value == "... + 0")
  expectValue
      "Dot formulation"
      (Exponentiation EllipsisLiteral (EllipsisNatural 0)) $ \value ->
    assert "Dot uses the agreed formulation syntax"
      (renderInterpretedValue value == "...^0")
  expectValue
      "second super-ellipsis formulation"
      (Exponentiation EllipsisLiteral (EllipsisNatural 2)) $ \value ->
    assert "higher formulations render by kind"
      (renderInterpretedValue value == "...^2")
  expectValue
      "rank-two finite value"
      (Addition
        (Multiplication EllipsisLiteral (EllipsisNatural 0))
        (EllipsisNatural 2)) $ \value ->
    assert "multiplication by zero appears only as a required rank witness"
      (renderInterpretedValue value == "... * 0 + 2")
  expectValue
      "map containing a canonical range"
      (AtlasMap
        [ MapConcatenation
            (SuperEllipsisRange (EllipsisNatural 2) (EllipsisNatural 5))
            (SuperEllipsisRangePlus (EllipsisNatural 5))
        ]) $ \value ->
    assert "maps render canonical infinite components without enumeration"
      (renderInterpretedValue value == "[2..]")

testMaps :: IO ()
testMaps = do
  let nested =
        AtlasMap
          [ AtlasMap [EllipsisNatural 1, EllipsisNatural 2]
          , AtlasMap [EllipsisNatural 3, EllipsisNatural 4]
          ]
  expectValue "nested map" nested $ \value -> do
    let valueMap = interpretedMap value
        values =
          map
            (\position ->
              interpretedMapValueAt valueMap (finiteOrdinal position)
                >>= naturalOrdinal)
            [0 .. 4]
    assert "nested map has the requested three-page cardinality"
      (interpretedMapCardinality valueMap == 3)
    assert "nested map final page preserves all four natural values"
      (values == map Just [1, 2, 3, 4] <> [Nothing])
    assert "nested maps render with their evaluated cardinality"
      (renderInterpretedValue value == "[[1; 2; 3; 4]]")
  expectValue
      "map concatenation"
      (MapConcatenation
        (AtlasMap [EllipsisNatural 1, EllipsisNatural 2])
        (AtlasMap [EllipsisNatural 3])) $ \value ->
    assert "map concatenation appends final-page order types"
      (interpretedMapFinalOrderType (interpretedMap value)
        == finiteOrdinal 3)

testAccess :: IO ()
testAccess = do
  let source = AtlasMap (map EllipsisNatural [0 .. 9])
      insertion =
        MapConcatenation
          (SuperEllipsisRange (EllipsisNatural 2) (EllipsisNatural 5))
          (SuperEllipsisRange (EllipsisNatural 5) (EllipsisNatural 8))
  expectValue "range-concatenation access" (MapAccess source insertion) $ \value -> do
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
  let rankTwoEight =
        Addition
          (Multiplication EllipsisLiteral (EllipsisNatural 0))
          (EllipsisNatural 8)
      mixedRankInsertion =
        MapConcatenation
          (SuperEllipsisRange (EllipsisNatural 2) (EllipsisNatural 5))
          (SuperEllipsisRange (EllipsisNatural 5) rankTwoEight)
  expectValue "mixed-rank range access"
      (MapAccess source mixedRankInsertion) $ \value -> do
    let valueMap = interpretedMap value
        selected =
          map
            (\position ->
              interpretedMapValueAt valueMap (finiteOrdinal position)
                >>= naturalOrdinal)
            [0 .. 6]
    assert "range concatenation promotes both ranges to their common rank"
      (selected == map Just [2 .. 7] <> [Nothing])
  expectValue
      "empty access"
      (MapAccess
        (AtlasMap [])
        (SuperEllipsisRange (EllipsisNatural 3) (EllipsisNatural 3))) $ \value ->
    assert "empty maps and ranges are accepted by access"
      ( interpretedMapCardinality (interpretedMap value) == 0
        && interpretedMapFinalOrderType (interpretedMap value)
          == finiteOrdinal 0
      )
  expectValue
      "symbolic access result"
      (MapAccess EllipsisLiteral EllipsisLiteral) $ \value ->
    assert "non-literal infinite selections use the symbolic fallback"
      (renderInterpretedValue value == "[<SuperEllipsisInsertion>]")

testTypedRejections :: IO ()
testTypedRejections = do
  assert "maps are rejected as numerical operands with a specific side"
    (case interpretExpressionReason
        (Addition (AtlasMap []) (EllipsisNatural 1)) of
      Left (ExpectedNumericalOperand LeftOperand MapValueKind) -> True
      _ -> False)
  assert "computed non-natural values are rejected as exponents"
    (case interpretExpressionReason
        (Exponentiation
          (EllipsisNatural 2)
          (Addition EllipsisLiteral (EllipsisNatural 0))) of
      Left (ExpectedNaturalExponent ExplicitOrdinalValueKind) -> True
      _ -> False)
  assert "out-of-bounds access reports the first invalid position"
    (case interpretExpressionReason
        (MapAccess
          (AtlasMap (map EllipsisNatural [0 .. 2]))
          (SuperEllipsisRange
            (EllipsisNatural 2)
            (EllipsisNatural 5))) of
      Left
          (AccessRejected
            (AccessPositionOutOfBounds position orderType)) ->
        position == finiteOrdinal 3 && orderType == finiteOrdinal 3
      _ -> False)
  assert "infinite-rank access reports the map order type"
    (case interpretExpressionReason
        (MapAccess
          (AtlasMap (map EllipsisNatural [0 .. 2]))
          EllipsisLiteral) of
      Left
          (AccessRejected
            (AccessInsertionRankExceedsMap insertionLimit mapOrderType)) ->
        insertionLimit == omega && mapOrderType == finiteOrdinal 3
      _ -> False)
  assert "overlapping access ranges retain the exact overlap rejection"
    (case interpretExpressionReason
        (MapAccess
          (AtlasMap (map EllipsisNatural [0 .. 9]))
          (MapConcatenation
            (SuperEllipsisRange
              (EllipsisNatural 2)
              (EllipsisNatural 5))
            (SuperEllipsisRange
              (EllipsisNatural 4)
              (EllipsisNatural 7)))) of
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
      expressionValue = Addition (AtlasMap []) (EllipsisNatural 1)
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
  let overlapExpression =
        MapAccess
          (AtlasMap (map EllipsisNatural [0 .. 9]))
          (MapConcatenation
            (SuperEllipsisRange
              (EllipsisNatural 2)
              (EllipsisNatural 5))
            (SuperEllipsisRange
              (EllipsisNatural 4)
              (EllipsisNatural 7)))
  assert "overlap diagnostics use source range notation and half-open bounds"
    (case interpretLocatedExpression (Located sourceSpan overlapExpression) of
      Left valueError ->
        renderDatraError English valueError
          == "<test>:1:5: cannot use overlapping ranges to access a map\n"
              <> "  first range: 2..5\n"
              <> "  second range: 4..7\n"
              <> "  overlap: 4..5 (upper bound excluded)"
      Right _ -> False)
