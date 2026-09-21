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
import Rendering (renderInterpretedValue)
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
  ( Locale (English, Română)
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
  , SuperEllipsisRangeTarget (GivenTarget, MinusSign, PlusSign)
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
    assert "sequential AST syntax constructs a flat two-page map"
      (interpretedMapCardinality (interpretedMap value) == 2)
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
      ((<.>)
        (AtlasMap [natural 1, natural 2])
        (AtlasMap [natural 3])) $ \value ->
    assert "map concatenation appends final-page order types"
      (interpretedMapFinalOrderType (interpretedMap value)
        == finiteOrdinal 3)

testAccess :: IO ()
testAccess = do
  let threeValues =
        (<.>)
          (natural 1)
          ((<.>) (natural 2) (natural 3))
      expectRangeAccess label expectedKind sourceValue selectionValue expected =
        expectValue label ((<@>) sourceValue selectionValue) $ \value ->
          assert label
            ( interpretedValueKind value == expectedKind
              && renderInterpretedValue value == expected
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
    assert "cross-rank range concatenation retains insertion capability"
      (renderInterpretedValue value == "<SuperEllipsisInsertion>")
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
    assert "non-literal infinite selections use the symbolic fallback"
      (renderInterpretedValue value == "<SuperEllipsisInsertion>")

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
        renderDatraError Română valueError
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
        renderDatraError Română valueError
          == "<test>:1:5: intervalele suprapuse nu pot fi folosite pentru a accesa o hartă\n"
              <> "  primul interval: 2..5\n"
              <> "  al doilea interval: 4..7\n"
              <> "  suprapunere: 4..5 (limita superioară este exclusă)"
      Right _ -> False)
