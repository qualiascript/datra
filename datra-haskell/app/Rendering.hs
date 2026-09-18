module Rendering
  ( renderCanonicalResult
  , renderInterpretedValue
  ) where

import Data.Char (isDigit)
import Data.List (intercalate)
import DatraLanguage.AST.Operator
  ( Operator (..)
  , ellipsisSymbol
  , operatorCanonicalSymbol
  , operatorSourceSymbol
  )
import DatraTypes
  ( CanonicalResult (..)
  , InterpretedValue
  , interpretedCanonicalResult
  )
import DatraOrdinal
  ( Ordinal
  , ordinalCoefficients
  )
import Numeric.Natural (Natural)
import SuperEllipsisRange
  ( SuperEllipsisRangeDescription (..)
  , SuperEllipsisRangeTarget (..)
  )

-- | Render an evaluated value in Datra source notation. Internal AST
-- operators never appear here; maps use brackets and semicolons, while
-- compact ranges retain their range notation.
renderInterpretedValue :: InterpretedValue -> String
renderInterpretedValue = renderCanonicalResult . interpretedCanonicalResult

renderCanonicalResult :: CanonicalResult -> String
renderCanonicalResult result =
  case result of
    CanonicalExplicit _ value -> renderExplicit value
    CanonicalFormulation level -> renderFormulation level
    CanonicalRange description -> renderRange description
    CanonicalRangeConcatenation descriptions ->
      intercalate ", " (map renderRange descriptions)
    CanonicalMap cardinality components ->
      renderMap cardinality components
    CanonicalSuperEllipsisInsertion -> "<SuperEllipsisInsertion>"

renderMap :: Natural -> [CanonicalResult] -> String
renderMap 0 _ = "[]"
renderMap cardinality components =
  nest (cardinality - 1)
    (intercalate "; " (map renderCanonicalResult components))
  where
    nest 0 value = value
    nest depth value = "[" <> nest (depth - 1) value <> "]"

renderRange :: SuperEllipsisRangeDescription -> String
renderRange description =
  case describedRangeTarget description of
    GivenTarget target ->
      startText
        <> sourceSymbol RangeOperator
        <> rangeEndpoint (renderRangeBoundary target)
    PlusSign -> startText <> sourceSymbol RangePlusOperator
    MinusSign -> startText <> sourceSymbol RangeMinusOperator
  where
    start = describedRangeStart description
    startText = rangeEndpoint (renderExplicit start)

rangeEndpoint :: String -> String
rangeEndpoint value
  | not (null value) && all isDigit value = value
  | otherwise = "(" <> value <> ")"

renderFormulation :: Natural -> String
renderFormulation 0 =
  ellipsisSymbol <> sourceSymbol ExponentiationOperator <> "0"
renderFormulation 1 = ellipsisSymbol
renderFormulation level =
  ellipsisSymbol <> sourceSymbol ExponentiationOperator <> show level

renderExplicit :: Ordinal -> String
renderExplicit = renderExplicitMinimal

-- At an upper range boundary, a pure omega power is most naturally written
-- as the corresponding formulation. The boundary may equal the rank limit,
-- so this does not manufacture a value in the following rank.
renderRangeBoundary :: Ordinal -> String
renderRangeBoundary value =
  case ordinalCoefficients value of
    1 : remaining
      | not (null remaining) && all (== 0) remaining ->
          renderFormulation (fromIntegral (length remaining))
    _ -> renderExplicitMinimal value

-- A transfinite ordinal with no finite tail receives an explicit @+ 0@.
-- This distinguishes the value omega from the Ellipsis formulation, and the
-- same rule applies at every higher super-ellipsis level.
renderExplicitMinimal :: Ordinal -> String
renderExplicitMinimal value
  | isZero value = "0"
  | otherwise =
      renderOrdinal value
        <> if hasTransfiniteTerm value && hasZeroFiniteTail value
             then spacedSourceSymbol AdditionOperator <> "0"
             else ""

renderOrdinal :: Ordinal -> String
renderOrdinal value =
  intercalate (spacedSourceSymbol AdditionOperator)
    [ renderTerm power coefficient
    | (power, coefficient) <- zip [degree, degree - 1 .. 0] coefficients
    , coefficient /= 0
    ]
  where
    coefficients = ordinalCoefficients value
    degree = length coefficients - 1

    renderTerm 0 coefficient = show coefficient
    renderTerm 1 1 = ellipsisSymbol
    renderTerm 1 coefficient =
      ellipsisSymbol
        <> spacedSourceSymbol MultiplicationOperator
        <> show coefficient
    renderTerm power 1 =
      ellipsisSymbol
        <> sourceSymbol ExponentiationOperator
        <> show power
    renderTerm power coefficient =
      ellipsisSymbol
        <> sourceSymbol ExponentiationOperator
        <> show power
        <> spacedSourceSymbol MultiplicationOperator
        <> show coefficient

sourceSymbol :: Operator -> String
sourceSymbol operator =
  case operatorSourceSymbol operator of
    Just value -> value
    Nothing -> operatorCanonicalSymbol operator

spacedSourceSymbol :: Operator -> String
spacedSourceSymbol operator = " " <> sourceSymbol operator <> " "

isZero :: Ordinal -> Bool
isZero = null . ordinalCoefficients

hasTransfiniteTerm :: Ordinal -> Bool
hasTransfiniteTerm value = length (ordinalCoefficients value) > 1

hasZeroFiniteTail :: Ordinal -> Bool
hasZeroFiniteTail value =
  case reverse (ordinalCoefficients value) of
    0 : _ -> True
    _ -> False
