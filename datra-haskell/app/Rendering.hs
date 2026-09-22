{-# LANGUAGE OverloadedStrings #-}

module Rendering
  ( renderCanonicalResult
  , renderInterpretedValue
  , renderInterpretedValueAsNewlineMap
  ) where

import Data.Char (isDigit)
import Data.List (intercalate, isSuffixOf)
import DatraLanguage.AST.Operator
  ( Operator (..)
  , ellipsisSymbol
  , operatorCanonicalSymbol
  , operatorSourceSymbol
  )
import DatraLanguage.AST (renderAsciiStringLiteral)
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
import NaturalRange (NaturalRangeTarget (..))
import Prettyprinter
  ( Doc
  , (<+>)
  , concatWith
  , layoutCompact
  , parens
  , pretty
  )
import Prettyprinter.Render.String (renderString)
import SuperEllipsisRange
  ( SuperEllipsisRangeDescription (..)
  , SuperEllipsisRangeTarget (..)
  )

-- | Render an evaluated value in Datra source notation. Internal AST
-- operators never appear here; maps use parentheses and semicolons, while
-- compact ranges retain their range notation.
renderInterpretedValue :: InterpretedValue -> String
renderInterpretedValue = renderCanonicalResult . interpretedCanonicalResult

-- | Render only the root map using implicit newline notation. Nested maps
-- keep their canonical parentheses. A semicolon is retained before a newline
-- when omitting it would let the range parser consume the next line.
renderInterpretedValueAsNewlineMap :: InterpretedValue -> String
renderInterpretedValueAsNewlineMap =
  renderCanonicalResultAsNewlineMap . interpretedCanonicalResult

renderCanonicalResult :: CanonicalResult -> String
renderCanonicalResult = renderCompact . prettyCanonicalResult

renderCanonicalResultAsNewlineMap :: CanonicalResult -> String
renderCanonicalResultAsNewlineMap result =
  case result of
    CanonicalMap cardinality components ->
      renderNewlineMap cardinality components
    _ -> renderCanonicalResult result

renderNewlineMap :: Natural -> [CanonicalResult] -> String
renderNewlineMap _ [] = ""
renderNewlineMap _ [component] = renderCanonicalResult component
renderNewlineMap _ components =
  intercalate "\n" (terminateBeforeNewline renderedComponents)
  where
    renderedComponents = map renderCanonicalResult components

terminateBeforeNewline :: [String] -> [String]
terminateBeforeNewline [] = []
terminateBeforeNewline [lastComponent] = [lastComponent]
terminateBeforeNewline (component : remaining) =
  disambiguate component : terminateBeforeNewline remaining
  where
    disambiguate rendered
      | ".." `isSuffixOf` rendered = rendered <> ";"
      | otherwise = rendered

prettyCanonicalResult :: CanonicalResult -> Doc annotation
prettyCanonicalResult result =
  case result of
    CanonicalExplicit _ value -> prettyExplicit value
    CanonicalFormulation level -> prettyFormulation level
    CanonicalRange description -> prettyRange description
    CanonicalNaturalRange origin target -> prettyNaturalRange origin target
    CanonicalValuedNaturalRange origin target ->
      prettyValuedNaturalRange origin target
    CanonicalNaturalType -> "Nat"
    CanonicalRangeConcatenation descriptions ->
      concatWith (\left right -> left <> ", " <> right)
        (map prettyRange descriptions)
    CanonicalConcatenation members ->
      concatWith (\left right -> left <> ", " <> right)
        (map prettyCanonicalResult members)
    CanonicalAsciiString value -> pretty (renderAsciiStringLiteral value)
    CanonicalIdentifierType name underlying ->
      pretty name
        <+> prettySourceSymbol IdentifierTypeOperator
        <+> prettyCanonicalResult underlying
    CanonicalDependentIdentifierType key underlying ->
      pretty key
        <+> prettySourceSymbol IdentifierTypeOperator
        <+> prettyCanonicalResult underlying
    CanonicalIdentifierNameProjection key underlying ->
      parens
        (pretty key
          <+> prettySourceSymbol IdentifierTypeOperator
          <+> prettyCanonicalResult underlying)
        <+> prettySourceSymbol AccessOperator
        <+> "0"
    CanonicalAssignment name typeResult assignedResult ->
      prettyAssignment name typeResult assignedResult
    CanonicalMap cardinality components ->
      prettyMap cardinality components
    CanonicalSpecification source target ->
      case (source, target) of
        ( CanonicalIdentifierType sourceName assignedResult
          , CanonicalIdentifierType targetName typeResult
          )
          | sourceName == targetName ->
              prettyAssignment sourceName typeResult assignedResult
        _ ->
          prettyCanonicalResult source
            <+> prettySourceSymbol SpecificationOperator
            <+> prettyCanonicalResult target

prettyAssignment
  :: String
  -> CanonicalResult
  -> CanonicalResult
  -> Doc annotation
prettyAssignment name typeResult assignedResult =
  if typeResult == assignedResult
    then
      pretty name
        <+> prettySourceSymbol AssignmentOperator
        <+> prettyCanonicalResult assignedResult
    else
      pretty name
        <+> prettySourceSymbol IdentifierTypeOperator
        <+> prettyCanonicalResult typeResult
        <+> prettySourceSymbol AssignmentOperator
        <+> prettyCanonicalResult assignedResult

prettyNaturalRange
  :: Natural
  -> NaturalRangeTarget
  -> Doc annotation
prettyNaturalRange origin target =
  case target of
    FiniteNaturalTarget final ->
      "from " <> pretty origin <> " to " <> pretty final
    UpwardsTarget -> "from " <> pretty origin <> " upwards"

prettyValuedNaturalRange
  :: Natural
  -> NaturalRangeTarget
  -> Doc annotation
prettyValuedNaturalRange origin target =
  case target of
    FiniteNaturalTarget final ->
      "within " <> pretty origin <> " to " <> pretty final
    UpwardsTarget -> "within " <> pretty origin <> " upwards"

prettyMap :: Natural -> [CanonicalResult] -> Doc annotation
prettyMap 0 _ = "()"
prettyMap _ [component] = prettyCanonicalResult component
prettyMap _ components =
  parens
    (concatWith (\left right -> left <> "; " <> right)
      (map prettyCanonicalResult components))

prettyRange :: SuperEllipsisRangeDescription -> Doc annotation
prettyRange description =
  case describedRangeTarget description of
    GivenTarget target ->
      startText
        <> prettySourceSymbol RangeOperator
        <> rangeEndpoint (renderRangeBoundary target)
    PlusSign -> startText <> prettySourceSymbol RangePlusOperator
    MinusSign -> startText <> prettySourceSymbol RangeMinusOperator
  where
    start = describedRangeStart description
    startText = rangeEndpoint (renderCompact (prettyExplicit start))

rangeEndpoint :: String -> Doc annotation
rangeEndpoint value
  | not (null value) && all isDigit value = pretty value
  | otherwise = parens (pretty value)

prettyFormulation :: Natural -> Doc annotation
prettyFormulation 0 =
  pretty ellipsisSymbol <> prettySourceSymbol ExponentiationOperator <> "0"
prettyFormulation 1 = pretty ellipsisSymbol
prettyFormulation level =
  pretty ellipsisSymbol
    <> prettySourceSymbol ExponentiationOperator
    <> pretty level

prettyExplicit :: Ordinal -> Doc annotation
prettyExplicit = prettyExplicitMinimal

-- At an upper range boundary, a pure omega power is most naturally written
-- as the corresponding formulation. The boundary may equal the rank limit,
-- so this does not manufacture a value in the following rank.
renderRangeBoundary :: Ordinal -> String
renderRangeBoundary value =
  case ordinalCoefficients value of
    1 : remaining
      | not (null remaining) && all (== 0) remaining ->
          renderCompact (prettyFormulation (fromIntegral (length remaining)))
    _ -> renderCompact (prettyExplicitMinimal value)

-- A transfinite ordinal with no finite tail receives an explicit @+ 0@.
-- This distinguishes the value omega from the Ellipsis formulation, and the
-- same rule applies at every higher super-ellipsis level.
prettyExplicitMinimal :: Ordinal -> Doc annotation
prettyExplicitMinimal value
  | isZero value = "0"
  | otherwise =
      prettyOrdinal value
        <> if hasTransfiniteTerm value && hasZeroFiniteTail value
             then prettySpacedSourceSymbol AdditionOperator <> "0"
             else mempty

prettyOrdinal :: Ordinal -> Doc annotation
prettyOrdinal value =
  concatWith
    (\left right ->
      left <> prettySpacedSourceSymbol AdditionOperator <> right)
    [ renderTerm power coefficient
    | (power, coefficient) <- zip [degree, degree - 1 .. 0] coefficients
    , coefficient /= 0
    ]
  where
    coefficients = ordinalCoefficients value
    degree = length coefficients - 1

    renderTerm 0 coefficient = pretty coefficient
    renderTerm 1 1 = pretty ellipsisSymbol
    renderTerm 1 coefficient =
      pretty ellipsisSymbol
        <> prettySpacedSourceSymbol MultiplicationOperator
        <> pretty coefficient
    renderTerm power 1 =
      pretty ellipsisSymbol
        <> prettySourceSymbol ExponentiationOperator
        <> pretty power
    renderTerm power coefficient =
      pretty ellipsisSymbol
        <> prettySourceSymbol ExponentiationOperator
        <> pretty power
        <> prettySpacedSourceSymbol MultiplicationOperator
        <> pretty coefficient

prettySourceSymbol :: Operator -> Doc annotation
prettySourceSymbol = pretty . sourceSymbol

prettySpacedSourceSymbol :: Operator -> Doc annotation
prettySpacedSourceSymbol operator =
  " " <> prettySourceSymbol operator <> " "

sourceSymbol :: Operator -> String
sourceSymbol operator =
  case operatorSourceSymbol operator of
    Just value -> value
    Nothing -> operatorCanonicalSymbol operator

renderCompact :: Doc annotation -> String
renderCompact = renderString . layoutCompact

isZero :: Ordinal -> Bool
isZero = null . ordinalCoefficients

hasTransfiniteTerm :: Ordinal -> Bool
hasTransfiniteTerm value = length (ordinalCoefficients value) > 1

hasZeroFiniteTail :: Ordinal -> Bool
hasZeroFiniteTail value =
  case reverse (ordinalCoefficients value) of
    0 : _ -> True
    _ -> False
