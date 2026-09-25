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
import DatraLanguage.AST.Reserved qualified as Reserved
import DatraLanguage.AST
  ( StringTemplatePart (..)
  , renderAsciiStringLiteral
  , renderIdentifierString
  , renderStringTemplate
  )
import DatraTypes
  ( CanonicalResult (..)
  , builtinMetaTypeName
  , InterpretedValue
  , interpretedCanonicalResult
  , interpretedEvaluationSource
  )
import DatraOrdinal
  ( Ordinal
  , naturalAtOrdinal
  , ordinalCoefficients
  )
import Numeric.Natural (Natural)
import NaturalRange (NaturalRangeTarget (..))
import IntegerRange (IntegerRangeTarget (..))
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
renderInterpretedValue value =
  retainSource value (renderCanonicalResult (interpretedCanonicalResult value))

retainSource :: InterpretedValue -> String -> String
retainSource value result
  | CanonicalFunction {} <- interpretedCanonicalResult value = result
  | otherwise = case interpretedEvaluationSource value of
    Nothing -> result
    Just block -> operand <> " <~ " <> block
      where
        operand = case interpretedCanonicalResult value of
          CanonicalExplicit {} -> result
          _ -> "(" <> result <> ")"

-- | Render only the root map using implicit newline notation. Nested maps
-- keep their canonical parentheses. A semicolon is retained before a newline
-- when omitting it would let the range parser consume the next line.
renderInterpretedValueAsNewlineMap :: InterpretedValue -> String
renderInterpretedValueAsNewlineMap value =
  case interpretedEvaluationSource value of
    Just _ -> renderInterpretedValue value
    Nothing -> renderCanonicalResultAsNewlineMap (interpretedCanonicalResult value)

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
prettyCanonicalResult result
  | isBooleanValue "False" 0 result =
      pretty (Reserved.reservedSymbolIdentifierString Reserved.FalseSymbol)
  | isBooleanValue "True" 1 result =
      pretty (Reserved.reservedSymbolIdentifierString Reserved.TrueSymbol)
  | isNothingValue result =
      pretty (Reserved.reservedSymbolIdentifierString Reserved.NothingSymbol)
  | otherwise = prettyNonKeywordCanonicalResult result

prettyNonKeywordCanonicalResult :: CanonicalResult -> Doc annotation
prettyNonKeywordCanonicalResult result =
  case result of
    CanonicalBuiltinMetaType kind -> pretty (builtinMetaTypeName kind)
    CanonicalFunction input output patternInfo body ->
      let signature = parens (prettyCanonicalResult input) <+> "->" <+> parens (prettyCanonicalResult output)
          typed = case patternInfo of
            Nothing -> signature
            Just (text, ordinary) -> pretty (show text) <+> (if ordinary then "as?" else "as") <+> parens signature
      in case body of
        Nothing -> typed
        Just text -> parens (pretty text)
    CanonicalExplicit _ value -> prettyExplicit value
    CanonicalInteger value ->
      prettySourceSymbol MinusOperator <> pretty (negate value)
    CanonicalFormulation level -> prettyFormulation level
    CanonicalSkip _ -> "*"
    CanonicalRange description -> prettyRange description
    CanonicalNaturalRange origin target -> prettyNaturalRange origin target
    CanonicalValuedNaturalRange origin target ->
      prettyValuedNaturalRange origin target
    CanonicalNaturalType -> reservedSymbolDoc Reserved.NaturalTypeSymbol
    CanonicalIntegerRange origin target -> prettyIntegerRange origin target
    CanonicalValuedIntegerRange origin target ->
      prettyValuedIntegerRange origin target
    CanonicalIntegerType -> reservedSymbolDoc Reserved.IntegerTypeSymbol
    CanonicalEither left right -> prettyEither result left right
    CanonicalRangeConcatenation descriptions ->
      concatWith (\left right -> left <> ", " <> right)
        (map prettyRange descriptions)
    CanonicalConcatenation members ->
      concatWith (\left right -> left <> ", " <> right)
        (map prettyConcatenationMember members)
    CanonicalAsciiString value -> pretty (renderAsciiStringLiteral value)
    CanonicalStringType -> reservedSymbolDoc Reserved.StringTypeSymbol
    CanonicalIdentifierValueType ->
      reservedSymbolDoc Reserved.IdentifierValueTypeSymbol
    CanonicalToString source ->
      pretty
        (renderStringTemplate
          renderCanonicalResult
          compactCanonicalStringInterpolation
          [StringTemplateInterpolation source])
    CanonicalWeakToString source ->
      pretty
        (renderStringTemplate
          renderCanonicalResult
          compactCanonicalStringInterpolation
          [StringTemplateWeakInterpolation source])
    CanonicalStringTemplate template ->
      case canonicalStringTemplateParts template of
        Just parts ->
          pretty
            (renderStringTemplate
              renderCanonicalResult
              compactCanonicalStringInterpolation
              parts)
        Nothing -> prettyCanonicalResult template
    CanonicalDependentSum source -> pretty source
    CanonicalSimpleIdentifierType identifierString typeAnnotation ->
      pretty (renderIdentifierString identifierString)
        <+> prettySourceSymbol DependentIdentifierTypeOperator
        <+> prettyCanonicalResult typeAnnotation
    CanonicalDependentIdentifierType familyKey typeAnnotation ->
      pretty (renderIdentifierString familyKey)
        <+> prettySourceSymbol DependentIdentifierTypeOperator
        <+> prettyCanonicalResult typeAnnotation
    CanonicalIdentifierStringProjection familyKey typeAnnotation ->
      parens
        (pretty (renderIdentifierString familyKey)
          <+> prettySourceSymbol DependentIdentifierTypeOperator
          <+> prettyCanonicalResult typeAnnotation)
        <+> prettySourceSymbol AccessOperator
        <+> "0"
    CanonicalAssignment identifierString typeAnnotation givenValue ->
      prettyAssignment identifierString typeAnnotation givenValue
    CanonicalMap cardinality components ->
      prettyMap cardinality components
    CanonicalArgumentMap totalPages components ->
      let separator = if totalPages then ", " else "; "
      in "{" <> concatWith (\left right -> left <> separator <> right)
        (map prettyArgumentMember components) <> "}"
    CanonicalSpecification source target ->
      case (source, target) of
        ( CanonicalSimpleIdentifierType sourceString givenValue
          , CanonicalSimpleIdentifierType targetString typeAnnotation
          )
          | sourceString == targetString ->
              prettyAssignment sourceString typeAnnotation givenValue
        ( CanonicalAssignment sourceString sourceType givenValue
          , CanonicalSimpleIdentifierType targetString typeAnnotation
          )
          | sourceString == targetString && sourceType == givenValue ->
              prettyAssignment sourceString typeAnnotation givenValue
        _ ->
          prettySpecificationOperand source
            <+> prettySourceSymbol SpecificationOperator
            <+> prettySpecificationOperand target

prettyConcatenationMember :: CanonicalResult -> Doc annotation
prettyConcatenationMember member@CanonicalSpecification {} =
  parens (prettyCanonicalResult member)
prettyConcatenationMember member = prettyCanonicalResult member

-- A nested concatenation is one argument, rather than additional arguments
-- at the enclosing brace level. Specifications also need their own boundary.
prettyArgumentMember :: CanonicalResult -> Doc annotation
prettyArgumentMember member@CanonicalConcatenation {} =
  parens (prettyCanonicalResult member)
prettyArgumentMember member@CanonicalRangeConcatenation {} =
  parens (prettyCanonicalResult member)
prettyArgumentMember member = prettyConcatenationMember member

canonicalStringTemplateParts
  :: CanonicalResult
  -> Maybe [StringTemplatePart CanonicalResult]
canonicalStringTemplateParts result =
  case result of
    CanonicalConcatenation members ->
      concat <$> traverse canonicalStringTemplateParts members
    CanonicalAsciiString value -> Just [StringTemplateLiteral value]
    CanonicalStringType -> Just [StringTemplateInterpolation result]
    CanonicalIdentifierValueType ->
      Just [StringTemplateInterpolation result]
    CanonicalToString source -> Just [StringTemplateInterpolation source]
    CanonicalWeakToString source ->
      Just [StringTemplateWeakInterpolation source]
    CanonicalStringTemplate nested -> canonicalStringTemplateParts nested
    CanonicalDependentSum "Str" ->
      Just [StringTemplateInterpolation result]
    _ -> Nothing

compactCanonicalStringInterpolation :: CanonicalResult -> Maybe String
compactCanonicalStringInterpolation result
  | CanonicalEither operand missing <- result
  , isNothingValue missing =
      (<> sourceSymbol OptionalOperator)
        <$> compactCanonicalStringInterpolation operand
  | result == CanonicalStringType
      || result == CanonicalDependentSum "Str" =
      reserved Reserved.StringTypeSymbol
  | result == CanonicalIdentifierValueType =
      reserved Reserved.IdentifierValueTypeSymbol
  | result == CanonicalNaturalType = reserved Reserved.NaturalTypeSymbol
  | result == CanonicalIntegerType = reserved Reserved.IntegerTypeSymbol
  | isBooleanValue "False" 0 result = reserved Reserved.FalseSymbol
  | isBooleanValue "True" 1 result = reserved Reserved.TrueSymbol
  | isBooleanType result = reserved Reserved.BooleanTypeSymbol
  | isNothingValue result = reserved Reserved.NothingSymbol
  | otherwise = Nothing
  where
    reserved = Just . Reserved.reservedSymbolIdentifierString

prettySpecificationOperand :: CanonicalResult -> Doc annotation
prettySpecificationOperand operand =
  if isKeywordValue operand
    then prettyCanonicalResult operand
    else prettyNonKeywordSpecificationOperand operand

prettyNonKeywordSpecificationOperand
  :: CanonicalResult
  -> Doc annotation
prettyNonKeywordSpecificationOperand operand =
  case operand of
    CanonicalAssignment {} -> parens (prettyCanonicalResult operand)
    CanonicalEither {}
      | isBooleanType operand || isOptionalType operand ->
          prettyCanonicalResult operand
      | otherwise -> parens (prettyCanonicalResult operand)
    CanonicalSpecification {} -> parens (prettyCanonicalResult operand)
    _ -> prettyCanonicalResult operand

isKeywordValue :: CanonicalResult -> Bool
isKeywordValue value =
  isBooleanValue "False" 0 value
    || isBooleanValue "True" 1 value
    || isNothingValue value
    || value == CanonicalAsciiString "Nothing"

prettyEither
  :: CanonicalResult
  -> CanonicalResult
  -> CanonicalResult
  -> Doc annotation
prettyEither whole left right
  | isBooleanType whole = reservedSymbolDoc Reserved.BooleanTypeSymbol
  | isNothingValue right = prettyOptional left
  | Just optionalIdentifier <- optionalIdentifierParts left right =
      optionalIdentifier
  | otherwise =
      prettyCanonicalResult left
        <+> prettySourceSymbol EitherOperator
        <+> prettyCanonicalResult right

prettyOptional :: CanonicalResult -> Doc annotation
prettyOptional operand =
  optionalOperand <> prettySourceSymbol OptionalOperator
  where
    optionalOperand
      | isAtomicOptionalOperand operand = prettyCanonicalResult operand
      | otherwise = parens (prettyCanonicalResult operand)

isAtomicOptionalOperand :: CanonicalResult -> Bool
isAtomicOptionalOperand CanonicalNaturalType = True
isAtomicOptionalOperand CanonicalIntegerType = True
isAtomicOptionalOperand CanonicalStringType = True
isAtomicOptionalOperand (CanonicalDependentSum "Str") = True
isAtomicOptionalOperand CanonicalIdentifierValueType = True
isAtomicOptionalOperand operand = isBooleanType operand

optionalIdentifierParts
  :: CanonicalResult
  -> CanonicalResult
  -> Maybe (Doc annotation)
optionalIdentifierParts left right =
  case left of
    CanonicalSimpleIdentifierType identifierString typeAnnotation
      | typeAnnotation == right ->
          Just
            (pretty (renderIdentifierString identifierString)
              <> prettySourceSymbol OptionalOperator
              <+> prettySourceSymbol DependentIdentifierTypeOperator
              <+> prettyCanonicalResult typeAnnotation)
    CanonicalAssignment identifierString typeAnnotation givenValue
      | typeAnnotation == right ->
          Just
            (pretty (renderIdentifierString identifierString)
              <> prettySourceSymbol OptionalOperator
              <+> if typeAnnotation == givenValue
                then
                  prettySourceSymbol DependentIdentifierTypeOperator
                    <+> prettyCanonicalResult givenValue
                else
                  prettySourceSymbol DependentIdentifierTypeOperator
                    <+> prettyCanonicalResult typeAnnotation
                    <+> prettySourceSymbol AssignmentOperator
                    <+> prettyCanonicalResult givenValue)
    _ -> Nothing

isOptionalType :: CanonicalResult -> Bool
isOptionalType (CanonicalEither _ right) = isNothingValue right
isOptionalType _ = False

isNothingValue :: CanonicalResult -> Bool
isNothingValue
    (CanonicalAssignment "Nothing" typeAnnotation givenValue) =
  typeAnnotation == CanonicalMap 0 [] && givenValue == typeAnnotation
isNothingValue _ = False

isBooleanType :: CanonicalResult -> Bool
isBooleanType (CanonicalEither falseValue trueValue) =
  isBooleanValue "False" 0 falseValue
    && isBooleanValue "True" 1 trueValue
isBooleanType _ = False

isBooleanValue :: String -> Natural -> CanonicalResult -> Bool
isBooleanValue identifierString expected value =
  case value of
    CanonicalAssignment actual typeAnnotation givenValue ->
      actual == identifierString
        && typeAnnotation == givenValue
        && case givenValue of
          CanonicalExplicit 1 ordinalValue ->
            naturalAtOrdinal ordinalValue == Just expected
          _ -> False
    _ -> False

prettyAssignment
  :: String
  -> CanonicalResult
  -> CanonicalResult
  -> Doc annotation
prettyAssignment identifierString typeAnnotation givenValue =
  if typeAnnotation == givenValue
    then
      pretty (renderIdentifierString identifierString)
        <+> prettySourceSymbol DependentIdentifierTypeOperator
        <+> prettyCanonicalResult givenValue
    else
      pretty (renderIdentifierString identifierString)
        <+> prettySourceSymbol DependentIdentifierTypeOperator
        <+> prettyCanonicalResult typeAnnotation
        <+> prettySourceSymbol AssignmentOperator
        <+> prettyCanonicalResult givenValue

prettyNaturalRange
  :: Natural
  -> NaturalRangeTarget
  -> Doc annotation
prettyNaturalRange origin target =
  case target of
    FiniteNaturalTarget final ->
      rangeWord <> " " <> pretty origin
        <> " " <> toWord <> " " <> pretty final
    UpwardsTarget ->
      rangeWord <> " " <> pretty origin <> " " <> upwardsWord

prettyValuedNaturalRange
  :: Natural
  -> NaturalRangeTarget
  -> Doc annotation
prettyValuedNaturalRange origin target =
  case target of
    FiniteNaturalTarget final ->
      fromWord <> " " <> pretty origin
        <> " " <> toWord <> " " <> pretty final
    UpwardsTarget -> fromWord <> " " <> pretty origin <> " " <> upwardsWord

prettyIntegerRange
  :: Integer
  -> IntegerRangeTarget
  -> Doc annotation
prettyIntegerRange origin target =
  case target of
    FiniteIntegerTarget final ->
      rangeWord <> " " <> pretty origin
        <> " " <> toWord <> " " <> pretty final
    UpwardsIntegerTarget ->
      rangeWord <> " " <> pretty origin <> " " <> upwardsWord
    DownwardsIntegerTarget ->
      rangeWord <> " " <> pretty origin <> " " <> downwardsWord
    AllIntegersTarget -> reservedSymbolDoc Reserved.IntegerTypeSymbol

prettyValuedIntegerRange
  :: Integer
  -> IntegerRangeTarget
  -> Doc annotation
prettyValuedIntegerRange origin target =
  case target of
    FiniteIntegerTarget final ->
      fromWord <> " " <> pretty origin
        <> " " <> toWord <> " " <> pretty final
    UpwardsIntegerTarget ->
      fromWord <> " " <> pretty origin <> " " <> upwardsWord
    DownwardsIntegerTarget ->
      fromWord <> " " <> pretty origin <> " " <> downwardsWord
    AllIntegersTarget -> reservedSymbolDoc Reserved.IntegerTypeSymbol

rangeWord, fromWord, toWord, upwardsWord, downwardsWord :: Doc annotation
rangeWord = reservedSymbolDoc Reserved.RangeSymbol
fromWord = reservedSymbolDoc Reserved.FromSymbol
toWord = reservedWordDoc Reserved.ToWord
upwardsWord = reservedWordDoc Reserved.UpwardsWord
downwardsWord = reservedWordDoc Reserved.DownwardsWord

reservedWordDoc :: Reserved.ReservedWord -> Doc annotation
reservedWordDoc = pretty . Reserved.reservedWordText

reservedSymbolDoc :: Reserved.ReservedSymbol -> Doc annotation
reservedSymbolDoc = pretty . Reserved.reservedSymbolIdentifierString

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
  pretty ellipsisSymbol
    <> prettySpacedSourceSymbol ExponentiationOperator
    <> "0"
prettyFormulation 1 = pretty ellipsisSymbol
prettyFormulation level =
  pretty ellipsisSymbol
    <> prettySpacedSourceSymbol ExponentiationOperator
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
        <> prettySpacedSourceSymbol ExponentiationOperator
        <> pretty power
    renderTerm power coefficient =
      pretty ellipsisSymbol
        <> prettySpacedSourceSymbol ExponentiationOperator
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
