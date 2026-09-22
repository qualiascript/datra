-- | Recursive interpretation of the parsed Datra AST.
--
-- This module deliberately owns syntax traversal only. Checked semantic
-- operations and all type errors are provided by 'DatraTypes'.
module Interpreting
  ( InterpretedValue
  , CanonicalResult (..)
  , InterpretedValueKind (..)
  , InterpretedMap
  , InterpretingError (..)
  , OperandSide (..)
  , interpretExpression
  , interpretLocatedExpression
  , interpretExpressionReason
  , interpretedValueKind
  , interpretedCanonicalResult
  , interpretedExplicitOrdinal
  , interpretedFormulationLevel
  , interpretedRangeDescription
  , interpretedMap
  , interpretedMapCardinality
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  ) where

import Data.Bifunctor qualified as Bifunctor
import DatraLanguage.AST
  ( Expression (..)
  , Identifier (Identifier)
  , normalizeExpression
  )
import DatraTypes
import DatraLanguage.Diagnostics
  ( DatraError
  , Located (Located)
  , atSourceSpan
  , withoutSourceSpan
  )
import Numeric.Natural (Natural)

interpretExpression
  :: Expression
  -> Either (DatraError InterpretingError) InterpretedValue
interpretExpression =
  Bifunctor.first withoutSourceSpan . interpretExpressionReason

interpretLocatedExpression
  :: Located Expression
  -> Either (DatraError InterpretingError) InterpretedValue
interpretLocatedExpression (Located sourceSpan expressionValue) =
  Bifunctor.first (atSourceSpan sourceSpan)
    (interpretExpressionReason expressionValue)

interpretExpressionReason
  :: Expression
  -> Either InterpretingError InterpretedValue
interpretExpressionReason = interpretNormalizedExpression . normalizeExpression

interpretNormalizedExpression
  :: Expression
  -> Either InterpretingError InterpretedValue
interpretNormalizedExpression expressionValue =
  case expressionValue of
    EllipsisNatural value -> Right (naturalValue value)
    EllipsisLiteral -> Right (formulationValue 1)
    AsciiStringLiteral value -> asciiStringValue value
    AtlasMap expressions ->
      interpretAtlasMapWith interpretExpressionReason expressions
    MapSequence expressions ->
      interpretAtlasMapWith interpretExpressionReason expressions
    MapExpansion left right ->
      interpretAtlasMapWithBuilder
        makeAtlasExpansion
        interpretExpressionReason
        [ensureMapLevel left, ensureMapLevel right]
    SuperEllipsisRange lower upper -> do
      lowerValue <- interpretExpressionReason lower
      upperValue <- interpretExpressionReason upper
      boundedRangeValue lowerValue upperValue
    SuperEllipsisRangePlus lower ->
      interpretExpressionReason lower >>= openPlusRangeValue
    SuperEllipsisRangeMinus upper ->
      interpretExpressionReason upper >>= openMinusRangeValue
    NaturalRange origin target -> naturalRangeValue origin target
    NaturalRangeUpwards origin -> naturalRangeUpwardsValue origin
    ValuedNaturalRange origin target ->
      valuedNaturalRangeValue origin target
    ValuedNaturalRangeUpwards origin ->
      valuedNaturalRangeUpwardsValue origin
    NaturalType -> naturalTypeValue
    Addition left right ->
      interpretBinary addValues left right
    Multiplication left right ->
      interpretBinary multiplyValues left right
    Exponentiation base exponentValue ->
      interpretBinary exponentiateValues base exponentValue
    MapConcatenation left right ->
      interpretBinary concatenateValues left right
    MapAccess mapOperand insertionOperand ->
      interpretBinary accessValues mapOperand insertionOperand
    MapSpecification sourceOperand targetOperand ->
      interpretBinary specifyValues sourceOperand targetOperand
    IdentifierOperation (Identifier name) typeExpression assignment -> do
      typeValue <- interpretExpressionReason typeExpression
      case assignment of
        Nothing -> Right (simpleIdentifierTypeValue name typeValue)
        Just assignedExpression -> do
          assignedValue <- interpretExpressionReason assignedExpression
          assignIdentifierValues name assignedValue typeValue

interpretBinary
  :: ( InterpretedValue
       -> InterpretedValue
       -> Either InterpretingError InterpretedValue
     )
  -> Expression
  -> Expression
  -> Either InterpretingError InterpretedValue
interpretBinary operation left right = do
  leftValue <- interpretExpressionReason left
  rightValue <- interpretExpressionReason right
  operation leftValue rightValue

interpretAtlasMapWith
  :: (Expression -> Either InterpretingError InterpretedValue)
  -> [Expression]
  -> Either InterpretingError InterpretedValue
interpretAtlasMapWith interpret expressions = do
  interpretAtlasMapWithBuilder makeAtlasMap interpret expressions

interpretAtlasMapWithBuilder
  :: (Natural -> [InterpretedValue] -> InterpretedValue)
  -> (Expression -> Either InterpretingError InterpretedValue)
  -> [Expression]
  -> Either InterpretingError InterpretedValue
interpretAtlasMapWithBuilder buildMap interpret expressions = do
  values <- traverse interpret expressions
  let nestingDepths =
        zipWith expressionNestingDepth expressions values
      mapDepth
        | null expressions = 0
        | otherwise = 1 + maximum nestingDepths
      cardinality
        | mapDepth == 0 = 0
        | otherwise = mapDepth + 1
  pure (buildMap cardinality values)

expressionNestingDepth :: Expression -> InterpretedValue -> Natural
expressionNestingDepth expressionValue value =
  case expressionValue of
    AtlasMap _ -> mapNestingDepth
    MapSequence _ -> mapNestingDepth
    MapExpansion _ _ -> mapNestingDepth
    _ -> 0
  where
    mapNestingDepth =
      let cardinality = interpretedMapCardinality (interpretedMap value)
      in if cardinality == 0 then 0 else cardinality - 1

ensureMapLevel :: Expression -> Expression
ensureMapLevel expressionValue =
  case expressionValue of
    AtlasMap _ -> expressionValue
    MapSequence _ -> expressionValue
    MapExpansion _ _ -> expressionValue
    _ -> AtlasMap [expressionValue]
