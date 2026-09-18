-- | Recursive interpretation of the parsed Datra AST.
--
-- This module deliberately owns syntax traversal only. Checked semantic
-- operations and all type errors are provided by 'DatraTypes'.
module Datra.Interpreting
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
import Datra.AST (Expression (..))
import DatraTypes
import Diagnostics
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
interpretExpressionReason expressionValue =
  case expressionValue of
    EllipsisNatural value -> Right (naturalValue value)
    EllipsisLiteral -> Right (formulationValue 1)
    AtlasMap expressions ->
      interpretAtlasMapWith interpretExpressionReason expressions
    SuperEllipsisRange lower upper -> do
      lowerValue <- interpretExpressionReason lower
      upperValue <- interpretExpressionReason upper
      boundedRangeValue lowerValue upperValue
    SuperEllipsisRangePlus lower ->
      interpretExpressionReason lower >>= openPlusRangeValue
    SuperEllipsisRangeMinus upper ->
      interpretExpressionReason upper >>= openMinusRangeValue
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
  values <- traverse interpret expressions
  let nestingDepths =
        zipWith expressionNestingDepth expressions values
      mapDepth
        | null expressions = 0
        | otherwise = 1 + maximum nestingDepths
      cardinality
        | mapDepth == 0 = 0
        | otherwise = mapDepth + 1
  pure (makeAtlasMap cardinality values)

expressionNestingDepth :: Expression -> InterpretedValue -> Natural
expressionNestingDepth expressionValue value =
  case expressionValue of
    AtlasMap _ ->
      let cardinality = interpretedMapCardinality (interpretedMap value)
      in if cardinality == 0 then 0 else cardinality - 1
    _ -> 0
