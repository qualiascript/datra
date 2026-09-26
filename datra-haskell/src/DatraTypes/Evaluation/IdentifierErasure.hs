-- | Remove identifier wrappers while preserving the surrounding map shape.
module Evaluation.IdentifierErasure
  ( stripIdentifiersValue
  , stripIdentifiersType
  ) where

import BooleanType (booleanNatural)
import Evaluation.Construction (makeNatural)
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import Evaluation.Arguments (makeArgumentMap, makeDistinctUnion)
import Evaluation.Error (InterpretingError (..), FunctionFailure (..))
import Evaluation.Map (makeAtlasMap, makeAtlasExpansion, concatenateValues, hasConcreteSource)
import Evaluation.Value

stripIdentifiersValue
  :: InterpretedValue -> Either InterpretingError InterpretedValue
stripIdentifiersValue value
  | hasConcreteSource value = stripIdentifiersType value
  | otherwise = Left (ExpectedTotalAtlasMap (interpretedValueKind value))

-- | Inference applies the same structural operation to the slot annotations.
-- Primitive types remain types; evaluation still requires a total operand.
stripIdentifiersType
  :: InterpretedValue -> Either InterpretingError InterpretedValue
stripIdentifiersType value
  | Just erased <- interpretedIdentifierErasureType value = Right erased
  | otherwise = erase value

erase :: InterpretedValue -> Either InterpretingError InterpretedValue
erase value = case interpretedForm value of
  BooleanForm flag -> Right (makeNatural (booleanNatural flag))
  DependentIdentifierTypeForm identifier ->
    stripIdentifiersType (evaluatedIdentifierUnderlying identifier)
  AssignmentForm specification -> eraseSpecification specification
  SpecificationForm specification -> eraseSpecification specification
  SequentialMapForm -> eraseMembers
  MapForm -> eraseMembers
  ExpansionMapForm left right ->
    makeAtlasExpansion (interpretedMapCardinality (interpretedMap value))
      <$> traverse stripIdentifiersType [left, right]
  ConcatenatedMapForm left right -> do
    erasedLeft <- stripIdentifiersType left
    erasedRight <- stripIdentifiersType right
    concatenateValues erasedLeft erasedRight
  ArgumentMapForm members _ ->
    traverse stripIdentifiersType members >>= makeArgumentMap
  EitherForm alternatives ->
    traverse stripIdentifiersType
      [evaluatedEitherLeft alternatives, evaluatedEitherRight alternatives]
      >>= makeDistinctUnion
  _ -> Right value
  where
    eraseSpecification = stripIdentifiersType . evaluatedSpecificationSourceValue
    eraseMembers = case naturalAtOrdinal (interpretedMapFinalOrderType (interpretedMap value)) of
      Nothing -> Right (makeLazyMapValue
        (interpretedMapFinalOrderType (interpretedMap value))
        (\position -> interpretedMapValueAt (interpretedMap value) position
          >>= either (const Nothing) Just . stripIdentifiersType))
      Just count -> do
        members <- traverse (\position -> maybe
          (Left (FunctionEvaluationFailed (FunctionArgumentPageUnavailable position)))
          stripIdentifiersType
          (interpretedMapValueAt (interpretedMap value) (finiteOrdinal position)))
          (if count == 0 then [] else [0 .. count - 1])
        pure (makeAtlasMap (interpretedMapCardinality (interpretedMap value)) members)
