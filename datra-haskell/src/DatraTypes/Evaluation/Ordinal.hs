-- | Explicit ordinal arithmetic and comparisons for the Ordinals library.
module Evaluation.Ordinal
  ( ordinalSumValues
  , ordinalProductValues
  , ordinalMinusValues
  , ordinalExponentValues
  , ordinalLTValues
  , ordinalLTEValues
  , ordinalGTValues
  , ordinalGTEValues
  , requireExplicit
  , requireRangeUpperBoundary
  ) where

import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  , multiplyOrdinals
  , ordinalGT
  , ordinalGTE
  , ordinalLT
  , ordinalLTE
  , omegaPower
  , powerOrdinal
  , subtractOrdinal
  )
import Evaluation.Construction (makeExplicit, makeExplicitValue)
import Evaluation.Error
  ( FunctionFailure (NoApplicableFunctionAlternative)
  , InterpretingError (FunctionEvaluationFailed)
  )
import Evaluation.Numerical (requireNaturalExponent)
import Evaluation.Value
import Numeric.Natural (Natural)

ordinalSumValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
ordinalSumValues = ordinalBinary addOrdinals

ordinalProductValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
ordinalProductValues = ordinalBinary multiplyOrdinals

ordinalMinusValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
ordinalMinusValues left right = do
  x <- requireOrdinal left
  y <- requireOrdinal right
  pure (makeExplicit ComputedOrigin
    (maybe (finiteOrdinal 0) id (subtractOrdinal y x)))

ordinalExponentValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
ordinalExponentValues base exponentValue = do
  ordinalValue <- requireOrdinal base
  naturalPower <- requireNaturalExponent exponentValue
  pure (makeExplicit ComputedOrigin (powerOrdinal ordinalValue naturalPower))

ordinalLTValues, ordinalLTEValues, ordinalGTValues, ordinalGTEValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError Bool
ordinalLTValues = ordinalComparison ordinalLT
ordinalLTEValues = ordinalComparison ordinalLTE
ordinalGTValues = ordinalComparison ordinalGT
ordinalGTEValues = ordinalComparison ordinalGTE

ordinalBinary
  :: (Ordinal -> Ordinal -> Ordinal)
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
ordinalBinary operation left right = do
  leftValue <- requireOrdinal left
  rightValue <- requireOrdinal right
  pure (makeExplicit ComputedOrigin (operation leftValue rightValue))

ordinalComparison
  :: (Ordinal -> Ordinal -> Bool)
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError Bool
ordinalComparison operation left right = do
  leftValue <- requireOrdinal left
  rightValue <- requireOrdinal right
  pure (operation leftValue rightValue)

requireOrdinal
  :: InterpretedValue
  -> Either InterpretingError Ordinal
requireOrdinal value =
  case ordinalProjection (interpretedSemanticSemantics value) of
    Just (_, ordinalValue) -> Right ordinalValue
    Nothing -> noApplicableAlternative

requireExplicit
  :: InterpretedValue
  -> Either InterpretingError EvaluatedExplicit
requireExplicit value =
  case ordinalProjection (interpretedSemanticSemantics value) of
    Just (_, ordinalValue) ->
      Right (makeExplicitValue ComputedOrigin ordinalValue)
    Nothing -> noApplicableAlternative

requireRangeUpperBoundary
  :: InterpretedValue
  -> Either InterpretingError (Natural, Ordinal)
requireRangeUpperBoundary value =
  case ordinalProjection (interpretedSemanticSemantics value) of
    Just boundary -> Right boundary
    Nothing -> noApplicableAlternative

noApplicableAlternative :: Either InterpretingError value
noApplicableAlternative =
  Left (FunctionEvaluationFailed NoApplicableFunctionAlternative)

ordinalProjection :: ValueSemantics -> Maybe (Natural, Ordinal)
ordinalProjection (PresentedSemantics _ _ semantics) = ordinalProjection semantics
ordinalProjection semantics =
  case semantics of
    ExplicitSemantics level value -> Just (level, value)
    FormulationSemantics level -> Just (level, omegaPower level)
    MapSemantics 0 [] -> Just (1, finiteOrdinal 0)
    DependentArgumentTypeSemantics _ underlying _ _ ->
      ordinalProjection underlying
    AssignmentSemantics _ _ given -> ordinalProjection given
    SpecificationSemantics source _ -> ordinalProjection source
    _ -> Nothing
