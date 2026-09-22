-- | Checked numerical coercions and ordinal arithmetic for evaluated values.
module Evaluation.Numerical
  ( addValues
  , multiplyValues
  , exponentiateValues
  , requireExplicit
  , requireRangeUpperBoundary
  ) where

import DatraOrdinal
  ( Ordinal
  , naturalAtOrdinal
  , omegaPower
  )
import Evaluation.Error
  ( InterpretingError (..)
  , OperandSide (..)
  )
import Evaluation.Construction
  ( makeExplicit
  , makeExplicitValue
  , makeFormulation
  )
import Evaluation.Value
import Numeric.Natural (Natural)
import NumericalOperators.NumericalOperand (someSuperEllipsisLevel)
import NumericalOperators.Semantics
  ( NumericalDenotation (..)
  , addNumericalDenotations
  , exponentiateNumericalDenotation
  , multiplyNumericalDenotations
  )

addValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
addValues left right = do
  leftValue <- requireNumerical LeftOperand left
  rightValue <- requireNumerical RightOperand right
  pure (makeNumericalResult
    (addNumericalDenotations leftValue rightValue))

multiplyValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
multiplyValues left right = do
  leftValue <- requireNumerical LeftOperand left
  rightValue <- requireNumerical RightOperand right
  pure (makeNumericalResult
    (multiplyNumericalDenotations leftValue rightValue))

exponentiateValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
exponentiateValues base exponentValue = do
  naturalPower <- requireNaturalExponent exponentValue
  baseValue <- requireNumerical LeftOperand base
  pure (makeNumericalResult
    (exponentiateNumericalDenotation baseValue naturalPower))

requireExplicit
  :: OperandSide
  -> InterpretedValue
  -> Either InterpretingError EvaluatedExplicit
requireExplicit side value =
  case interpretedForm value of
    ExplicitForm explicitValue -> Right explicitValue
    FormulationForm formulation ->
      Right
        (makeExplicitValue
          ComputedOrigin
          (omegaPower (someSuperEllipsisLevel formulation)))
    _ -> Left (ExpectedNumericalOperand side (interpretedValueKind value))

requireRangeUpperBoundary
  :: OperandSide
  -> InterpretedValue
  -> Either InterpretingError (Natural, Ordinal)
requireRangeUpperBoundary side value =
  case interpretedForm value of
    ExplicitForm explicitValue -> Right (explicitOrdinal explicitValue)
    FormulationForm formulation ->
      let level = someSuperEllipsisLevel formulation
      in Right (level, omegaPower level)
    _ -> Left (ExpectedNumericalOperand side (interpretedValueKind value))

requireNumerical
  :: OperandSide
  -> InterpretedValue
  -> Either InterpretingError NumericalDenotation
requireNumerical side value =
  case interpretedForm value of
    ExplicitForm explicitValue ->
      Right (ExplicitDenotation (snd (explicitOrdinal explicitValue)))
    FormulationForm formulation ->
      Right
        (FormulationDenotation
          (someSuperEllipsisLevel formulation))
    _ -> Left (ExpectedNumericalOperand side (interpretedValueKind value))

requireNaturalExponent
  :: InterpretedValue
  -> Either InterpretingError Natural
requireNaturalExponent value =
  case interpretedForm value of
    ExplicitForm explicitValue ->
      case explicitOrdinal explicitValue of
        (1, ordinalValue) ->
          case naturalAtOrdinal ordinalValue of
            Just natural -> Right natural
            Nothing -> rejection
        _ -> rejection
    _ -> rejection
  where
    rejection = Left (ExpectedNaturalExponent (interpretedValueKind value))

makeNumericalResult :: NumericalDenotation -> InterpretedValue
makeNumericalResult (ExplicitDenotation value) =
  makeExplicit ComputedOrigin value
makeNumericalResult (FormulationDenotation level) =
  makeFormulation level
