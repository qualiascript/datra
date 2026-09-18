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
  , addOrdinals
  , multiplyOrdinals
  , naturalAtOrdinal
  , omegaPower
  , powerOrdinal
  )
import Diagnostics.Interpreter
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

data NumericalValue
  = ExplicitNumericalValue Ordinal
  | FormulationNumericalValue Natural

addValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
addValues left right = do
  leftValue <- requireNumerical LeftOperand left
  rightValue <- requireNumerical RightOperand right
  pure
    (makeExplicit ComputedOrigin
      (addOrdinals
        (numericalOrdinal leftValue)
        (numericalOrdinal rightValue)))

multiplyValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
multiplyValues left right = do
  leftValue <- requireNumerical LeftOperand left
  rightValue <- requireNumerical RightOperand right
  case (leftValue, rightValue) of
    ( FormulationNumericalValue leftLevel
      , FormulationNumericalValue rightLevel
      ) -> Right (makeFormulation (leftLevel + rightLevel))
    _ ->
      Right
        (makeExplicit ComputedOrigin
          (multiplyOrdinals
            (numericalOrdinal leftValue)
            (numericalOrdinal rightValue)))

exponentiateValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
exponentiateValues base exponentValue = do
  naturalPower <- requireNaturalExponent exponentValue
  case interpretedForm base of
    FormulationForm formulation ->
      Right
        (makeFormulation
          (someSuperEllipsisLevel formulation * naturalPower))
    ExplicitForm explicitValue ->
      Right
        (makeExplicit
          ComputedOrigin
          (powerOrdinal (snd (explicitOrdinal explicitValue)) naturalPower))
    _ ->
      Left
        (ExpectedNumericalOperand
          LeftOperand
          (interpretedValueKind base))

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
  -> Either InterpretingError NumericalValue
requireNumerical side value =
  case interpretedForm value of
    ExplicitForm explicitValue ->
      Right (ExplicitNumericalValue (snd (explicitOrdinal explicitValue)))
    FormulationForm formulation ->
      Right
        (FormulationNumericalValue
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

numericalOrdinal :: NumericalValue -> Ordinal
numericalOrdinal (ExplicitNumericalValue value) = value
numericalOrdinal (FormulationNumericalValue level) = omegaPower level
