-- | Checked numerical coercions and ordinal arithmetic for evaluated values.
module Evaluation.Numerical
  ( addValues
  , subtractValues
  , minusValue
  , multiplyValues
  , exponentiateValues
  , requireExplicit
  , requireFiniteInteger
  , requireRangeUpperBoundary
  ) where

import DatraOrdinal
  ( Ordinal
  , finiteOrdinal
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
  , makeInteger
  )
import Evaluation.Value
import Numeric.Natural (Natural)
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
  case (numericalValue left, numericalValue right) of
    (Just (IntegerNumerical _), _) -> integerBinary (+) left right
    (_, Just (IntegerNumerical _)) -> integerBinary (+) left right
    _ -> do
      leftValue <- requireNumerical LeftOperand left
      rightValue <- requireNumerical RightOperand right
      pure (makeNumericalResult
        (addNumericalDenotations leftValue rightValue))

subtractValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
subtractValues = integerBinary (-)

minusValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
minusValue value =
  makeInteger . negate <$> requireFiniteInteger LeftOperand value

multiplyValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
multiplyValues left right = do
  case (numericalValue left, numericalValue right) of
    (Just (IntegerNumerical _), _) -> integerBinary (*) left right
    (_, Just (IntegerNumerical _)) -> integerBinary (*) left right
    _ -> do
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
  case numericalValue base of
    Just (IntegerNumerical integer) ->
      pure (makeInteger (integer ^ naturalPower))
    _ -> do
      baseValue <- requireNumerical LeftOperand base
      pure (makeNumericalResult
        (exponentiateNumericalDenotation baseValue naturalPower))

integerBinary
  :: (Integer -> Integer -> Integer)
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
integerBinary operation left right = do
  leftValue <- requireFiniteInteger LeftOperand left
  rightValue <- requireFiniteInteger RightOperand right
  pure (makeInteger (operation leftValue rightValue))

requireFiniteInteger
  :: OperandSide
  -> InterpretedValue
  -> Either InterpretingError Integer
requireFiniteInteger side value =
  case numericalValue value >>= finiteInteger of
    Just integer -> Right integer
    Nothing ->
      Left (ExpectedFiniteIntegerOperand side (interpretedValueKind value))

requireExplicit
  :: OperandSide
  -> InterpretedValue
  -> Either InterpretingError EvaluatedExplicit
requireExplicit side value =
  case numericalValue value of
    Just (ExplicitNumerical _ ordinalValue) ->
      Right (makeExplicitValue ComputedOrigin ordinalValue)
    Just (FormulationNumerical level) ->
      Right
        (makeExplicitValue
          ComputedOrigin
          (omegaPower level))
    _ -> Left (ExpectedNumericalOperand side (interpretedValueKind value))

requireRangeUpperBoundary
  :: OperandSide
  -> InterpretedValue
  -> Either InterpretingError (Natural, Ordinal)
requireRangeUpperBoundary side value =
  case numericalValue value of
    Just (ExplicitNumerical level ordinalValue) ->
      Right (level, ordinalValue)
    Just (FormulationNumerical level) -> Right (level, omegaPower level)
    _ -> Left (ExpectedNumericalOperand side (interpretedValueKind value))

requireNumerical
  :: OperandSide
  -> InterpretedValue
  -> Either InterpretingError NumericalDenotation
requireNumerical side value =
  case numericalValue value of
    Just (ExplicitNumerical _ ordinalValue) ->
      Right (ExplicitDenotation ordinalValue)
    Just (FormulationNumerical level) ->
      Right (FormulationDenotation level)
    _ -> Left (ExpectedNumericalOperand side (interpretedValueKind value))

requireNaturalExponent
  :: InterpretedValue
  -> Either InterpretingError Natural
requireNaturalExponent value =
  case numericalValue value of
    Just (ExplicitNumerical 1 ordinalValue) ->
      case naturalAtOrdinal ordinalValue of
        Just natural -> Right natural
        Nothing -> rejection
    _ -> rejection
  where
    rejection = Left (ExpectedNaturalExponent (interpretedValueKind value))

data NumericalValue
  = ExplicitNumerical Natural Ordinal
  | IntegerNumerical Integer
  | FormulationNumerical Natural

-- | Numerical operators first recognize direct numerical values, then view
-- specifications through their source when the target is a valued numerical
-- range. Identifiers expose the same specification shape, which keeps named
-- numerical values on this one coercion path.
numericalValue :: InterpretedValue -> Maybe NumericalValue
numericalValue = numericalSemantics . interpretedSemantics

numericalSemantics :: ValueSemantics -> Maybe NumericalValue
numericalSemantics semantics =
  case semantics of
    ExplicitSemantics level ordinalValue ->
      Just (ExplicitNumerical level ordinalValue)
    IntegerSemantics integer -> Just (IntegerNumerical integer)
    FormulationSemantics level -> Just (FormulationNumerical level)
    MapSemantics 0 [] -> Just (ExplicitNumerical 1 (finiteOrdinal 0))
    _ -> do
      (source, target) <- numericalSpecification semantics
      if isValuedNumericalTarget target
        then numericalSemantics source
        else Nothing

-- An identifier is its identity specification. An assignment retains the
-- non-identity specification supplied by the user, while an ordinary
-- specification already has the required source and target directly.
numericalSpecification
  :: ValueSemantics
  -> Maybe (ValueSemantics, ValueSemantics)
numericalSpecification semantics =
  case semantics of
    DependentIdentifierTypeSemantics _ underlying True ->
      Just (underlying, underlying)
    AssignmentSemantics _ target source -> Just (source, target)
    SpecificationSemantics source target -> Just (source, target)
    _ -> Nothing

-- Concrete numerical values are singleton valued ranges. Nat and Int are the
-- corresponding unbounded valued ranges, and the empty map is their zero-size
-- case. Index-only ranges deliberately do not appear here.
isValuedNumericalTarget :: ValueSemantics -> Bool
isValuedNumericalTarget semantics =
  case semantics of
    ExplicitSemantics _ _ -> True
    IntegerSemantics _ -> True
    FormulationSemantics _ -> True
    ValuedNaturalRangeSemantics _ _ -> True
    NaturalTypeSemantics -> True
    ValuedIntegerRangeSemantics _ _ -> True
    IntegerTypeSemantics -> True
    MapSemantics 0 [] -> True
    DependentIdentifierTypeSemantics _ underlying True ->
      isValuedNumericalTarget underlying
    AssignmentSemantics _ target _ -> isValuedNumericalTarget target
    SpecificationSemantics _ target -> isValuedNumericalTarget target
    _ -> False

finiteInteger :: NumericalValue -> Maybe Integer
finiteInteger (IntegerNumerical integer) = Just integer
finiteInteger (ExplicitNumerical 1 ordinalValue) =
  toInteger <$> naturalAtOrdinal ordinalValue
finiteInteger _ = Nothing

makeNumericalResult :: NumericalDenotation -> InterpretedValue
makeNumericalResult (ExplicitDenotation value) =
  makeExplicit ComputedOrigin value
makeNumericalResult (FormulationDenotation level) =
  makeFormulation level
