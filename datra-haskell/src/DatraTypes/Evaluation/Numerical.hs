-- | Checked numerical coercions and ordinal arithmetic for evaluated values.
module Evaluation.Numerical
  ( addValues
  , subtractValues
  , minusValue
  , multiplyValues
  , exponentiateValues
  , requireExplicit
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

-- | Numerical operators view every total map through its semantics. Named
-- total maps recursively expose their associated value through the same path,
-- so no identifier spelling or distinguished constructor needs a special
-- numerical rule.
numericalValue :: InterpretedValue -> Maybe NumericalValue
numericalValue value
  | interpretedValueHasTotalMap value =
      numericalSemantics (interpretedSemantics value)
  | otherwise = Nothing

numericalSemantics :: ValueSemantics -> Maybe NumericalValue
numericalSemantics semantics =
  case semantics of
    ExplicitSemantics level ordinalValue ->
      Just (ExplicitNumerical level ordinalValue)
    IntegerSemantics integer -> Just (IntegerNumerical integer)
    FormulationSemantics level -> Just (FormulationNumerical level)
    MapSemantics 0 [] -> Just (ExplicitNumerical 1 (finiteOrdinal 0))
    _ -> implicitCoercionSemantics semantics >>= numericalSemantics

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
