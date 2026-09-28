-- | Checked finite numerical coercions and arithmetic for evaluated values.
module Evaluation.Numerical
  ( addValues
  , subtractValues
  , plusValue
  , minusValue
  , multiplyValues
  , exponentiateValues
  , requireFiniteInteger
  , requireNaturalExponent
  , numericallyEquivalent
  ) where

import DatraOrdinal
  ( Ordinal
  , finiteOrdinal
  , naturalAtOrdinal
  )
import Evaluation.Error
  ( InterpretingError (..)
  , OperandSide (..)
  )
import Evaluation.Construction
  ( makeExplicit
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
  , numericalDenotationOrdinal
  )

addValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
addValues left right = do
  case (numericalProjection left, numericalProjection right) of
    (Just (IntegerNumerical _), _) -> integerBinary (+) left right
    (_, Just (IntegerNumerical _)) -> integerBinary (+) left right
    _ -> do
      leftValue <- requireFiniteNumerical LeftOperand left
      rightValue <- requireFiniteNumerical RightOperand right
      pure (makeNumericalResult
        (addNumericalDenotations leftValue rightValue))

subtractValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
subtractValues = integerBinary (-)

plusValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
plusValue value =
  case numericalProjection value of
    Just (IntegerNumerical integer) -> Right (makeInteger integer)
    _ -> makeNumericalResult <$> requireFiniteNumerical LeftOperand value

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
  case (numericalProjection left, numericalProjection right) of
    (Just (IntegerNumerical _), _) -> integerBinary (*) left right
    (_, Just (IntegerNumerical _)) -> integerBinary (*) left right
    _ -> do
      leftValue <- requireFiniteNumerical LeftOperand left
      rightValue <- requireFiniteNumerical RightOperand right
      pure (makeNumericalResult
        (multiplyNumericalDenotations leftValue rightValue))

exponentiateValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
exponentiateValues base exponentValue = do
  naturalPower <- requireNaturalExponent exponentValue
  case numericalProjection base of
    Just (IntegerNumerical integer) ->
      pure (makeInteger (integer ^ naturalPower))
    _ -> do
      baseValue <- requireFiniteNumerical LeftOperand base
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
  case numericalProjection value >>= finiteInteger of
    Just integer -> Right integer
    Nothing ->
      Left (ExpectedFiniteIntegerOperand side (interpretedValueKind value))

requireFiniteNumerical
  :: OperandSide
  -> InterpretedValue
  -> Either InterpretingError NumericalDenotation
requireFiniteNumerical side value =
  case numericalProjection value of
    Just (FormulationNumerical 0) ->
      Right (ExplicitDenotation (finiteOrdinal 1))
    Just (ExplicitNumerical 1 ordinalValue)
      | Just _ <- naturalAtOrdinal ordinalValue ->
          Right (ExplicitDenotation ordinalValue)
    _ -> Left (ExpectedFiniteIntegerOperand side (interpretedValueKind value))

requireNaturalExponent
  :: InterpretedValue
  -> Either InterpretingError Natural
requireNaturalExponent value =
  case numericalProjection value of
    Just (ExplicitNumerical 1 ordinalValue) ->
      case naturalAtOrdinal ordinalValue of
        Just natural -> Right natural
        Nothing -> rejection
    _ -> rejection
  where
    rejection = Left (ExpectedNaturalExponent (interpretedValueKind value))

-- | Compare the shared numerical projections of two values.  'Nothing'
-- means at least one operand does not participate in numerical coercion.
-- This is intentionally the same projection used by arithmetic, including
-- the positional skip sentinel's rank-zero formulation payload.
numericallyEquivalent
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe Bool
numericallyEquivalent left right =
  (==) <$> (projectionOrdinal =<< numericalProjection left)
       <*> (projectionOrdinal =<< numericalProjection right)

data NumericalProjection
  = ExplicitNumerical Natural Ordinal
  | IntegerNumerical Integer
  | FormulationNumerical Natural

-- | Numerical operators first recognize direct numerical values, then view
-- specifications through their source when the target is a valued numerical
-- range. Identifiers expose the same specification shape, which keeps named
-- numerical values on this one coercion path.
numericalProjection :: InterpretedValue -> Maybe NumericalProjection
numericalProjection = numericalSemantics . interpretedSemantics

numericalSemantics :: ValueSemantics -> Maybe NumericalProjection
numericalSemantics semantics =
  case semantics of
    ExplicitSemantics level ordinalValue ->
      Just (ExplicitNumerical level ordinalValue)
    IntegerSemantics integer -> Just (IntegerNumerical integer)
    FormulationSemantics level -> Just (FormulationNumerical level)
    SkipSemantics _ -> Just (ExplicitNumerical 1 (finiteOrdinal 1))
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

finiteInteger :: NumericalProjection -> Maybe Integer
finiteInteger (IntegerNumerical integer) = Just integer
finiteInteger (ExplicitNumerical 1 ordinalValue) =
  toInteger <$> naturalAtOrdinal ordinalValue
finiteInteger _ = Nothing

projectionOrdinal :: NumericalProjection -> Maybe Ordinal
projectionOrdinal projection =
  case projection of
    ExplicitNumerical _ ordinalValue -> Just ordinalValue
    FormulationNumerical level ->
      Just (numericalDenotationOrdinal (FormulationDenotation level))
    IntegerNumerical integer
      | integer >= 0 -> Just (finiteOrdinal (fromInteger integer))
      | otherwise -> Nothing

makeNumericalResult :: NumericalDenotation -> InterpretedValue
makeNumericalResult (ExplicitDenotation value) =
  makeExplicit ComputedOrigin value
makeNumericalResult (FormulationDenotation level) =
  makeFormulation level
