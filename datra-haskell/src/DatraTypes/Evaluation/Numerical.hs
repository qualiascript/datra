-- | Checked finite numerical coercions and arithmetic for evaluated values.
module Evaluation.Numerical
  ( addValues
  , subtractValues
  , plusValue
  , minusValue
  , multiplyValues
  , exponentiateValues
  , compareIntegerLimitValues
  , IntegerLimit (..)
  , integerLimitProjection
  , requireIntegerLimit
  , complementedIntegerTypeIncludesInfinity
  , nonnegativeFederationInComplementedInteger
  , makeIntegerLimit
  , requireFiniteInteger
  , requireNaturalExponent
  , numericallyEquivalent
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (SequentialAtlasMapFederation) )
import DatraOrdinal
  ( Ordinal
  , finiteOrdinal
  , naturalAtOrdinal
  )
import Evaluation.Error
  ( FunctionFailure (NoApplicableFunctionAlternative)
  , InterpretingError (..)
  )
import Evaluation.Construction
  ( makeExplicit
  , makeFormulation
  , makeInteger
  )
import Evaluation.Identifier (integerComplementValue)
import Evaluation.Value
import NaturalRange qualified
import Numeric.Natural (Natural)
import NumericalOperators.Semantics
  ( NumericalDenotation (..)
  , addNumericalDenotations
  , exponentiateNumericalDenotation
  , multiplyNumericalDenotations
  , numericalDenotationOrdinal
  )
import NumericalOperators.NumericalOperand (someSuperEllipsis)
import SuperEllipsisInsertion (fullSomeSuperEllipsisInsertion)

addValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
addValues left right = do
  case (integerLimitProjection left, integerLimitProjection right) of
    (Just leftLimit, Just rightLimit) ->
      addIntegerLimits "+" leftLimit rightLimit
    _ -> case (numericalProjection left, numericalProjection right) of
      (Just (IntegerNumerical _), _) -> integerBinary (+) left right
      (_, Just (IntegerNumerical _)) -> integerBinary (+) left right
      _ -> do
        leftValue <- requireFiniteNumerical left
        rightValue <- requireFiniteNumerical right
        pure (makeNumericalResult
          (addNumericalDenotations leftValue rightValue))

subtractValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
subtractValues left right = do
  leftValue <- requireIntegerLimit left
  rightValue <- requireIntegerLimit right
  addIntegerLimits "-" leftValue (negateIntegerLimit rightValue)

plusValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
plusValue value =
  case integerLimitProjection value of
    Just integer -> Right (makeIntegerLimit integer)
    Nothing -> makeNumericalResult <$> requireFiniteNumerical value

minusValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
minusValue value =
  makeIntegerLimit . negateIntegerLimit
    <$> requireIntegerLimit value

multiplyValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
multiplyValues left right = do
  case (integerLimitProjection left, integerLimitProjection right) of
    (Just leftLimit, Just rightLimit) ->
      multiplyIntegerLimits leftLimit rightLimit
    _ -> case (numericalProjection left, numericalProjection right) of
      (Just (IntegerNumerical _), _) -> integerBinary (*) left right
      (_, Just (IntegerNumerical _)) -> integerBinary (*) left right
      _ -> do
        leftValue <- requireFiniteNumerical left
        rightValue <- requireFiniteNumerical right
        pure (makeNumericalResult
          (multiplyNumericalDenotations leftValue rightValue))

exponentiateValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
exponentiateValues base exponentValue = do
  naturalPower <- requireNaturalExponent exponentValue
  case integerLimitProjection base of
    Just integer ->
      pure (makeIntegerLimit (powerIntegerLimit integer naturalPower))
    Nothing -> do
      baseValue <- requireFiniteNumerical base
      pure (makeNumericalResult
        (exponentiateNumericalDenotation baseValue naturalPower))

integerBinary
  :: (Integer -> Integer -> Integer)
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
integerBinary operation left right = do
  leftValue <- requireFiniteInteger left
  rightValue <- requireFiniteInteger right
  pure (makeInteger (operation leftValue rightValue))

addIntegerLimits
  :: String
  -> IntegerLimit
  -> IntegerLimit
  -> Either InterpretingError InterpretedValue
addIntegerLimits operator PositiveInfinity NegativeInfinity = indeterminate operator
addIntegerLimits operator NegativeInfinity PositiveInfinity = indeterminate operator
addIntegerLimits _ PositiveInfinity _ = Right (makeIntegerLimit PositiveInfinity)
addIntegerLimits _ _ PositiveInfinity = Right (makeIntegerLimit PositiveInfinity)
addIntegerLimits _ NegativeInfinity _ = Right (makeIntegerLimit NegativeInfinity)
addIntegerLimits _ _ NegativeInfinity = Right (makeIntegerLimit NegativeInfinity)
addIntegerLimits _ (FiniteInteger left) (FiniteInteger right) =
  Right (makeInteger (left + right))

multiplyIntegerLimits
  :: IntegerLimit
  -> IntegerLimit
  -> Either InterpretingError InterpretedValue
multiplyIntegerLimits (FiniteInteger 0) PositiveInfinity = indeterminate "*"
multiplyIntegerLimits (FiniteInteger 0) NegativeInfinity = indeterminate "*"
multiplyIntegerLimits PositiveInfinity (FiniteInteger 0) = indeterminate "*"
multiplyIntegerLimits NegativeInfinity (FiniteInteger 0) = indeterminate "*"
multiplyIntegerLimits (FiniteInteger left) (FiniteInteger right) =
  Right (makeInteger (left * right))
multiplyIntegerLimits left right =
  Right (makeIntegerLimit
    (if integerLimitSign left == integerLimitSign right
      then PositiveInfinity
      else NegativeInfinity))

indeterminate :: String -> Either InterpretingError value
indeterminate = Left . IndeterminateInfinityOperation

integerLimitSign :: IntegerLimit -> Ordering
integerLimitSign NegativeInfinity = LT
integerLimitSign PositiveInfinity = GT
integerLimitSign (FiniteInteger value) = compare value 0

negateIntegerLimit :: IntegerLimit -> IntegerLimit
negateIntegerLimit NegativeInfinity = PositiveInfinity
negateIntegerLimit PositiveInfinity = NegativeInfinity
negateIntegerLimit (FiniteInteger integer) = FiniteInteger (negate integer)

powerIntegerLimit :: IntegerLimit -> Natural -> IntegerLimit
powerIntegerLimit _ 0 = FiniteInteger 1
powerIntegerLimit (FiniteInteger integer) power =
  FiniteInteger (integer ^ power)
powerIntegerLimit PositiveInfinity _ = PositiveInfinity
powerIntegerLimit NegativeInfinity power
  | even power = PositiveInfinity
  | otherwise = NegativeInfinity

makeIntegerLimit :: IntegerLimit -> InterpretedValue
makeIntegerLimit NegativeInfinity = makeNegativeInfinity
makeIntegerLimit PositiveInfinity = makePositiveInfinity
makeIntegerLimit (FiniteInteger integer) = makeInteger integer

-- Negative infinity is the complemented positive-infinity magnitude, exactly
-- like the negative half of Std.IntLimit.  It is not a second infinity atom.
makeNegativeInfinity :: InterpretedValue
makeNegativeInfinity = withOrderedAtlasMapView value
  where
    values =
      [ makePositiveInfinity
      , integerComplementValue
      ]
    finalValues = foldl
      appendOrdinalOrderedValues
      emptyOrdinalOrderedValues
      (map singletonOrdinalOrderedValues values)
    components = map interpretedSemantics values
    semantics = IntegerLimitSemantics NegativeInfinity
    valueMap = InterpretedMap
      2
      finalValues
      (Right . ordinalOrderedValueAt finalValues)
      components
    value = makeInterpretedValue
      (composedStructuralDatraType (map interpretedDatraType values))
      SequentialMapForm
      NoInsertion
      valueMap
      (SequentialAtlasMapFederation
        (map interpretedAtlasMapFederation values))
      TotalInterpretedMap
      semantics

-- Infinity is a typed integer-limit atom. Keeping it to one map position lets
-- a closed valued range place the endpoint exactly at its transfinite boundary.
makePositiveInfinity :: InterpretedValue
makePositiveInfinity = value
  where
    underlying = FormulationSemantics 1
    semantics = IntegerLimitSemantics PositiveInfinity
    value =
      makeSingletonInterpretedValue
        structuralDatraType
        (FormulationForm (someSuperEllipsis 1))
        (ValidInsertion (fullSomeSuperEllipsisInsertion 0))
        (singletonMap underlying value)
        TotalInterpretedMap
        semantics

requireIntegerLimit
  :: InterpretedValue
  -> Either InterpretingError IntegerLimit
requireIntegerLimit value =
  case integerLimitProjection value of
    Just limit -> Right limit
    Nothing -> noApplicableAlternative

compareIntegerLimitValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError Ordering
compareIntegerLimitValues left right =
  compare
    <$> requireIntegerLimit left
    <*> requireIntegerLimit right

requireFiniteInteger
  :: InterpretedValue
  -> Either InterpretingError Integer
requireFiniteInteger value =
  case numericalProjection value >>= finiteInteger of
    Just integer -> Right integer
    Nothing -> noApplicableAlternative

requireFiniteNumerical
  :: InterpretedValue
  -> Either InterpretingError NumericalDenotation
requireFiniteNumerical value =
  case numericalProjection value of
    Just (FormulationNumerical 0) ->
      Right (ExplicitDenotation (finiteOrdinal 1))
    Just (ExplicitNumerical 1 ordinalValue)
      | Just _ <- naturalAtOrdinal ordinalValue ->
          Right (ExplicitDenotation ordinalValue)
    _ -> noApplicableAlternative

noApplicableAlternative :: Either InterpretingError value
noApplicableAlternative =
  Left (FunctionEvaluationFailed NoApplicableFunctionAlternative)

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
  case (integerLimitProjection left, integerLimitProjection right) of
    (Just leftLimit, Just rightLimit) -> Just (leftLimit == rightLimit)
    _ ->
      (==) <$> (projectionOrdinal =<< numericalProjection left)
           <*> (projectionOrdinal =<< numericalProjection right)

data NumericalProjection
  = ExplicitNumerical Natural Ordinal
  | IntegerNumerical Integer
  | FormulationNumerical Natural

integerLimitProjection :: InterpretedValue -> Maybe IntegerLimit
integerLimitProjection = integerLimitSemantics . interpretedSemanticSemantics

integerLimitSemantics :: ValueSemantics -> Maybe IntegerLimit
integerLimitSemantics (PresentedSemantics _ _ semantics) =
  integerLimitSemantics semantics
integerLimitSemantics semantics =
  case semantics of
    CoalizationSemantics operand -> integerLimitSemantics operand
    IntegerSemantics integer -> Just (FiniteInteger integer)
    IntegerLimitSemantics limit -> Just limit
    ExplicitSemantics 1 ordinalValue ->
      FiniteInteger . toInteger <$> naturalAtOrdinal ordinalValue
    FormulationSemantics 1 -> Just PositiveInfinity
    SkipSemantics _ -> Just (FiniteInteger 1)
    MapSemantics 0 [] -> Just (FiniteInteger 0)
    MapSemantics _ [magnitude, complement] -> do
      nonnegative <- integerLimitSemantics magnitude >>= requireNonnegative
      complementedIntegerValue nonnegative complement
    _ -> do
      (source, target) <- numericalSpecification semantics
      if isValuedNumericalTarget target
        then integerLimitSemantics source
        else Nothing
  where
    requireNonnegative limit =
      case limit of
        FiniteInteger integer
          | integer >= 0 -> Just limit
        PositiveInfinity -> Just limit
        _ -> Nothing

    complementedIntegerValue magnitude complement
      | absentComplement complement = Just magnitude
      | presentComplement complement =
          Just
            (case magnitude of
              FiniteInteger integer -> FiniteInteger (negate integer - 1)
              PositiveInfinity -> NegativeInfinity
              NegativeInfinity -> NegativeInfinity)
      | otherwise = Nothing

    absentComplement (PresentedSemantics _ _ value) = absentComplement value
    absentComplement (MapSemantics 0 []) = True
    absentComplement
        (DependentArgumentTypeSemantics
          (SimpleIdentifierDependency "Nothing")
          (MapSemantics 0 [])
          True
          _) = True
    absentComplement _ = False

    presentComplement (PresentedSemantics _ _ value) = presentComplement value
    presentComplement
        (DependentArgumentTypeSemantics
          (SimpleIdentifierDependency "Just")
          (AsciiStringSemantics "Complement")
          _
          _) = True
    presentComplement _ = False

-- | Numerical operators first recognize direct numerical values, then view
-- specifications through their source when the target is a valued numerical
-- range. Identifiers expose the same specification shape, which keeps named
-- numerical values on this one coercion path.
numericalProjection :: InterpretedValue -> Maybe NumericalProjection
numericalProjection = numericalSemantics . interpretedSemanticSemantics

numericalSemantics :: ValueSemantics -> Maybe NumericalProjection
numericalSemantics (PresentedSemantics _ _ semantics) =
  numericalSemantics semantics
numericalSemantics semantics =
  case semantics of
    CoalizationSemantics operand -> numericalSemantics operand
    ExplicitSemantics level ordinalValue ->
      Just (ExplicitNumerical level ordinalValue)
    IntegerSemantics integer -> Just (IntegerNumerical integer)
    IntegerLimitSemantics PositiveInfinity -> Just (FormulationNumerical 1)
    IntegerLimitSemantics NegativeInfinity -> Nothing
    IntegerLimitSemantics (FiniteInteger integer) ->
      Just (IntegerNumerical integer)
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
  case semanticValueSemantics semantics of
    DependentArgumentTypeSemantics _ underlying True _ ->
      Just (underlying, underlying)
    AssignmentSemantics _ target source -> Just (source, target)
    SpecificationSemantics source target -> Just (source, target)
    _ -> Nothing

-- Concrete numerical values are singleton valued ranges. Nat and Int are the
-- corresponding unbounded valued ranges, and the empty map is their zero-size
-- case. Index-only ranges deliberately do not appear here.
isValuedNumericalTarget :: ValueSemantics -> Bool
isValuedNumericalTarget (PresentedSemantics _ _ semantics) =
  isValuedNumericalTarget semantics
isValuedNumericalTarget semantics
  | Just _ <- complementedIntegerTypeIncludesInfinity semantics = True
  | otherwise = case semantics of
    CoalizationSemantics operand -> isValuedNumericalTarget operand
    ExplicitSemantics _ _ -> True
    IntegerSemantics _ -> True
    IntegerLimitSemantics _ -> True
    FormulationSemantics _ -> True
    EitherSemantics left right ->
      isValuedNumericalTarget left && isValuedNumericalTarget right
    ValuedNaturalRangeSemantics _ _ -> True
    NaturalTypeSemantics -> True
    ValuedIntegerRangeSemantics _ _ -> True
    IntegerTypeSemantics -> True
    MapSemantics 0 [] -> True
    DependentArgumentTypeSemantics _ underlying True _ ->
      isValuedNumericalTarget underlying
    AssignmentSemantics _ target _ -> isValuedNumericalTarget target
    SpecificationSemantics _ target -> isValuedNumericalTarget target
    _ -> False

-- Source-defined Int and IntLimit are sequences of a nonnegative magnitude
-- and the optional distinguished complement marker.  Recognize that
-- representation by structure so numerical behavior does not depend on a
-- standard-library binding name.
complementedIntegerTypeIncludesInfinity :: ValueSemantics -> Maybe Bool
complementedIntegerTypeIncludesInfinity (PresentedSemantics _ _ semantics) =
  complementedIntegerTypeIncludesInfinity semantics
complementedIntegerTypeIncludesInfinity semantics =
  case semantics of
    CoalizationSemantics operand ->
      complementedIntegerTypeIncludesInfinity operand
    MapSemantics _ [magnitude, complement]
      | Just includesInfinity <- nonnegativeMagnitude magnitude
      , optionalComplement complement -> Just includesInfinity
    _ -> Nothing

-- | Relate a nonnegative valued range to the source-defined complemented
-- integer carrier. Both sides are recognized from retained semantics rather
-- than library binding names. An infinity-extended magnitude is included only
-- when the complemented target retains its infinity member too.
nonnegativeFederationInComplementedInteger
  :: ValueSemantics
  -> ValueSemantics
  -> Maybe Bool
nonnegativeFederationInComplementedInteger source target = do
  sourceIncludesInfinity <- nonnegativeMagnitude source
  targetIncludesInfinity <- complementedIntegerTypeIncludesInfinity target
  pure (not sourceIncludesInfinity || targetIncludesInfinity)

nonnegativeMagnitude :: ValueSemantics -> Maybe Bool
nonnegativeMagnitude (PresentedSemantics _ _ semantics) =
  nonnegativeMagnitude semantics
nonnegativeMagnitude semantics =
  case semantics of
    CoalizationSemantics operand -> nonnegativeMagnitude operand
    NaturalTypeSemantics -> Just False
    ValuedNaturalRangeSemantics 0 NaturalRange.UpwardsTarget -> Just False
    ConcatenationSemantics members
      | any isPositiveInfinity members
      , all (\member -> isPositiveInfinity member
          || nonnegativeMagnitude member == Just False) members -> Just True
    _ -> Nothing
  where
    isPositiveInfinity (PresentedSemantics _ _ value) = isPositiveInfinity value
    isPositiveInfinity (IntegerLimitSemantics PositiveInfinity) = True
    isPositiveInfinity (FormulationSemantics 1) = True
    isPositiveInfinity _ = False

optionalComplement :: ValueSemantics -> Bool
optionalComplement semantics =
  let alternatives = flattenEither semantics
  in any isAbsent alternatives
      && any isComplement alternatives
      && all (\member -> isAbsent member || isComplement member) alternatives
  where
    flattenEither (PresentedSemantics _ _ value) = flattenEither value
    flattenEither (CoalizationSemantics operand) = flattenEither operand
    flattenEither (EitherSemantics left right) =
      flattenEither left <> flattenEither right
    flattenEither member = [member]

    isAbsent (PresentedSemantics _ _ value) = isAbsent value
    isAbsent (MapSemantics 0 []) = True
    isAbsent
        (DependentArgumentTypeSemantics
          (SimpleIdentifierDependency "Nothing")
          (MapSemantics 0 [])
          True
          _) = True
    isAbsent _ = False

    isComplement (PresentedSemantics _ _ value) = isComplement value
    isComplement
        (DependentArgumentTypeSemantics
          (SimpleIdentifierDependency "Just")
          (AsciiStringSemantics "Complement")
          _
          _) = True
    isComplement _ = False

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
