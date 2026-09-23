-- | Leaf rules for selecting total Atlas maps from Atlas-map federations.
--
-- Composite constructions deliberately live elsewhere. Adding a primitive
-- rule here is enough for sequence, concatenation, and expansion selection to
-- inherit it through their recursive dispatcher.
module Evaluation.Specification.Federation
  ( selectAtomicFederationMember
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (..)
  )
import DatraOrdinal
  ( finiteOrdinal
  , naturalAtOrdinal
  , ordinalLT
  )
import Evaluation.Federation
  ( selectNaturalRangeMember
  , selectValuedNaturalRangeMember
  , selectIntegerRangeMember
  , selectValuedIntegerRangeMember
  )
import Evaluation.Specification.Decision
import Evaluation.Value
import NaturalRange qualified
import IntegerRange qualified
import Numeric.Natural (Natural)
import SuperEllipsisRange qualified as Range

-- | Decide the atomic federation families understood by specification.
-- 'Nothing' means the target is a composite construction and belongs to the
-- composition layer; a refuted atomic decision remains distinguishable from
-- that case.
selectAtomicFederationMember
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe (Decision EvaluatedAtlasMapFederationMember)
selectAtomicFederationMember source target =
  case interpretedAtlasMapFederation target of
    SingletonAtlasMapFederation _ ->
      Just
        (if interpretedValueHasTotalMap source
              && interpretedValueHasTotalMap target
              && interpretedCanonicalResult source
                == interpretedCanonicalResult target
          then
            DecisionProved
              (EvaluatedSingletonAtlasMapMember
                (interpretedCanonicalResult source))
          else DecisionRefuted)
    PrimitiveAtlasMapFederation
        (NaturalRangeAtlasMapFederation
          (EvaluatedNaturalRange targetRange)) ->
      Just
        (maybe
          DecisionRefuted
          (DecisionProved . EvaluatedNaturalRangeMember)
          (sourceNaturalSubrange source
            >>= selectNaturalRangeMember targetRange))
    PrimitiveAtlasMapFederation
        (ValuedNaturalRangeAtlasMapFederation
          (EvaluatedValuedNaturalRange targetRange)) ->
      Just
        (maybe
          DecisionRefuted
          (DecisionProved . EvaluatedValuedNaturalRangeMember)
          (sourceEllipsisNatural source
            >>= selectValuedNaturalRangeMember targetRange))
    PrimitiveAtlasMapFederation
        (IntegerRangeAtlasMapFederation
          (EvaluatedIntegerRange targetRange)) ->
      Just
        (maybe
          DecisionRefuted
          (DecisionProved . EvaluatedIntegerRangeMember)
          (sourceIntegerSubrange source
            >>= selectIntegerRangeMember targetRange))
    PrimitiveAtlasMapFederation
        (ValuedIntegerRangeAtlasMapFederation
          (EvaluatedValuedIntegerRange targetRange)) ->
      Just
        (maybe
          DecisionRefuted
          (DecisionProved . EvaluatedValuedIntegerRangeMember)
          (interpretedInteger source
            >>= selectValuedIntegerRangeMember targetRange))
    PrimitiveAtlasMapFederation (IdentifierTypeAtlasMapFederation _) ->
      Nothing
    PrimitiveAtlasMapFederation
        (IdentifierStringProjectionAtlasMapFederation _) ->
      Nothing
    PrimitiveAtlasMapFederation (EitherAtlasMapFederation _) -> Nothing
    SequentialAtlasMapFederation _ -> Nothing
    ConcatenatedAtlasMapFederation _ _ -> Nothing
    ExpansionAtlasMapFederation _ _ -> Nothing

sourceEllipsisNatural :: InterpretedValue -> Maybe Natural
sourceEllipsisNatural value =
  case interpretedForm value of
    ExplicitForm explicitValue ->
      let (level, ordinalValue) = explicitOrdinal explicitValue
      in if level == 1 then naturalAtOrdinal ordinalValue else Nothing
    SequentialMapForm -> do
      cardinality <-
        naturalAtOrdinal
          (interpretedMapFinalOrderType (interpretedMap value))
      if cardinality /= 1
        then Nothing
        else do
          member <-
            interpretedMapValueAt
              (interpretedMap value)
              (finiteOrdinal 0)
          sourceEllipsisNatural member
    _ -> Nothing

sourceNaturalSubrange
  :: InterpretedValue
  -> Maybe NaturalRange.NaturalSubrangeDescription
sourceNaturalSubrange value =
  case interpretedForm value of
    RangeForm valueRange -> rangeSubrange valueRange
    SequentialMapForm -> mapFormSubrange value
    ConcatenatedMapForm _ _ -> mapFormSubrange value
    ExpansionMapForm _ _ -> mapFormSubrange value
    MapForm -> mapFormSubrange value
    _ -> Nothing

sourceIntegerSubrange
  :: InterpretedValue
  -> Maybe IntegerRange.IntegerSubrangeDescription
sourceIntegerSubrange value =
  case interpretedForm value of
    IntegerRangeForm (EvaluatedIntegerRange valueRange) ->
      Just
        (IntegerRange.integerSubrangeDescription
          (IntegerRange.integerRangeFullSubrange valueRange))
    SequentialMapForm -> integerMapFormSubrange value
    ConcatenatedMapForm _ _ -> integerMapFormSubrange value
    ExpansionMapForm _ _ -> integerMapFormSubrange value
    MapForm -> integerMapFormSubrange value
    _ ->
      IntegerRange.FiniteIntegerSubrange <$> interpretedInteger value
        <*> interpretedInteger value

integerMapFormSubrange
  :: InterpretedValue
  -> Maybe IntegerRange.IntegerSubrangeDescription
integerMapFormSubrange value
  | interpretedMapPageCardinality (interpretedMap value) == 0 =
      Just IntegerRange.EmptyIntegerSubrange
  | otherwise = do
      cardinality <-
        naturalAtOrdinal
          (interpretedMapFinalOrderType (interpretedMap value))
      values <- traverse valueAt (finitePositions cardinality)
      integerSequenceSubrange values
  where
    valueAt position =
      interpretedMapValueAt
        (interpretedMap value)
        (finiteOrdinal position)
        >>= interpretedInteger
    finitePositions 0 = []
    finitePositions cardinality = [0 .. cardinality - 1]

integerSequenceSubrange
  :: [Integer]
  -> Maybe IntegerRange.IntegerSubrangeDescription
integerSequenceSubrange [] = Just IntegerRange.EmptyIntegerSubrange
integerSequenceSubrange [value] =
  Just (IntegerRange.FiniteIntegerSubrange value value)
integerSequenceSubrange values@(first : second : _)
  | second == first + 1 && ascending values =
      Just (IntegerRange.FiniteIntegerSubrange first (last values))
  | first == second + 1 && descending values =
      Just (IntegerRange.FiniteIntegerSubrange first (last values))
  | otherwise = Nothing
  where
    ascending (left : right : rest) =
      right == left + 1 && ascending (right : rest)
    ascending _ = True
    descending (left : right : rest) =
      left == right + 1 && descending (right : rest)
    descending _ = True

mapFormSubrange
  :: InterpretedValue
  -> Maybe NaturalRange.NaturalSubrangeDescription
mapFormSubrange value
  | interpretedMapPageCardinality (interpretedMap value) == 0 =
      Just NaturalRange.EmptyNaturalSubrange
  | interpretedMapPageCardinality (interpretedMap value) == 2 =
      mapSubrange value
  | otherwise = Nothing

mapSubrange
  :: InterpretedValue
  -> Maybe NaturalRange.NaturalSubrangeDescription
mapSubrange value =
  case interpretedSemantics value of
    MapSemantics _ [RangeSemantics description] ->
      describedRangeSubrange 1 description
    MapSemantics _ [ExplicitSemantics level ordinalValue] -> do
      natural <- naturalAtOrdinal ordinalValue
      if level == 1
        then Just (NaturalRange.FiniteNaturalSubrange natural natural)
        else Nothing
    _ -> do
      cardinality <-
        naturalAtOrdinal
          (interpretedMapFinalOrderType (interpretedMap value))
      values <- traverse valueAt (finitePositions cardinality)
      finiteSequenceSubrange values
  where
    valueAt position = do
      member <-
        interpretedMapValueAt
          (interpretedMap value)
          (finiteOrdinal position)
      (level, ordinalValue) <- interpretedExplicitOrdinal member
      if level == 1 then naturalAtOrdinal ordinalValue else Nothing

    finitePositions 0 = []
    finitePositions cardinality = [0 .. cardinality - 1]

rangeSubrange
  :: EvaluatedRange
  -> Maybe NaturalRange.NaturalSubrangeDescription
rangeSubrange valueRange =
  describedRangeSubrange
    (evaluatedRangeLevel valueRange)
    (rangeDescription valueRange)

describedRangeSubrange
  :: Natural
  -> Range.SuperEllipsisRangeDescription
  -> Maybe NaturalRange.NaturalSubrangeDescription
describedRangeSubrange level description
  | level /= 1 = Nothing
  | otherwise = do
      start <- naturalAtOrdinal (Range.describedRangeStart description)
      case Range.describedRangeTarget description of
        Range.PlusSign ->
          Just (NaturalRange.UpwardsNaturalSubrange start)
        Range.MinusSign ->
          Just (NaturalRange.FiniteNaturalSubrange start 0)
        Range.GivenTarget boundary -> do
          finalBoundary <- naturalAtOrdinal boundary
          if boundary == Range.describedRangeStart description
            then Just NaturalRange.EmptyNaturalSubrange
            else if ordinalLT (Range.describedRangeStart description) boundary
              then
                Just
                  (NaturalRange.FiniteNaturalSubrange
                    start (finalBoundary - 1))
              else
                Just
                  (NaturalRange.FiniteNaturalSubrange
                    start (finalBoundary + 1))

finiteSequenceSubrange
  :: [Natural]
  -> Maybe NaturalRange.NaturalSubrangeDescription
finiteSequenceSubrange [] = Just NaturalRange.EmptyNaturalSubrange
finiteSequenceSubrange [value] =
  Just (NaturalRange.FiniteNaturalSubrange value value)
finiteSequenceSubrange values@(first : second : _)
  | second == first + 1 && ascending values =
      Just (NaturalRange.FiniteNaturalSubrange first (last values))
  | first == second + 1 && descending values =
      Just (NaturalRange.FiniteNaturalSubrange first (last values))
  | otherwise = Nothing
  where
    ascending (left : right : rest) =
      right == left + 1 && ascending (right : rest)
    ascending _ = True

    descending (left : right : rest) =
      left == right + 1 && descending (right : rest)
    descending _ = True
