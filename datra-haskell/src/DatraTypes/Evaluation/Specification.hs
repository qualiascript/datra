-- | Compile-time decision procedure for the specification operator.
module Evaluation.Specification
  ( specifyValues
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationDecision (..)
  , AtlasMapFederationExpression (PrimitiveAtlasMapFederation)
  )
import AtlasMapSubfederation (decideAtlasMapSubfederation)
import DatraLanguage.Diagnostics.Interpreter
  ( AtlasMapFederationOperation
      ( AtlasMapFederationSpecification
      , AtlasMapFederationSubfederation
      )
  , AtlasMapFederationRefutation
      ( AtlasMapFederationSpecificationHasNoMatchingMember
      , AtlasMapFederationSubfederationHasMissingMember
      )
  , AtlasMapFederationUncertainty
      (NoAtlasMapFederationDecisionProcedure)
  , InterpretingError (..)
  )
import DatraOrdinal
  ( finiteOrdinal
  , naturalAtOrdinal
  , ordinalLT
  )
import Evaluation.Value
import NaturalRange qualified
import Numeric.Natural (Natural)
import SuperEllipsisRange qualified as Range
import ValuedNaturalRange qualified

-- | NaturalRange and ValuedNaturalRange have separate target-specific
-- decision procedures.  NaturalRange members are range Atlases;
-- ValuedNaturalRange members are individual EllipsisNatural Atlases.  Both
-- families have total members, but that fact is not inferred for arbitrary
-- Atlas-map federations.
specifyValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyValues source target =
  case interpretedForm source of
    SpecificationForm specification ->
      widenSpecification source specification target
    _ -> specifyTotalAtlasMap source target

specifyTotalAtlasMap
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyTotalAtlasMap source target = do
  totalSource <-
    case interpretedTotalAtlasMap source of
      Just totalMap -> Right totalMap
      Nothing -> Left (ExpectedTotalAtlasMap (interpretedValueKind source))
  case interpretedAtlasMapFederation target of
    PrimitiveAtlasMapFederation
        (NaturalRangeAtlasMapFederation
          (EvaluatedNaturalRange targetRange)) ->
      case sourceNaturalSubrange source
          >>= selectNaturalRangeMember targetRange of
        Nothing -> noMatchingMember
        Just member ->
          Right
            (specifiedValue
              totalSource
              (interpretedSemantics source)
              target
              (EvaluatedNaturalRangeMember member))
    PrimitiveAtlasMapFederation
        (ValuedNaturalRangeAtlasMapFederation
          (EvaluatedValuedNaturalRange targetRange)) ->
      case sourceEllipsisNatural source
          >>= selectValuedNaturalRangeMember targetRange of
        Nothing -> noMatchingMember
        Just member ->
          Right
            (specifiedValue
              totalSource
              (interpretedSemantics source)
              target
              (EvaluatedValuedNaturalRangeMember member))
    _ ->
      Left
        (AtlasMapFederationOperationUndecidable
          (NoAtlasMapFederationDecisionProcedure
            AtlasMapFederationSpecification))
  where
    noMatchingMember =
      Left
        (AtlasMapFederationOperationRefuted
          AtlasMapFederationSpecificationHasNoMatchingMember)

-- | Compose a prior specification with inclusion of its whole target
-- federation into a larger target.  Checking only the previously selected
-- member would be weaker: the intermediate object itself must be an Atlas
-- subfederation of the final object.
widenSpecification
  :: InterpretedValue
  -> EvaluatedSpecification
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
widenSpecification source specification target =
  case decideAtlasMapSubfederation
      (NoAtlasMapFederationDecisionProcedure
        AtlasMapFederationSubfederation)
      decidePrimitiveSubfederation
      (evaluatedSpecificationTarget specification)
      (interpretedAtlasMapFederation target) of
    AtlasMapFederationRefuted refutation ->
      Left (AtlasMapFederationOperationRefuted refutation)
    AtlasMapFederationUndecidable uncertainty ->
      Left (AtlasMapFederationOperationUndecidable uncertainty)
    AtlasMapFederationProved () ->
      Right
        (specifiedValue
          (evaluatedSpecificationSource specification)
          (originalSpecificationSourceSemantics source)
          target
          (evaluatedSpecificationMember specification))

decidePrimitiveSubfederation
  :: InterpretedAtlasMapFederationPrimitive
  -> InterpretedAtlasMapFederationPrimitive
  -> AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
decidePrimitiveSubfederation
    (NaturalRangeAtlasMapFederation
      (EvaluatedNaturalRange sourceRange))
    (NaturalRangeAtlasMapFederation
      (EvaluatedNaturalRange targetRange))
  | NaturalRange.naturalRangeIsSubfederationOf sourceRange targetRange =
      AtlasMapFederationProved ()
  | otherwise =
      AtlasMapFederationRefuted
        AtlasMapFederationSubfederationHasMissingMember
decidePrimitiveSubfederation
    (ValuedNaturalRangeAtlasMapFederation
      (EvaluatedValuedNaturalRange sourceRange))
    (ValuedNaturalRangeAtlasMapFederation
      (EvaluatedValuedNaturalRange targetRange))
  | ValuedNaturalRange.valuedNaturalRangeIsSubfederationOf
      sourceRange targetRange =
      AtlasMapFederationProved ()
  | otherwise =
      AtlasMapFederationRefuted
        AtlasMapFederationSubfederationHasMissingMember
decidePrimitiveSubfederation _ _ =
  AtlasMapFederationRefuted
    AtlasMapFederationSubfederationHasMissingMember

specifiedValue
  :: InterpretedTotalAtlasMap
  -> ValueSemantics
  -> InterpretedValue
  -> EvaluatedAtlasMapFederationMember
  -> InterpretedValue
specifiedValue totalSource sourceCanonical target member =
  makeInterpretedValue
    (SpecificationForm
      EvaluatedSpecification
        { evaluatedSpecificationSource = totalSource
        , evaluatedSpecificationTarget = interpretedAtlasMapFederation target
        , evaluatedSpecificationMember = member
        })
    NoInsertion
    (interpretedTotalAtlasMapUnderlying totalSource)
    (interpretedAtlasMapFederation target)
    NonTotalInterpretedMap
    (SpecificationSemantics sourceCanonical (interpretedSemantics target))

originalSpecificationSourceSemantics :: InterpretedValue -> ValueSemantics
originalSpecificationSourceSemantics value =
  case interpretedSemantics value of
    SpecificationSemantics source _ -> source
    semantics -> semantics

selectNaturalRangeMember
  :: NaturalRange.NaturalRange rangeScope federationScope
  -> NaturalRange.NaturalSubrangeDescription
  -> Maybe NaturalRange.NaturalSubrangeDescription
selectNaturalRangeMember targetRange candidate =
  case candidate of
    NaturalRange.EmptyNaturalSubrange -> Just candidate
    NaturalRange.FiniteNaturalSubrange start final ->
      NaturalRange.naturalSubrangeDescription
        <$> NaturalRange.naturalRangeFiniteSubrange
              targetRange start final
    NaturalRange.UpwardsNaturalSubrange start ->
      NaturalRange.naturalSubrangeDescription
        <$> NaturalRange.naturalRangeUpwardsSubrange targetRange start

sourceEllipsisNatural :: InterpretedValue -> Maybe Natural
sourceEllipsisNatural value =
  case interpretedForm value of
    ExplicitForm explicitValue ->
      let (level, ordinalValue) = explicitOrdinal explicitValue
      in if level == 1 then naturalAtOrdinal ordinalValue else Nothing
    _ -> Nothing

selectValuedNaturalRangeMember
  :: ValuedNaturalRange.ValuedNaturalRange rangeScope federationScope
  -> Natural
  -> Maybe Natural
selectValuedNaturalRangeMember targetRange candidate =
  candidate
    <$ ValuedNaturalRange.valuedNaturalRangeValue targetRange candidate

sourceNaturalSubrange
  :: InterpretedValue
  -> Maybe NaturalRange.NaturalSubrangeDescription
sourceNaturalSubrange value =
  case interpretedForm value of
    RangeForm valueRange -> rangeSubrange valueRange
    MapForm
      | interpretedMapPageCardinality (interpretedMap value) == 0 ->
          Just NaturalRange.EmptyNaturalSubrange
      | interpretedMapPageCardinality (interpretedMap value) == 2 ->
          mapSubrange value
      | otherwise -> Nothing
    _ -> Nothing

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
