-- | Compile-time decision procedure for the specification operator.
module Evaluation.Specification
  ( specifyValues
  ) where

import AtlasMapFederation
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

-- | NaturalRange is special here: each of its members is an empty Atlas or a
-- chained-dominion Atlas whose final regions are singleton sets.  This fact
-- belongs to this decision procedure and is not inferred for arbitrary
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
  case targetNaturalRange target of
    Nothing ->
      Left
        (AtlasMapFederationOperationUndecidable
          (NoAtlasMapFederationDecisionProcedure
            AtlasMapFederationSpecification))
    Just (EvaluatedNaturalRange targetRange) ->
      case sourceNaturalSubrange source
          >>= selectNaturalRangeMember targetRange of
        Nothing ->
          Left
            (AtlasMapFederationOperationRefuted
              AtlasMapFederationSpecificationHasNoMatchingMember)
        Just member ->
          Right
            (specifiedValue
              totalSource
              (interpretedCanonicalResult source)
              target
              member)

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
          (originalSpecificationSource source)
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

specifiedValue
  :: InterpretedTotalAtlasMap
  -> CanonicalResult
  -> InterpretedValue
  -> NaturalRange.NaturalSubrangeDescription
  -> InterpretedValue
specifiedValue totalSource sourceCanonical target member =
  InterpretedValue
    { interpretedForm =
        SpecificationForm
          EvaluatedSpecification
            { evaluatedSpecificationSource = totalSource
            , evaluatedSpecificationTarget =
                interpretedAtlasMapFederation target
            , evaluatedSpecificationMember = member
            }
    , interpretedInsertionCapability = NoInsertion
    , interpretedMap = interpretedTotalAtlasMapUnderlying totalSource
    , interpretedAtlasMapFederation =
        interpretedAtlasMapFederation target
    , interpretedTotalAtlasMap = Nothing
    , interpretedCanonicalResult =
        CanonicalSpecification
          sourceCanonical
          (interpretedCanonicalResult target)
    }

originalSpecificationSource :: InterpretedValue -> CanonicalResult
originalSpecificationSource value =
  case interpretedCanonicalResult value of
    CanonicalSpecification source _ -> source
    canonical -> canonical

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

targetNaturalRange
  :: InterpretedValue
  -> Maybe EvaluatedNaturalRange
targetNaturalRange value =
  case interpretedAtlasMapFederation value of
    PrimitiveAtlasMapFederation
        (NaturalRangeAtlasMapFederation naturalRange) ->
      Just naturalRange
    _ -> Nothing

sourceNaturalSubrange
  :: InterpretedValue
  -> Maybe NaturalRange.NaturalSubrangeDescription
sourceNaturalSubrange value =
  case interpretedForm value of
    RangeForm valueRange -> rangeSubrange valueRange
    MapForm
      | interpretedMapCardinality (interpretedMap value) == 0 ->
          Just NaturalRange.EmptyNaturalSubrange
      | interpretedMapCardinality (interpretedMap value) == 2 ->
          mapSubrange value
      | otherwise -> Nothing
    _ -> Nothing

mapSubrange
  :: InterpretedValue
  -> Maybe NaturalRange.NaturalSubrangeDescription
mapSubrange value =
  case interpretedCanonicalResult value of
    CanonicalMap _ [CanonicalRange description] ->
      describedRangeSubrange 1 description
    CanonicalMap _ [CanonicalExplicit level ordinalValue] -> do
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
