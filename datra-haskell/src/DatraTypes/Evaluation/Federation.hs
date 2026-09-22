-- | Shared decision procedures for evaluated Atlas-map federations.
module Evaluation.Federation
  ( FederationAccess (..)
  , decideFederationAccess
  , naturalRangeFederation
  , decideFederationConcatenation
  , decidePrimitiveSubfederation
  , requireFederationDecision
  , undecidableFederationOperation
  , selectNaturalRangeMember
  , selectValuedNaturalRangeMember
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationDecision (..)
  , AtlasMapFederationExpression (..)
  , atlasMapFederationExpressionIsSingleton
  )
import DatraOrdinal (finiteOrdinal)
import Evaluation.Error
import Evaluation.Value
import NaturalRange qualified
import Numeric.Natural (Natural)
import ValuedNaturalRange qualified
import SuperEllipsisInsertion
  ( someSuperEllipsisInsertionOrderType
  )

data FederationAccess
  = NaturalRangeFederationAccess
      EvaluatedNaturalRange
      EvaluatedNaturalRange
  | NaturalRangeSelectionAccess EvaluatedNaturalRange
  | EmptyFederationAccess
  | SingletonFederationAccess SomeSuperEllipsisInsertion

decideFederationAccess
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError FederationAccess
decideFederationAccess mapValue insertionValue =
  case (naturalRangeFederation mapValue,
        naturalRangeFederation insertionValue) of
    (Just sourceRange, Just selectionRange) ->
      Right (NaturalRangeFederationAccess sourceRange selectionRange)
    (Nothing, Just selectionRange)
      | atlasMapFederationExpressionIsSingleton
          (interpretedAtlasMapFederation mapValue) ->
          Right (NaturalRangeSelectionAccess selectionRange)
      | otherwise ->
          undecidableFederationOperation AtlasMapFederationAccess
    (_, Nothing) -> do
      insertion <- requireInsertion insertionValue
      if someSuperEllipsisInsertionOrderType insertion == finiteOrdinal 0
        then Right EmptyFederationAccess
        else case naturalRangeFederation mapValue of
          Just _ ->
            Left
              (AtlasMapFederationOperationRefuted
                AtlasMapFederationAccessHasEmptyCounterexample)
          Nothing
            | atlasMapFederationExpressionIsSingleton
                (interpretedAtlasMapFederation mapValue) ->
                Right (SingletonFederationAccess insertion)
            | otherwise ->
                undecidableFederationOperation AtlasMapFederationAccess

naturalRangeFederation
  :: InterpretedValue
  -> Maybe EvaluatedNaturalRange
naturalRangeFederation value =
  case interpretedAtlasMapFederation value of
    PrimitiveAtlasMapFederation
        (NaturalRangeAtlasMapFederation naturalRange) ->
      Just naturalRange
    _ -> Nothing

decideFederationConcatenation
  :: InterpretedAtlasMapFederation
  -> InterpretedAtlasMapFederation
  -> AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
decideFederationConcatenation left right
  | atlasMapFederationExpressionIsSingleton left =
      AtlasMapFederationProved ()
  | atlasMapFederationExpressionIsSingleton right =
      AtlasMapFederationProved ()
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (NaturalRangeAtlasMapFederation
        (EvaluatedNaturalRange leftRange)))
    (PrimitiveAtlasMapFederation
      (NaturalRangeAtlasMapFederation
        (EvaluatedNaturalRange rightRange))) =
  overlapDecision
    (NaturalRange.naturalRangeOverlapWitness leftRange rightRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (ValuedNaturalRangeAtlasMapFederation
        (EvaluatedValuedNaturalRange leftRange)))
    (PrimitiveAtlasMapFederation
      (ValuedNaturalRangeAtlasMapFederation
        (EvaluatedValuedNaturalRange rightRange))) =
  overlapDecision
    (ValuedNaturalRange.valuedNaturalRangesOverlapWitness
      leftRange rightRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (NaturalRangeAtlasMapFederation
        (EvaluatedNaturalRange naturalRange)))
    (PrimitiveAtlasMapFederation
      (ValuedNaturalRangeAtlasMapFederation
        (EvaluatedValuedNaturalRange valuedRange))) =
  overlapDecision
    (ValuedNaturalRange.valuedNaturalRangeOverlapNaturalRange
      valuedRange naturalRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (ValuedNaturalRangeAtlasMapFederation
        (EvaluatedValuedNaturalRange valuedRange)))
    (PrimitiveAtlasMapFederation
      (NaturalRangeAtlasMapFederation
        (EvaluatedNaturalRange naturalRange))) =
  overlapDecision
    (ValuedNaturalRange.valuedNaturalRangeOverlapNaturalRange
      valuedRange naturalRange)
decideFederationConcatenation _ _ =
  AtlasMapFederationUndecidable
    (NoAtlasMapFederationDecisionProcedure
      AtlasMapFederationConcatenation)

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
  | otherwise = missingMember
decidePrimitiveSubfederation
    (ValuedNaturalRangeAtlasMapFederation
      (EvaluatedValuedNaturalRange sourceRange))
    (ValuedNaturalRangeAtlasMapFederation
      (EvaluatedValuedNaturalRange targetRange))
  | ValuedNaturalRange.valuedNaturalRangeIsSubfederationOf
      sourceRange targetRange =
      AtlasMapFederationProved ()
  | otherwise = missingMember
decidePrimitiveSubfederation _ _ = missingMember

requireFederationDecision
  :: AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
  -> Either InterpretingError ()
requireFederationDecision decision =
  case decision of
    AtlasMapFederationRefuted refutation ->
      Left (AtlasMapFederationOperationRefuted refutation)
    AtlasMapFederationUndecidable uncertainty ->
      Left (AtlasMapFederationOperationUndecidable uncertainty)
    AtlasMapFederationProved () -> Right ()

undecidableFederationOperation
  :: AtlasMapFederationOperation
  -> Either InterpretingError result
undecidableFederationOperation operation =
  Left
    (AtlasMapFederationOperationUndecidable
      (NoAtlasMapFederationDecisionProcedure operation))

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

selectValuedNaturalRangeMember
  :: ValuedNaturalRange.ValuedNaturalRange rangeScope federationScope
  -> Natural
  -> Maybe Natural
selectValuedNaturalRangeMember targetRange candidate =
  candidate
    <$ ValuedNaturalRange.valuedNaturalRangeValue targetRange candidate

requireInsertion
  :: InterpretedValue
  -> Either InterpretingError SomeSuperEllipsisInsertion
requireInsertion value =
  case interpretedInsertionCapability value of
    NoInsertion ->
      Left (ExpectedInsertionOperand (interpretedValueKind value))
    RejectedInsertion rejection ->
      Left (RangeConcatenationRejected rejection)
    ValidInsertion insertion -> Right insertion

overlapDecision
  :: Maybe Natural
  -> AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
overlapDecision Nothing = AtlasMapFederationProved ()
overlapDecision (Just witness) =
  AtlasMapFederationRefuted
    (AtlasMapFederationConcatenationCollision witness)

missingMember
  :: AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
missingMember =
  AtlasMapFederationRefuted
    AtlasMapFederationSubfederationHasMissingMember
