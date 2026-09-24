-- | Shared decision procedures for evaluated Atlas-map federations.
module Evaluation.Federation
  ( decideFederationConcatenation
  , decidePrimitiveSubfederation
  , requireFederationDecision
  , undecidableFederationOperation
  , selectNaturalRangeMember
  , selectValuedNaturalRangeMember
  , selectIntegerRangeMember
  , selectValuedIntegerRangeMember
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationDecision (..)
  , AtlasMapFederationExpression (..)
  , atlasMapFederationExpressionIsSingleton
  )
import Evaluation.Error
import Evaluation.ToString
  ( stringFederationConcatenationIsInjective )
import Evaluation.Value
import NaturalRange qualified
import IntegerRange qualified
import Numeric.Natural (Natural)
import ValuedNaturalRange qualified
import ValuedIntegerRange qualified
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
  | stringFederationConcatenationIsInjective left right =
      AtlasMapFederationProved ()
decideFederationConcatenation
    (PrimitiveAtlasMapFederation (EitherAtlasMapFederation _)) _ =
  AtlasMapFederationProved ()
decideFederationConcatenation _
    (PrimitiveAtlasMapFederation (EitherAtlasMapFederation _)) =
  AtlasMapFederationProved ()
-- Reassociation preserves already checked concatenations. Check the new
-- operand against both components instead of treating the retained tree as
-- an unknown primitive federation.
decideFederationConcatenation left
    (ConcatenatedAtlasMapFederation first second) =
  case decideFederationConcatenation left first of
    AtlasMapFederationProved () -> decideFederationConcatenation left second
    rejection -> rejection
decideFederationConcatenation
    (ConcatenatedAtlasMapFederation first second) right =
  case decideFederationConcatenation first right of
    AtlasMapFederationProved () -> decideFederationConcatenation second right
    rejection -> rejection
-- Distinct identifier families occupy disjoint named positions. This also
-- makes a sequence's canonical comma spelling interpretable when nested.
decideFederationConcatenation
    (PrimitiveAtlasMapFederation (DependentIdentifierTypeAtlasMapFederation left))
    (PrimitiveAtlasMapFederation (DependentIdentifierTypeAtlasMapFederation right))
  | not (identifierDependenciesCompatible
      (evaluatedIdentifierDependency left)
      (evaluatedIdentifierDependency right)) = AtlasMapFederationProved ()
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
      (IntegerRangeAtlasMapFederation
        (EvaluatedIntegerRange leftRange)))
    (PrimitiveAtlasMapFederation
      (IntegerRangeAtlasMapFederation
        (EvaluatedIntegerRange rightRange))) =
  integerOverlapDecision
    (IntegerRange.integerRangeOverlapWitness leftRange rightRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (ValuedIntegerRangeAtlasMapFederation
        (EvaluatedValuedIntegerRange leftRange)))
    (PrimitiveAtlasMapFederation
      (ValuedIntegerRangeAtlasMapFederation
        (EvaluatedValuedIntegerRange rightRange))) =
  integerOverlapDecision
    (ValuedIntegerRange.valuedIntegerRangesOverlapWitness
      leftRange rightRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (IntegerRangeAtlasMapFederation
        (EvaluatedIntegerRange integerRange)))
    (PrimitiveAtlasMapFederation
      (ValuedIntegerRangeAtlasMapFederation
        (EvaluatedValuedIntegerRange valuedRange))) =
  integerOverlapDecision
    (ValuedIntegerRange.valuedIntegerRangeOverlapIntegerRange
      valuedRange integerRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (ValuedIntegerRangeAtlasMapFederation
        (EvaluatedValuedIntegerRange valuedRange)))
    (PrimitiveAtlasMapFederation
      (IntegerRangeAtlasMapFederation
        (EvaluatedIntegerRange integerRange))) =
  integerOverlapDecision
    (ValuedIntegerRange.valuedIntegerRangeOverlapIntegerRange
      valuedRange integerRange)
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
    StringTypeAtlasMapFederation
    StringTypeAtlasMapFederation =
  AtlasMapFederationProved ()
decidePrimitiveSubfederation
    IdentifierValueTypeAtlasMapFederation
    IdentifierValueTypeAtlasMapFederation =
  AtlasMapFederationProved ()
decidePrimitiveSubfederation
    (NaturalRangeAtlasMapFederation
      (EvaluatedNaturalRange sourceRange))
    (NaturalRangeAtlasMapFederation
      (EvaluatedNaturalRange targetRange))
  | NaturalRange.naturalRangeIsSubfederationOf sourceRange targetRange =
      AtlasMapFederationProved ()
  | otherwise = missingMember
decidePrimitiveSubfederation
    (IntegerRangeAtlasMapFederation
      (EvaluatedIntegerRange sourceRange))
    (IntegerRangeAtlasMapFederation
      (EvaluatedIntegerRange targetRange))
  | IntegerRange.integerRangeIsSubfederationOf sourceRange targetRange =
      AtlasMapFederationProved ()
  | otherwise = missingMember
decidePrimitiveSubfederation
    (ValuedIntegerRangeAtlasMapFederation
      (EvaluatedValuedIntegerRange sourceRange))
    (ValuedIntegerRangeAtlasMapFederation
      (EvaluatedValuedIntegerRange targetRange))
  | ValuedIntegerRange.valuedIntegerRangeIsSubfederationOf
      sourceRange targetRange = AtlasMapFederationProved ()
  | otherwise = missingMember
decidePrimitiveSubfederation
    (ValuedNaturalRangeAtlasMapFederation
      (EvaluatedValuedNaturalRange sourceRange))
    (ValuedIntegerRangeAtlasMapFederation
      (EvaluatedValuedIntegerRange targetRange))
  | valuedNaturalContainedInInteger sourceRange targetRange =
      AtlasMapFederationProved ()
  | otherwise = missingMember
decidePrimitiveSubfederation
    (ValuedIntegerRangeAtlasMapFederation
      (EvaluatedValuedIntegerRange sourceRange))
    (ValuedNaturalRangeAtlasMapFederation
      (EvaluatedValuedNaturalRange targetRange))
  | valuedIntegerContainedInNatural sourceRange targetRange =
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
decidePrimitiveSubfederation
    (DependentIdentifierTypeAtlasMapFederation _)
    (DependentIdentifierTypeAtlasMapFederation _) =
  AtlasMapFederationUndecidable
    (NoAtlasMapFederationDecisionProcedure
      AtlasMapFederationSubfederation)
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

selectIntegerRangeMember
  :: IntegerRange.IntegerRange rangeScope federationScope
  -> IntegerRange.IntegerSubrangeDescription
  -> Maybe IntegerRange.IntegerSubrangeDescription
selectIntegerRangeMember targetRange candidate =
  case candidate of
    IntegerRange.EmptyIntegerSubrange -> Just candidate
    IntegerRange.FiniteIntegerSubrange start final ->
      IntegerRange.integerSubrangeDescription
        <$> IntegerRange.integerRangeFiniteSubrange targetRange start final
    IntegerRange.UpwardsIntegerSubrange start ->
      IntegerRange.integerSubrangeDescription
        <$> IntegerRange.integerRangeUpwardsSubrange targetRange start
    IntegerRange.DownwardsIntegerSubrange start ->
      IntegerRange.integerSubrangeDescription
        <$> IntegerRange.integerRangeDownwardsSubrange targetRange start

selectValuedIntegerRangeMember
  :: ValuedIntegerRange.ValuedIntegerRange rangeScope federationScope
  -> Integer
  -> Maybe Integer
selectValuedIntegerRangeMember targetRange candidate =
  candidate
    <$ ValuedIntegerRange.valuedIntegerRangeValue targetRange candidate

overlapDecision
  :: Maybe Natural
  -> AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
overlapDecision Nothing = AtlasMapFederationProved ()
overlapDecision (Just witness) =
  AtlasMapFederationRefuted
    (AtlasMapFederationConcatenationCollision (toInteger witness))

integerOverlapDecision
  :: Maybe Integer
  -> AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
integerOverlapDecision Nothing = AtlasMapFederationProved ()
integerOverlapDecision (Just witness) =
  AtlasMapFederationRefuted
    (AtlasMapFederationConcatenationCollision witness)

valuedNaturalContainedInInteger
  :: ValuedNaturalRange.ValuedNaturalRange sourceRange sourceFederation
  -> ValuedIntegerRange.ValuedIntegerRange targetRange targetFederation
  -> Bool
valuedNaturalContainedInInteger source target =
  case ValuedNaturalRange.valuedNaturalRangeTarget source of
    NaturalRange.FiniteNaturalTarget final ->
      contains (toInteger (ValuedNaturalRange.valuedNaturalRangeStart source))
        && contains (toInteger final)
    NaturalRange.UpwardsTarget ->
      contains (toInteger (ValuedNaturalRange.valuedNaturalRangeStart source))
        && ValuedIntegerRange.valuedIntegerRangeTarget target
          `elem` [ IntegerRange.UpwardsIntegerTarget
                 , IntegerRange.AllIntegersTarget
                 ]
  where
    contains = ValuedIntegerRange.valuedIntegerRangeContains target

valuedIntegerContainedInNatural
  :: ValuedIntegerRange.ValuedIntegerRange sourceRange sourceFederation
  -> ValuedNaturalRange.ValuedNaturalRange targetRange targetFederation
  -> Bool
valuedIntegerContainedInNatural source target =
  case ValuedIntegerRange.valuedIntegerRangeTarget source of
    IntegerRange.FiniteIntegerTarget final ->
      contains (ValuedIntegerRange.valuedIntegerRangeStart source)
        && contains final
    IntegerRange.UpwardsIntegerTarget ->
      contains (ValuedIntegerRange.valuedIntegerRangeStart source)
        && ValuedNaturalRange.valuedNaturalRangeTarget target
          == NaturalRange.UpwardsTarget
    IntegerRange.DownwardsIntegerTarget -> False
    IntegerRange.AllIntegersTarget -> False
  where
    contains value
      | value < 0 = False
      | otherwise =
          ValuedNaturalRange.valuedNaturalRangeContains
            target (fromInteger value)

missingMember
  :: AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
missingMember =
  AtlasMapFederationRefuted
    AtlasMapFederationSubfederationHasMissingMember
