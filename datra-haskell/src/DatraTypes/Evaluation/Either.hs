-- | Disjoint federation composition for Datra's surface @|@ operator.
module Evaluation.Either
  ( makeEitherValue
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (PrimitiveAtlasMapFederation) )
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import Evaluation.Error
  ( InterpretingError (EitherAlternativesNotDistinct) )
import Evaluation.Specification.Composition (selectFederationMember)
import Evaluation.Specification.Decision (Decision (..))
import Evaluation.Specification.String (federationProducesStrings)
import Evaluation.Value
import Evaluation.Federation.Structure (sequenceOperands)
import ValuedIntegerRange qualified
import ValuedNaturalRange qualified

-- | Build the union only when every alternative is provably a distinct Atlas
-- map family. Boolean injection tags record selection after this proof; they
-- do not make overlapping members distinct.
makeEitherValue
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
makeEitherValue left right =
  if alternativesArePairwiseDistinct (NonEmpty.toList members)
    then Right (buildEither members)
    else Left EitherAlternativesNotDistinct
  where
    members = eitherMembers left <> eitherMembers right

alternativesArePairwiseDistinct :: [InterpretedValue] -> Bool
alternativesArePairwiseDistinct [] = True
alternativesArePairwiseDistinct (member : remaining) =
  all (alternativesAreDistinct member) remaining
    && alternativesArePairwiseDistinct remaining

alternativesAreDistinct :: InterpretedValue -> InterpretedValue -> Bool
alternativesAreDistinct left right
  | interpretedCanonicalResult left == interpretedCanonicalResult right = False
  | ArgumentMapForm _ underlying <- interpretedForm left =
      alternativesAreDistinct underlying right
  | ArgumentMapForm _ underlying <- interpretedForm right =
      alternativesAreDistinct left underlying
  | AssignmentForm leftAssignment <- interpretedForm left =
      alternativesAreDistinct
        (evaluatedSpecificationTarget leftAssignment)
        right
  | AssignmentForm rightAssignment <- interpretedForm right =
      alternativesAreDistinct
        left
        (evaluatedSpecificationTarget rightAssignment)
  | SpecificationForm leftSpecification <- interpretedForm left =
      alternativesAreDistinct
        (evaluatedSpecificationTarget leftSpecification)
        right
  | SpecificationForm rightSpecification <- interpretedForm right =
      alternativesAreDistinct
        left
        (evaluatedSpecificationTarget rightSpecification)
  | IdentifierTypeForm leftIdentifier <- interpretedForm left
  , IdentifierTypeForm rightIdentifier <- interpretedForm right =
      identifierAlternativesAreDistinct leftIdentifier rightIdentifier
  | IdentifierTypeForm _ <- interpretedForm left = True
  | IdentifierTypeForm _ <- interpretedForm right = True
  | EitherForm leftEither <- interpretedForm left =
      alternativesAreDistinct (evaluatedEitherLeft leftEither) right
        && alternativesAreDistinct (evaluatedEitherRight leftEither) right
  | EitherForm rightEither <- interpretedForm right =
      alternativesAreDistinct left (evaluatedEitherLeft rightEither)
        && alternativesAreDistinct left (evaluatedEitherRight rightEither)
  | Just leftMembers <- sequenceOperands left
  , Just rightMembers <- sequenceOperands right =
      length leftMembers /= length rightMembers
        || or (zipWith alternativesAreDistinct leftMembers rightMembers)
  | interpretedValueHasTotalMap left = memberIsRefuted left right
  | interpretedValueHasTotalMap right = memberIsRefuted right left
  | federationProducesStrings (interpretedAtlasMapFederation left)
  , isNumericalRange right = True
  | isNumericalRange left
  , federationProducesStrings (interpretedAtlasMapFederation right) = True
  | otherwise = rangeAlternativesAreDistinct left right

isNumericalRange :: InterpretedValue -> Bool
isNumericalRange value =
  case interpretedForm value of
    NaturalRangeForm _ -> True
    ValuedNaturalRangeForm _ -> True
    IntegerRangeForm _ -> True
    ValuedIntegerRangeForm _ -> True
    _ -> False

identifierAlternativesAreDistinct
  :: EvaluatedIdentifierType
  -> EvaluatedIdentifierType
  -> Bool
identifierAlternativesAreDistinct left right
  | not
      (identifierDependenciesCompatible
        (evaluatedIdentifierDependency left)
        (evaluatedIdentifierDependency right)) = True
  | otherwise =
      alternativesAreDistinct
        (evaluatedIdentifierUnderlying left)
        (evaluatedIdentifierUnderlying right)

memberIsRefuted :: InterpretedValue -> InterpretedValue -> Bool
memberIsRefuted member federation =
  case selectFederationMember member federation of
    DecisionRefuted -> True
    DecisionProved _ -> False
    DecisionUndecidable -> False

rangeAlternativesAreDistinct
  :: InterpretedValue
  -> InterpretedValue
  -> Bool
rangeAlternativesAreDistinct left right =
  case (interpretedForm left, interpretedForm right) of
    ( ValuedNaturalRangeForm (EvaluatedValuedNaturalRange leftRange)
      , ValuedNaturalRangeForm (EvaluatedValuedNaturalRange rightRange)
      ) ->
        noOverlap
          (ValuedNaturalRange.valuedNaturalRangesOverlapWitness
            leftRange rightRange)
    ( NaturalRangeForm (EvaluatedNaturalRange naturalRange)
      , ValuedNaturalRangeForm (EvaluatedValuedNaturalRange valuedRange)
      ) ->
        noOverlap
          (ValuedNaturalRange.valuedNaturalRangeOverlapNaturalRange
            valuedRange naturalRange)
    ( ValuedNaturalRangeForm (EvaluatedValuedNaturalRange valuedRange)
      , NaturalRangeForm (EvaluatedNaturalRange naturalRange)
      ) ->
        noOverlap
          (ValuedNaturalRange.valuedNaturalRangeOverlapNaturalRange
            valuedRange naturalRange)
    ( ValuedIntegerRangeForm (EvaluatedValuedIntegerRange leftRange)
      , ValuedIntegerRangeForm (EvaluatedValuedIntegerRange rightRange)
      ) ->
        noOverlap
          (ValuedIntegerRange.valuedIntegerRangesOverlapWitness
            leftRange rightRange)
    ( IntegerRangeForm (EvaluatedIntegerRange integerRange)
      , ValuedIntegerRangeForm (EvaluatedValuedIntegerRange valuedRange)
      ) ->
        noOverlap
          (ValuedIntegerRange.valuedIntegerRangeOverlapIntegerRange
            valuedRange integerRange)
    ( ValuedIntegerRangeForm (EvaluatedValuedIntegerRange valuedRange)
      , IntegerRangeForm (EvaluatedIntegerRange integerRange)
      ) ->
        noOverlap
          (ValuedIntegerRange.valuedIntegerRangeOverlapIntegerRange
            valuedRange integerRange)
    -- Two ordinary range federations always share their empty Atlas member.
    (NaturalRangeForm _, NaturalRangeForm _) -> False
    (IntegerRangeForm _, IntegerRangeForm _) -> False
    _ -> False
  where
    noOverlap Nothing = True
    noOverlap (Just _) = False

eitherMembers :: InterpretedValue -> NonEmpty InterpretedValue
eitherMembers value =
  case interpretedForm value of
    EitherForm alternatives ->
      eitherMembers (evaluatedEitherLeft alternatives)
        <> eitherMembers (evaluatedEitherRight alternatives)
    _ -> value :| []

buildEither :: NonEmpty InterpretedValue -> InterpretedValue
buildEither (member :| []) = member
buildEither (member :| next : remaining) =
  rawEither member (buildEither (next :| remaining))

rawEither :: InterpretedValue -> InterpretedValue -> InterpretedValue
rawEither left right =
  makeInterpretedValue
    (EitherForm alternatives)
    NoInsertion
    emptyInterpretedMap
    (PrimitiveAtlasMapFederation
      (EitherAtlasMapFederation alternatives))
    NonTotalInterpretedMap
    (EitherSemantics
      (interpretedSemantics left)
      (interpretedSemantics right))
  where
    alternatives = EvaluatedEither left right
