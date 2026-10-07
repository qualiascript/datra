-- | Disjoint federation composition for Datra's surface @|@ operator.
module Evaluation.Either
  ( makeEitherValue
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (PrimitiveAtlasMapFederation) )
import Data.List (nubBy)
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import DatraLanguage.SyntaxTemplate
  ( FunctionSyntax (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  )
import DatraOrdinal (Ordinal, finiteOrdinal)
import Evaluation.Coalization (valueIsCoalition)
import Evaluation.Error
  ( InterpretingError (EitherAlternativesNotDistinct) )
import Evaluation.Specification.Composition (selectFederationMember)
import Evaluation.Specification.Decision (Decision (..))
import Evaluation.Specification.String (valueProducesStrings)
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
    members = case nubBy identicalLoweredSyntaxFunction
        (NonEmpty.toList (eitherMembers left <> eitherMembers right)) of
      first : remaining -> first :| remaining
      [] -> left :| []

identicalLoweredSyntaxFunction :: InterpretedValue -> InterpretedValue -> Bool
identicalLoweredSyntaxFunction left right =
  case (interpretedFunction left, interpretedFunction right) of
    (Just leftFunction, Just rightFunction) ->
      case ( functionSyntax leftFunction
           , functionSyntax rightFunction
           ) of
        (Just leftSyntax, Just rightSyntax) ->
          functionSyntaxEquivalent leftSyntax rightSyntax
            && interpretedSemanticResult left
              == interpretedSemanticResult right
        _ -> False
    _ -> False

alternativesArePairwiseDistinct :: [InterpretedValue] -> Bool
alternativesArePairwiseDistinct [] = True
alternativesArePairwiseDistinct (member : remaining) =
  all (alternativesAreDistinct member) remaining
    && alternativesArePairwiseDistinct remaining

alternativesAreDistinct :: InterpretedValue -> InterpretedValue -> Bool
alternativesAreDistinct left right
  | Just leftFunction <- interpretedFunction left
  , Just rightFunction <- interpretedFunction right
  , Just leftSyntax <- functionSyntax leftFunction
  , Just rightSyntax <- functionSyntax rightFunction =
      case decideSyntaxFunctionAlternatives
          leftFunction leftSyntax rightFunction rightSyntax of
        DecisionProved () -> True
        DecisionRefuted -> False
        DecisionUndecidable -> False
  | interpretedSemanticResult left == interpretedSemanticResult right = False
  | Just a <- interpretedFunction left, Just b <- interpretedFunction right =
      alternativesAreDistinct (functionDomain a) (functionDomain b)
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
  | DependentIdentifierTypeForm leftIdentifier <- interpretedForm left
  , DependentIdentifierTypeForm rightIdentifier <- interpretedForm right =
      identifierAlternativesAreDistinct leftIdentifier rightIdentifier
  | DependentIdentifierTypeForm _ <- interpretedForm left = True
  | DependentIdentifierTypeForm _ <- interpretedForm right = True
  | Just leftSlots <- structuralSlotOrdinal left
  , Just rightSlots <- structuralSlotOrdinal right
  , leftSlots /= rightSlots = True
  | ArgumentMapForm leftMembers _ <- interpretedForm left
  , ArgumentMapForm rightMembers _ <- interpretedForm right =
      length leftMembers /= length rightMembers
        || or (zipWith alternativesAreDistinct leftMembers rightMembers)
  | ArgumentMapForm _ _ <- interpretedForm left
  , BuiltinMetaTypeForm (ASTMetaType _) <- interpretedForm right = True
  | BuiltinMetaTypeForm (ASTMetaType _) <- interpretedForm left
  , ArgumentMapForm _ _ <- interpretedForm right = True
  | ArgumentMapForm _ underlying <- interpretedForm left =
      alternativesAreDistinct underlying right
  | ArgumentMapForm _ underlying <- interpretedForm right =
      alternativesAreDistinct left underlying
  | BuiltinMetaTypeForm OrdinalMetaType <- interpretedForm left
  , ValuedNaturalRangeForm _ <- interpretedForm right = True
  | ValuedNaturalRangeForm _ <- interpretedForm left
  , BuiltinMetaTypeForm OrdinalMetaType <- interpretedForm right = True
  | EitherForm leftEither <- interpretedForm left =
      alternativesAreDistinct (evaluatedEitherLeft leftEither) right
        && alternativesAreDistinct (evaluatedEitherRight leftEither) right
  | EitherForm rightEither <- interpretedForm right =
      alternativesAreDistinct left (evaluatedEitherLeft rightEither)
        && alternativesAreDistinct left (evaluatedEitherRight rightEither)
  | DependentSumForm dependent <- interpretedForm right
  , interpretedValueHasTotalMap left =
      dependentMemberIsRefuted dependent left
  | DependentSumForm dependent <- interpretedForm left
  , interpretedValueHasTotalMap right =
      dependentMemberIsRefuted dependent right
  | Just _ <- interpretedFunction left = True
  | Just _ <- interpretedFunction right = True
  | Just leftMembers <- sequenceOperands left
  , Just rightMembers <- sequenceOperands right =
      length leftMembers /= length rightMembers
        || or (zipWith alternativesAreDistinct leftMembers rightMembers)
  | interpretedValueHasTotalMap right
  , sequenceRequiresMultipleSources left = True
  | interpretedValueHasTotalMap left
  , sequenceRequiresMultipleSources right = True
  | interpretedValueHasTotalMap left = memberIsRefuted left right
  | interpretedValueHasTotalMap right = memberIsRefuted right left
  | valueProducesStrings left
  , isNumericalRange right = True
  | isNumericalRange left
  , valueProducesStrings right = True
  | otherwise = rangeAlternativesAreDistinct left right

-- Declaration order makes structurally different templates deterministic for
-- the declared spelling. Ordinary application is always available, so the
-- domains must independently be disjoint as well.
decideSyntaxFunctionAlternatives
  :: EvaluatedFunction
  -> FunctionSyntax InterpretedValue
  -> EvaluatedFunction
  -> FunctionSyntax InterpretedValue
  -> Decision ()
decideSyntaxFunctionAlternatives
    leftFunction leftSyntax rightFunction rightSyntax
  | ordinaryRoutesIdentical = DecisionRefuted
  | not syntaxRoutesDistinct =
      if functionSyntaxEquivalent leftSyntax rightSyntax
        then DecisionRefuted
        else DecisionUndecidable
  | ordinaryRoutesNotProvedDistinct = DecisionUndecidable
  | otherwise = DecisionProved ()
  where
    syntaxRoutesDistinct = and
      [ templatePriority leftTemplate /= templatePriority rightTemplate
          || alignedLiteralsConflict leftTemplate rightTemplate
          || alternativesAreDistinct
            (functionDomain leftFunction)
            (functionDomain rightFunction)
      | leftTemplate <- functionSyntaxTemplates leftSyntax
      , rightTemplate <- functionSyntaxTemplates rightSyntax
      ]
    ordinaryRoutesIdentical =
      interpretedSemanticResult (functionDomain leftFunction)
        == interpretedSemanticResult (functionDomain rightFunction)
    ordinaryRoutesNotProvedDistinct = not (alternativesAreDistinct
      (functionDomain leftFunction)
      (functionDomain rightFunction))

templatePriority :: SyntaxTemplate value -> Int
templatePriority (SyntaxTemplate pieces) = length pieces

alignedLiteralsConflict
  :: SyntaxTemplate left
  -> SyntaxTemplate right
  -> Bool
alignedLiteralsConflict
    (SyntaxTemplate leftPieces) (SyntaxTemplate rightPieces) =
  length leftPieces == length rightPieces
    && or (zipWith conflicts leftPieces rightPieces)
  where
    conflicts
        (SyntaxLiteral leftLiteral) (SyntaxLiteral rightLiteral) =
      leftLiteral /= rightLiteral
    conflicts _ _ = False

-- Literal unit components are neutral in a sequence. An atomic total value
-- still supplies one structural component, so it cannot overlap a sequence
-- with two or more non-unit components. Use literal structure here rather
-- than asking whether @()@ subtypes a component: the empty map also denotes
-- numerical zero, but that does not erase a Nat slot's map cardinality.
sequenceRequiresMultipleSources :: InterpretedValue -> Bool
sequenceRequiresMultipleSources value =
  case sequenceOperands value of
    Nothing -> False
    Just members -> length (filter (not . isLiteralUnit) members) > 1
  where
    isLiteralUnit member =
      interpretedSemanticResult member == CanonicalMap 0 []

structuralSlotOrdinal :: InterpretedValue -> Maybe Ordinal
structuralSlotOrdinal value
  | valueIsCoalition value = Just (finiteOrdinal 1)
  | otherwise = case interpretedForm value of
      SequentialMapForm -> Just (finiteOrdinal
        (interpretedMapPageCardinality (interpretedMap value)))
      MapForm -> Just (finiteOrdinal
        (interpretedMapPageCardinality (interpretedMap value)))
      ConcatenatedMapForm _ _ -> Just (finiteOrdinal
        (interpretedMapPageCardinality (interpretedMap value)))
      ExpansionMapForm _ _ -> Just (finiteOrdinal
        (interpretedMapPageCardinality (interpretedMap value)))
      ArgumentMapForm members _ ->
        Just (finiteOrdinal (fromIntegral (length members)))
      _ -> Just (finiteOrdinal 1)

isNumericalRange :: InterpretedValue -> Bool
isNumericalRange value =
  case interpretedForm value of
    NaturalRangeForm _ -> True
    ValuedNaturalRangeForm _ -> True
    IntegerRangeForm _ -> True
    ValuedIntegerRangeForm _ -> True
    RangeForm _ -> True
    RangeConcatenationForm _ _ -> True
    _ -> False

identifierAlternativesAreDistinct
  :: EvaluatedDependentIdentifierType
  -> EvaluatedDependentIdentifierType
  -> Bool
identifierAlternativesAreDistinct left right
  | SimpleIdentifierDependency leftName <- evaluatedIdentifierDependency left
  , SimpleIdentifierDependency rightName <- evaluatedIdentifierDependency right
  , leftName /= rightName = True
  | not
      (identifierDependenciesCompatible
        (evaluatedIdentifierDependency left)
        (evaluatedIdentifierDependency right)) = False
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

dependentMemberIsRefuted
  :: EvaluatedDependentSum
  -> InterpretedValue
  -> Bool
dependentMemberIsRefuted dependent member =
  case evaluatedDependentSumSpecify dependent member of
    Left _ -> True
    Right _ -> False

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
    (composedStructuralDatraType
      (map interpretedDatraType [left, right]))
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
