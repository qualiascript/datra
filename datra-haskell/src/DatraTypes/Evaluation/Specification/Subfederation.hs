-- | Central dispatch for inclusion between evaluated Datra types.
module Evaluation.Specification.Subfederation
  ( decideValueSubfederation
  , IdentifierNameDisjointness (..)
  , identifierNameDisjointness
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (..)
  )
import Evaluation.Construction (makeAsciiString)
import Evaluation.Error (InterpretingError (..))
import Evaluation.Specification.Decision
import Evaluation.TypeFamily
  ( TypeFamilyOperations (decideTypeFamilySubfederation)
  , typeFamilyOperations
  )
import Evaluation.Value

-- | Whether one literal identifier name can occur anywhere in an evaluated
-- identifier family. Generic-scope validation deliberately distinguishes an
-- undecidable family from a proven-disjoint one: failing to find one witness
-- is not a proof that moving a generic into the domain prefix is safe.
data IdentifierNameDisjointness
  = IdentifierNameDisjoint
  | IdentifierNameOverlap
  | IdentifierNameDisjointnessUndecidable
  deriving (Eq, Show)

identifierNameDisjointness
  :: String
  -> InterpretedValue
  -> IdentifierNameDisjointness
identifierNameDisjointness candidate value =
  case interpretedForm value of
    DependentIdentifierTypeForm identifier -> againstIdentifier identifier
    IdentifierStringProjectionForm identifier -> againstIdentifier identifier
    SpecificationForm specification ->
      identifierNameDisjointness candidate
        (evaluatedSpecificationTarget specification)
    AssignmentForm specification ->
      identifierNameDisjointness candidate
        (evaluatedSpecificationTarget specification)
    _ -> IdentifierNameDisjointnessUndecidable
  where
    againstIdentifier identifier =
      case evaluatedIdentifierDependency identifier of
        SimpleIdentifierDependency name
          | name == candidate -> IdentifierNameOverlap
          | otherwise -> IdentifierNameDisjoint
        dependency@DependentIdentifierDependency {} ->
          case evaluatedIdentifierNameFederation identifier of
            Just names -> fromDecision
              (decideValueSubfederation (makeAsciiString candidate) names)
            Nothing
              | interpretedValueHasTotalMap underlying ->
                  if identifierDependencyStringFor dependency
                      (interpretedSemanticResult underlying) == candidate
                    then IdentifierNameOverlap
                    else IdentifierNameDisjoint
              | otherwise -> IdentifierNameDisjointnessUndecidable
          where
            underlying = evaluatedIdentifierUnderlying identifier
    fromDecision decision =
      case decision of
        DecisionProved () -> IdentifierNameOverlap
        DecisionRefuted -> IdentifierNameDisjoint
        DecisionUndecidable -> IdentifierNameDisjointnessUndecidable

decideValueSubfederation
  :: InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideValueSubfederation source target
  | productFederationFormsConflict source target = DecisionRefuted
  | Just _ <- interpretedFunction source
  , Just _ <- interpretedFunction target =
      decideTypeFamilySubfederation
        (typeFamilyOperations
          (datraTypeFamily (interpretedDatraType target)))
        decideValueSubfederation
        source
        target
  | interpretedSemanticResult source == interpretedSemanticResult target =
      DecisionProved ()
  | DependentSumForm sourceDependent <- interpretedForm source
  , DependentSumForm targetDependent <- interpretedForm target
  , ListDependentSum sourceElement <-
      evaluatedDependentSumStructure sourceDependent
  , ListDependentSum targetElement <-
      evaluatedDependentSumStructure targetDependent =
      decideValueSubfederation sourceElement targetElement
  | DependentSumForm dependent <- interpretedForm target =
      case evaluatedDependentSumSpecify dependent source of
        Right _ -> DecisionProved ()
        Left (AtlasMapFederationOperationUndecidable _) ->
          DecisionUndecidable
        Left _ -> DecisionRefuted
  | EitherForm alternatives <- interpretedForm target
  , eitherContainsDependentSum alternatives =
      decideAny
        [ decideValueSubfederation source alternative
        | alternative <- flattenEither target
        ]
  | EitherForm alternatives <- interpretedForm source
  , isFunctionFamily source =
      decideAllEitherAlternatives alternatives target
  | EitherForm alternatives <- interpretedForm target
  , isFunctionFamily target =
      decideAnyEitherAlternative source alternatives
  | otherwise =
      decideTypeFamilySubfederation
        (typeFamilyOperations
          (datraTypeFamily (interpretedDatraType target)))
        decideValueSubfederation
        source
        target

-- Sequential products retain their Atlas-map positions. Concatenation joins
-- federations without introducing those positions, so equal final values do
-- not make the two structures mutually inclusive.
productFederationFormsConflict
  :: InterpretedValue
  -> InterpretedValue
  -> Bool
productFederationFormsConflict left right =
  case
      ( interpretedAtlasMapFederation left
      , interpretedAtlasMapFederation right
      ) of
    (SequentialAtlasMapFederation _, ConcatenatedAtlasMapFederation _ _) ->
      True
    (ConcatenatedAtlasMapFederation _ _, SequentialAtlasMapFederation _) ->
      True
    _ -> False

eitherContainsDependentSum :: EvaluatedEither -> Bool
eitherContainsDependentSum alternatives =
  any isDependentSum
    (flattenEither (evaluatedEitherLeft alternatives)
      <> flattenEither (evaluatedEitherRight alternatives))
  where
    isDependentSum value =
      case interpretedForm value of
        DependentSumForm _ -> True
        _ -> False

flattenEither :: InterpretedValue -> [InterpretedValue]
flattenEither value =
  case interpretedForm value of
    EitherForm alternatives ->
      flattenEither (evaluatedEitherLeft alternatives)
        <> flattenEither (evaluatedEitherRight alternatives)
    _ -> [value]

-- Function alternatives are handled before family dispatch because the
-- enclosing Either is structural while every member has function behavior.
decideAllEitherAlternatives
  :: EvaluatedEither
  -> InterpretedValue
  -> Decision ()
decideAllEitherAlternatives source target =
  mapDecision
    (const ())
    (decideAll
      [ decideValueSubfederation (evaluatedEitherLeft source) target
      , decideValueSubfederation (evaluatedEitherRight source) target
      ])

decideAnyEitherAlternative
  :: InterpretedValue
  -> EvaluatedEither
  -> Decision ()
decideAnyEitherAlternative source target =
  decideAny
    [ decideValueSubfederation source (evaluatedEitherLeft target)
    , decideValueSubfederation source (evaluatedEitherRight target)
    ]
