-- | Compile-time decision procedure for the specification operator.
module Evaluation.Specification
  ( specifyValues
  , assignIdentifierValues
  ) where

import DatraLanguage.AST (renderAsciiStringLiteral)
import BooleanType (DatraBoolean (..))
import Evaluation.Boolean (makeBoolean)
import Evaluation.Construction (makeAsciiString)
import Evaluation.Optional (makeNothing)
import Evaluation.Error
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
  , InterpretedValueKind (MapValueKind, NaturalValueKind)
  , InterpretingError (..)
  )
import Evaluation.Specification.Composition (selectFederationMember)
import Evaluation.Identifier (simpleIdentifierTypeValue)
import Evaluation.Specification.Decision (Decision (..))
import Evaluation.Specification.String (federationUsesWeakToString)
import Evaluation.Specification.Subfederation
  ( decideValueSubfederation
  )
import Evaluation.Value

specifyValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyValues source target
  | federationUsesWeakToString (interpretedAtlasMapFederation target) =
      Left NoCanonicalStringConversion
  | interpretedCanonicalResult source == interpretedCanonicalResult target =
      Right source
  | otherwise = specifyValuesWithoutIdentity source target

specifyValuesWithoutIdentity
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyValuesWithoutIdentity source target =
  case identifierStringMismatch source target of
    Just (expected, given) ->
      Left
        (IdentifierStringMismatch
          { expectedIdentifierString = expected
          , givenIdentifierString = given
          })
    Nothing ->
      case interpretedForm source of
        SpecificationForm specification ->
          widenSpecification source specification target
        AssignmentForm specification ->
          widenSpecification source specification target
        _ -> specifyTotalAtlasMap source target

identifierStringMismatch
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe (String, String)
identifierStringMismatch source target = do
  given <- simpleIdentifierStringFromSemantics (interpretedSemantics source)
  expected <- simpleIdentifierStringFromSemantics (interpretedSemantics target)
  if given == expected
    then Nothing
    else
      Just
        ( renderAsciiStringLiteral expected
        , renderAsciiStringLiteral given
        )

simpleIdentifierStringFromSemantics :: ValueSemantics -> Maybe String
simpleIdentifierStringFromSemantics semantics =
  case semantics of
    IdentifierTypeSemantics
        (SimpleIdentifierDependency identifierString) _ _ ->
          Just identifierString
    AssignmentSemantics identifierString _ _ -> Just identifierString
    SpecificationSemantics source target -> do
      sourceString <- simpleIdentifierStringFromSemantics source
      targetString <- simpleIdentifierStringFromSemantics target
      if sourceString == targetString then Just sourceString else Nothing
    _ -> Nothing

-- | Assignment is specification between two constant-string identifier types,
-- but remains marked for canonical assignment rendering even when its source
-- and target coincide. Pointwise specifications produced by access still use
-- 'specifyValues' and therefore obey the general identity coercion.
assignIdentifierValues
  :: String
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
assignIdentifierValues identifierString typeAnnotation givenValue = do
  case distinguishedAssignment identifierString typeAnnotation givenValue of
    Just value -> Right value
    Nothing -> do
      let source = simpleIdentifierTypeValue identifierString givenValue
          target = simpleIdentifierTypeValue identifierString typeAnnotation
      specified <- specifyValuesWithoutIdentity source target
      case interpretedForm specified of
        SpecificationForm specification ->
          Right
            (makeInterpretedValue
              (AssignmentForm specification)
              NoInsertion
              (interpretedMap specified)
              (interpretedAtlasMapFederation specified)
              NonTotalInterpretedMap
              (AssignmentSemantics
                identifierString
                (interpretedSemantics typeAnnotation)
                (interpretedSemantics givenValue)))
        _ -> Right specified

-- These assignments are distinguished nullary constructors rather than
-- ordinary identifier specifications. Thus the expanded spellings of Bool
-- and optional absence are definitionally equal to their shorthand forms.
distinguishedAssignment
  :: String
  -> InterpretedValue
  -> InterpretedValue
  -> Maybe InterpretedValue
distinguishedAssignment identifierString typeAnnotation givenValue
  | interpretedCanonicalResult typeAnnotation
      /= interpretedCanonicalResult givenValue = Nothing
  | otherwise =
      case ( identifierString
           , interpretedValueKind givenValue
           , interpretedInteger givenValue
           , interpretedCanonicalResult givenValue
           ) of
        ("False", NaturalValueKind, Just 0, _) ->
          Just (makeBoolean DatraFalse)
        ("True", NaturalValueKind, Just 1, _) ->
          Just (makeBoolean DatraTrue)
        ("Nothing", MapValueKind, _, CanonicalMap 0 []) -> Just makeNothing
        (_, MapValueKind, _, CanonicalMap 0 []) ->
          Just (makeAsciiString identifierString)
        _ -> Nothing

specifyTotalAtlasMap
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyTotalAtlasMap source target = do
  (selectionSource, totalSource) <-
    case concreteOptionalAssignmentSource source of
      Just concreteSource -> Right concreteSource
      Nothing ->
        case interpretedTotalAtlasMap source of
          Just totalMap -> Right (source, totalMap)
          Nothing -> Left (ExpectedTotalAtlasMap (interpretedValueKind source))
  case selectFederationMember selectionSource target of
    DecisionProved member ->
      Right
        (specifiedValue
          source
          totalSource
          (interpretedSemantics source)
          target
          member)
    DecisionRefuted -> noMatchingMember
    DecisionUndecidable ->
      Left
        (AtlasMapFederationOperationUndecidable
          (NoAtlasMapFederationDecisionProcedure
            AtlasMapFederationSpecification))
  where
    noMatchingMember =
      Left
        (AtlasMapFederationOperationRefuted
          AtlasMapFederationSpecificationHasNoMatchingMember)

-- An optional assigned identifier is a federation union syntactically, but
-- its assignment branch retains the concrete total source that supplied the
-- value. As a specification source, it therefore selects the present branch
-- rather than being rejected merely because the surrounding Either is
-- non-total.
concreteOptionalAssignmentSource
  :: InterpretedValue
  -> Maybe (InterpretedValue, InterpretedTotalAtlasMap)
concreteOptionalAssignmentSource source = do
  alternatives <-
    case interpretedForm source of
      EitherForm value -> Just value
      _ -> Nothing
  let present = evaluatedEitherLeft alternatives
      missing = evaluatedEitherRight alternatives
  assignment <-
    case interpretedForm present of
      AssignmentForm value -> Just value
      _ -> Nothing
  case interpretedCanonicalResult present of
    CanonicalAssignment _ typeAnnotation _
      | typeAnnotation == interpretedCanonicalResult missing ->
          Just
            ( evaluatedSpecificationSourceValue assignment
            , evaluatedSpecificationSource assignment
            )
    _ -> Nothing

-- | Compose a prior specification with inclusion of its whole target
-- federation into a larger target. Checking only the previously selected
-- member would be weaker: the intermediate object itself must be an Atlas
-- subfederation of the final object.
widenSpecification
  :: InterpretedValue
  -> EvaluatedSpecification
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
widenSpecification source specification target =
  if interpretedCanonicalResult
      (evaluatedSpecificationTarget specification)
      == interpretedCanonicalResult target
    then Right source
    else
      case decideValueSubfederation
          (evaluatedSpecificationTarget specification)
          target of
        DecisionProved () ->
          Right
            (specifiedValue
              (evaluatedSpecificationSourceValue specification)
              (evaluatedSpecificationSource specification)
              (originalSpecificationSourceSemantics source)
              target
              (evaluatedSpecificationMember specification))
        DecisionRefuted ->
          Left
            (AtlasMapFederationOperationRefuted
              AtlasMapFederationSubfederationHasMissingMember)
        DecisionUndecidable ->
          Left
            (AtlasMapFederationOperationUndecidable
              (NoAtlasMapFederationDecisionProcedure
                AtlasMapFederationSubfederation))

specifiedValue
  :: InterpretedValue
  -> InterpretedTotalAtlasMap
  -> ValueSemantics
  -> InterpretedValue
  -> EvaluatedAtlasMapFederationMember
  -> InterpretedValue
specifiedValue sourceValue totalSource sourceCanonical target member =
  makeInterpretedValue
    (SpecificationForm
      EvaluatedSpecification
        { evaluatedSpecificationSourceValue = sourceValue
        , evaluatedSpecificationSource = totalSource
        , evaluatedSpecificationTarget = target
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
    AssignmentSemantics identifierString _ givenValueSemantics ->
      IdentifierTypeSemantics
        (SimpleIdentifierDependency identifierString)
        givenValueSemantics
        True
    semantics -> semantics
