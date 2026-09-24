-- | Specification and assignment rules owned by structural Datra types.
module Evaluation.TypeFamily.Structural.Specification
  ( assignIdentifierValues
  , specifyStructural
  ) where

import BooleanType (DatraBoolean (..))
import DatraLanguage.AST (renderAsciiStringLiteral)
import Evaluation.Arguments (argumentAlternatives)
import Evaluation.Construction (makeAsciiString)
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
  , FunctionFailure (ExpectedFunctionType)
  )
import Evaluation.Identifier (simpleIdentifierTypeValue)
import Evaluation.Map (concatenateValues)
import Evaluation.Optional (makeNothing)
import Evaluation.Specification.Composition (selectFederationMember)
import Evaluation.Specification.Decision
import Evaluation.Specification.String (federationUsesWeakToString)
import Evaluation.Value

type Specifier =
  InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue

type SubfederationDecider =
  InterpretedValue -> InterpretedValue -> Decision ()

specifyStructural
  :: Specifier
  -> SubfederationDecider
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyStructural specify decideSubfederation source target
  | Just _ <- interpretedFunction source =
      Left (FunctionEvaluationFailed ExpectedFunctionType)
  | federationUsesWeakToString (interpretedAtlasMapFederation target) =
      Left NoCanonicalStringConversion
  | interpretedCanonicalResult source == interpretedCanonicalResult target =
      Right source
  | otherwise =
      specifyValuesWithoutIdentity
        specify decideSubfederation source target

specifyValuesWithoutIdentity
  :: Specifier
  -> SubfederationDecider
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyValuesWithoutIdentity specify decideSubfederation source target =
  case identifierStringMismatch source target of
    Just (expected, given) ->
      Left
        (IdentifierStringMismatch
          { expectedIdentifierString = expected
          , givenIdentifierString = given
          })
    Nothing ->
      case interpretedForm source of
        ArgumentMapForm _ underlying ->
          specifyFamily specify source (argumentAlternatives underlying) target
        EitherForm _
          | Nothing <- concreteOptionalAssignmentSource source ->
              specifyFamily specify source (argumentAlternatives source) target
        FederationSpecificationForm originalSource previousTarget branches ->
          case decideSubfederation previousTarget target of
            DecisionProved () ->
              specifyFamily specify originalSource branches target
            DecisionRefuted ->
              Left (AtlasMapFederationOperationRefuted
                AtlasMapFederationSubfederationHasMissingMember)
            DecisionUndecidable ->
              Left (AtlasMapFederationOperationUndecidable
                (NoAtlasMapFederationDecisionProcedure
                  AtlasMapFederationSubfederation))
        SpecificationForm specification ->
          widenSpecification decideSubfederation source specification target
        AssignmentForm specification ->
          widenSpecification decideSubfederation source specification target
        ConcatenatedMapForm _ _ -> do
          presentations <- concatenatedSourcePresentations source
          case presentations of
            Just branches -> specifyFamily specify source branches target
            Nothing -> specifyTotalAtlasMap source target
        _ -> specifyTotalAtlasMap source target

-- Concatenation preserves each operand's family of presentations. Distribute
-- finite alternatives through its retained tree before requiring a total
-- source, then certify every resulting concatenation against the target.
concatenatedSourcePresentations
  :: InterpretedValue
  -> Either InterpretingError (Maybe [InterpretedValue])
concatenatedSourcePresentations value =
  case interpretedForm value of
    ArgumentMapForm _ underlying ->
      Right (Just (argumentAlternatives underlying))
    EitherForm _
      | Nothing <- concreteOptionalAssignmentSource value ->
          Right (Just (argumentAlternatives value))
    ConcatenatedMapForm left right -> do
      leftPresentations <- concatenatedSourcePresentations left
      rightPresentations <- concatenatedSourcePresentations right
      case (leftPresentations, rightPresentations) of
        (Nothing, Nothing) -> Right Nothing
        _ -> Just <$> sequence
          [ concatenateValues leftSource rightSource
          | leftSource <- maybe [left] id leftPresentations
          , rightSource <- maybe [right] id rightPresentations
          ]
    _ -> Right Nothing

specifyFamily
  :: Specifier
  -> InterpretedValue
  -> [InterpretedValue]
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyFamily specify source branches target = do
  specified <- traverse (`specify` target) branches
  pure
    (makeInterpretedValue
      (composedStructuralDatraType
        (map interpretedDatraType [source, target]))
      (FederationSpecificationForm source target specified)
      NoInsertion
      emptyInterpretedMap
      (interpretedAtlasMapFederation target)
      NonTotalInterpretedMap
      (SpecificationSemantics
        (interpretedSemantics source) (interpretedSemantics target)))

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
    DependentIdentifierTypeSemantics
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
-- and target coincide.
assignIdentifierValues
  :: (DatraBoolean -> InterpretedValue)
  -> Specifier
  -> SubfederationDecider
  -> String
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
assignIdentifierValues
    makeBoolean
    specify
    decideSubfederation
    identifierString
    typeAnnotation
    givenValue = do
  case distinguishedAssignment
      makeBoolean identifierString typeAnnotation givenValue of
    Just value -> Right value
    Nothing -> do
      let source = simpleIdentifierTypeValue identifierString givenValue
          target = simpleIdentifierTypeValue identifierString typeAnnotation
      specified <-
        specifyValuesWithoutIdentity
          specify decideSubfederation source target
      case interpretedForm specified of
        SpecificationForm specification ->
          Right
            (makeInterpretedValue
              (composedStructuralDatraType
                (map interpretedDatraType [typeAnnotation, givenValue]))
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

distinguishedAssignment
  :: (DatraBoolean -> InterpretedValue)
  -> String
  -> InterpretedValue
  -> InterpretedValue
  -> Maybe InterpretedValue
distinguishedAssignment makeBoolean identifierString typeAnnotation givenValue
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
    DecisionRefuted ->
      Left
        (AtlasMapFederationOperationRefuted
          AtlasMapFederationSpecificationHasNoMatchingMember)
    DecisionUndecidable ->
      Left
        (AtlasMapFederationOperationUndecidable
          (NoAtlasMapFederationDecisionProcedure
            AtlasMapFederationSpecification))

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

widenSpecification
  :: SubfederationDecider
  -> InterpretedValue
  -> EvaluatedSpecification
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
widenSpecification decideSubfederation source specification target =
  if interpretedCanonicalResult
      (evaluatedSpecificationTarget specification)
      == interpretedCanonicalResult target
    then Right source
    else
      case decideSubfederation
          (evaluatedSpecificationTarget specification)
          target of
        DecisionProved () ->
          case selectFederationMember
              (evaluatedSpecificationSourceValue specification) target of
            DecisionProved member ->
              Right
                (specifiedValue
                  (evaluatedSpecificationSourceValue specification)
                  (evaluatedSpecificationSource specification)
                  (originalSpecificationSourceSemantics source)
                  target
                  member)
            _ ->
              Left (AtlasMapFederationOperationUndecidable
                (NoAtlasMapFederationDecisionProcedure
                  AtlasMapFederationSpecification))
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
    (composedStructuralDatraType
      (map interpretedDatraType [sourceValue, target]))
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
      DependentIdentifierTypeSemantics
        (SimpleIdentifierDependency identifierString)
        givenValueSemantics
        True
    semantics -> semantics
