-- | Specification and inclusion rules owned by structural Datra types.
--
-- The recursive operations are supplied by the central dispatch modules. This
-- keeps the family implementation independent of those dispatchers while
-- still allowing composite structural values to recurse into any type family.
module Evaluation.TypeFamily.Structural
  ( assignIdentifierValues
  , decideStructuralSubfederation
  , specifyStructural
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationDecision (..)
  , AtlasMapFederationExpression (..)
  )
import BooleanType (DatraBoolean (..))
import DatraLanguage.AST (renderAsciiStringLiteral)
import Evaluation.Access.Federation (federationIsCoalition)
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
  )
import Evaluation.Federation (decidePrimitiveSubfederation)
import Evaluation.Federation.Structure
  ( concatenationOperands
  , expansionOperands
  , sequenceOperands
  )
import Evaluation.Identifier (simpleIdentifierTypeValue)
import Evaluation.Map (concatenateValues)
import Evaluation.Optional (makeNothing)
import Evaluation.Specification.Composition (selectFederationMember)
import Evaluation.Specification.Decision
import Evaluation.Specification.String
  ( federationProducesStrings
  , federationUsesWeakToString
  )
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
      Left (FunctionError "expected a function type")
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

-- | Decide inclusion for the structural family. Recursive comparisons are
-- routed back through the central decider so nested values can change family.
decideStructuralSubfederation
  :: SubfederationDecider
  -> InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideStructuralSubfederation decideSubfederation source target
  | Just _ <- interpretedFunction source
  , EitherForm targetEither <- interpretedForm target =
      decideAnyEitherAlternative decideSubfederation source targetEither
  | BuiltinMetaTypeForm _ <- interpretedForm source = DecisionRefuted
  | Just _ <- interpretedFunction source = DecisionRefuted
  | ArgumentMapForm _ underlying <- interpretedForm source =
      decideSubfederation underlying target
  | ArgumentMapForm members _ <- interpretedForm target
  , all isNonAlternativeMember members
  , interpretedValueHasTotalMap source =
      mapDecision (const ()) (selectFederationMember source target)
  | ArgumentMapForm _ underlying <- interpretedForm target =
      decideSubfederation source underlying
  | FederationSpecificationForm _ previousTarget _ <- interpretedForm source =
      decideSubfederation previousTarget target
  | SpecificationForm specification <- interpretedForm source =
      decideSubfederation
        (evaluatedSpecificationTarget specification)
        target
  | AssignmentForm assignment <- interpretedForm source =
      decideSubfederation
        (evaluatedSpecificationTarget assignment)
        target
  | Just sourceMembers <- sequenceOperands source
  , Just targetMembers <- sequenceOperands target =
      decidePointwiseSubfederation
        decideSubfederation (Just sourceMembers) (Just targetMembers)
  | interpretedValueHasTotalMap source =
      mapDecision (const ()) (selectFederationMember source target)
  | otherwise =
      case (interpretedForm source, interpretedForm target) of
        (EitherForm sourceEither, _) ->
          decideAllEitherAlternatives
            decideSubfederation sourceEither target
        (_, EitherForm targetEither) ->
          decideAnyEitherAlternative
            decideSubfederation source targetEither
        _ ->
          decideNonEitherSubfederation
            decideSubfederation source target

decideNonEitherSubfederation
  :: SubfederationDecider
  -> InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideNonEitherSubfederation decideSubfederation source target =
  case targetFederation of
    PrimitiveAtlasMapFederation StringTypeAtlasMapFederation
      | federationProducesStrings sourceFederation -> DecisionProved ()
    _ ->
      case (sourceFederation, targetFederation) of
        ( PrimitiveAtlasMapFederation
            (DependentIdentifierTypeAtlasMapFederation sourceIdentifier)
          , PrimitiveAtlasMapFederation
            (DependentIdentifierTypeAtlasMapFederation targetIdentifier)
          ) ->
            decideIdentifierSubfederation
              decideSubfederation sourceIdentifier targetIdentifier
        ( PrimitiveAtlasMapFederation
            (IdentifierStringProjectionAtlasMapFederation sourceIdentifier)
          , PrimitiveAtlasMapFederation
            (IdentifierStringProjectionAtlasMapFederation targetIdentifier)
          ) ->
            decideIdentifierSubfederation
              decideSubfederation sourceIdentifier targetIdentifier
        ( PrimitiveAtlasMapFederation sourcePrimitive
          , PrimitiveAtlasMapFederation targetPrimitive
          ) ->
            case (sourcePrimitive, targetPrimitive) of
              ( ToStringAtlasMapFederation sourceValue _
                , ToStringAtlasMapFederation targetValue _
                ) -> decideSubfederation sourceValue targetValue
              _ ->
                primitiveSubfederationDecision
                  sourcePrimitive targetPrimitive
        (SequentialAtlasMapFederation _, SequentialAtlasMapFederation _) ->
          decidePointwiseSubfederation
            decideSubfederation
            (sequenceOperands source)
            (sequenceOperands target)
        ( SequentialAtlasMapFederation _
          , ConcatenatedAtlasMapFederation _ _
          ) ->
            decideCoalitionComponents
              decideSubfederation
              (sequenceOperands source)
              (Just (concatenationOperands target))
        ( ConcatenatedAtlasMapFederation _ _
          , SequentialAtlasMapFederation _
          ) ->
            decideCoalitionComponents
              decideSubfederation
              (Just (concatenationOperands source))
              (sequenceOperands target)
        ( ExpansionAtlasMapFederation _ _
          , ExpansionAtlasMapFederation _ _
          ) ->
            decideExpansionSubfederation
              decideSubfederation source target
        ( ConcatenatedAtlasMapFederation _ _
          , ConcatenatedAtlasMapFederation _ _
          ) ->
            decidePointwiseSubfederation
              decideSubfederation
              (Just (concatenationOperands source))
              (Just (concatenationOperands target))
        _ -> DecisionUndecidable
  where
    sourceFederation = interpretedAtlasMapFederation source
    targetFederation = interpretedAtlasMapFederation target

decideAllEitherAlternatives
  :: SubfederationDecider
  -> EvaluatedEither
  -> InterpretedValue
  -> Decision ()
decideAllEitherAlternatives decideSubfederation source target =
  mapDecision
    (const ())
    (decideAll
      [ decideSubfederation (evaluatedEitherLeft source) target
      , decideSubfederation (evaluatedEitherRight source) target
      ])

decideAnyEitherAlternative
  :: SubfederationDecider
  -> InterpretedValue
  -> EvaluatedEither
  -> Decision ()
decideAnyEitherAlternative decideSubfederation source target =
  decideAny
    [ decideSubfederation source (evaluatedEitherLeft target)
    , decideSubfederation source (evaluatedEitherRight target)
    ]

decideIdentifierSubfederation
  :: SubfederationDecider
  -> EvaluatedDependentIdentifierType
  -> EvaluatedDependentIdentifierType
  -> Decision ()
decideIdentifierSubfederation decideSubfederation source target
  | identifierDependenciesCompatible
      (evaluatedIdentifierDependency source)
      (evaluatedIdentifierDependency target) =
        decideSubfederation
          (evaluatedIdentifierUnderlying source)
          (evaluatedIdentifierUnderlying target)
  | otherwise = DecisionRefuted

decideExpansionSubfederation
  :: SubfederationDecider
  -> InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideExpansionSubfederation decideSubfederation source target =
  case (expansionOperands source, expansionOperands target) of
    (Just (sourceLeft, sourceRight), Just (targetLeft, targetRight)) ->
      mapDecision
        (const ())
        (decideAll
          [ decideSubfederation sourceLeft targetLeft
          , decideSubfederation sourceRight targetRight
          ])
    _ -> DecisionRefuted

primitiveSubfederationDecision
  :: InterpretedAtlasMapFederationPrimitive
  -> InterpretedAtlasMapFederationPrimitive
  -> Decision ()
primitiveSubfederationDecision source target =
  case decidePrimitiveSubfederation source target of
    AtlasMapFederationProved () -> DecisionProved ()
    AtlasMapFederationRefuted _ -> DecisionRefuted
    AtlasMapFederationUndecidable _ -> DecisionUndecidable

decidePointwiseSubfederation
  :: SubfederationDecider
  -> Maybe [InterpretedValue]
  -> Maybe [InterpretedValue]
  -> Decision ()
decidePointwiseSubfederation
    decideSubfederation
    (Just sourceMembers)
    (Just targetMembers)
  | length sourceMembers == length targetMembers =
      mapDecision
        (const ())
        (decideAll
          (zipWith decideSubfederation sourceMembers targetMembers))
decidePointwiseSubfederation _ _ _ = DecisionRefuted

-- A sequence and its explicit concatenation describe the same ordered
-- federation exactly when every component is a coalition.
decideCoalitionComponents
  :: SubfederationDecider
  -> Maybe [InterpretedValue]
  -> Maybe [InterpretedValue]
  -> Decision ()
decideCoalitionComponents decideSubfederation sourceMembers targetMembers =
  case (sourceMembers, targetMembers) of
    (Just source, Just target)
      | all valueIsCoalition (source <> target) ->
          decidePointwiseSubfederation
            decideSubfederation sourceMembers targetMembers
    _ -> DecisionRefuted

valueIsCoalition :: InterpretedValue -> Bool
valueIsCoalition =
  federationIsCoalition . interpretedAtlasMapFederation

isNonAlternativeMember :: InterpretedValue -> Bool
isNonAlternativeMember member =
  case interpretedForm member of
    EitherForm _ -> False
    _ -> True
