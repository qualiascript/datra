-- | Inclusion decisions between evaluated Atlas-map federations.
module Evaluation.Specification.Subfederation
  ( decideValueSubfederation
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationDecision (..)
  , AtlasMapFederationExpression (..)
  )
import Evaluation.Federation (decidePrimitiveSubfederation)
import Evaluation.Access.Federation (federationIsCoalition)
import Evaluation.Federation.Structure
  ( concatenationOperands
  , expansionOperands
  , sequenceOperands
  )
import Evaluation.Specification.Composition (selectFederationMember)
import Evaluation.Specification.Decision
import Evaluation.Specification.String (federationProducesStrings)
import Evaluation.Value

-- | Decide inclusion of evaluated federation constructions. A total-map
-- source reduces to ordinary member selection. Primitive families use their
-- established inclusion procedure, while composite families are checked
-- componentwise after erasing only concatenation associativity.
decideValueSubfederation
  :: InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideValueSubfederation source target
  | EitherForm alternatives <- interpretedForm source, not (null (functionAlternatives source)) =
      decideAllEitherAlternatives alternatives target
  | EitherForm alternatives <- interpretedForm target, not (null (functionAlternatives target)) =
      decideAnyEitherAlternative source alternatives
  | otherwise =
      case canonicalSubfederationImplementation
          (interpretedCanonicalType target) of
        BuiltinMetaSubfederation kind -> decideMetaType source kind
        FunctionSubfederation -> decideFunctionSubfederation source target
        StructuralSubfederation ->
          decideStructuralSubfederation source target
        TotalBlockSubfederation ->
          decideTotalBlockSubfederation source target

decideTotalBlockSubfederation
  :: InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideTotalBlockSubfederation source target
  | interpretedCanonicalResult source == interpretedCanonicalResult target =
      DecisionProved ()
  | otherwise = DecisionRefuted

decideFunctionSubfederation
  :: InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideFunctionSubfederation source target
  | BuiltinMetaTypeForm _ <- interpretedForm source = DecisionRefuted
  | Just sourceFunction <- interpretedFunction source
  , Just targetFunction <- interpretedFunction target =
      if not (patternCompatible (functionPattern sourceFunction) (functionPattern targetFunction))
        then DecisionRefuted else case functionSource targetFunction of
        Just _ -> DecisionUndecidable
        Nothing -> mapDecision (const ()) (decideAll
          [ decideValueSubfederation (functionDomain targetFunction) (functionDomain sourceFunction)
          , decideValueSubfederation (functionCodomain sourceFunction) (functionCodomain targetFunction)
          ])
  | otherwise = DecisionRefuted

decideStructuralSubfederation
  :: InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideStructuralSubfederation source target
  | BuiltinMetaTypeForm _ <- interpretedForm source = DecisionRefuted
  | Just _ <- interpretedFunction source = DecisionRefuted
  | ArgumentMapForm _ underlying <- interpretedForm source =
      decideValueSubfederation underlying target
  | ArgumentMapForm _ underlying <- interpretedForm target =
      decideValueSubfederation source underlying
  | FederationSpecificationForm _ previousTarget _ <- interpretedForm source =
      decideValueSubfederation previousTarget target
  | SpecificationForm specification <- interpretedForm source =
      decideValueSubfederation
        (evaluatedSpecificationTarget specification)
        target
  | AssignmentForm assignment <- interpretedForm source =
      decideValueSubfederation
        (evaluatedSpecificationTarget assignment)
        target
  | Just sourceMembers <- sequenceOperands source
  , Just targetMembers <- sequenceOperands target =
      decidePointwiseSubfederation (Just sourceMembers) (Just targetMembers)
  | interpretedValueHasTotalMap source =
      mapDecision (const ()) (selectFederationMember source target)
  | otherwise =
      case (interpretedForm source, interpretedForm target) of
        (EitherForm sourceEither, _) ->
          decideAllEitherAlternatives sourceEither target
        (_, EitherForm targetEither) ->
          decideAnyEitherAlternative source targetEither
        _ -> decideNonEitherSubfederation source target

decideNonEitherSubfederation
  :: InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideNonEitherSubfederation source target =
  case targetFederation of
    PrimitiveAtlasMapFederation StringTypeAtlasMapFederation
      | federationProducesStrings sourceFederation -> DecisionProved ()
    _ ->
      case (sourceFederation, targetFederation) of
        ( PrimitiveAtlasMapFederation
            (DependentIdentifierTypeAtlasMapFederation sourceIdentifier)
          , PrimitiveAtlasMapFederation
            (DependentIdentifierTypeAtlasMapFederation targetIdentifier)
          ) -> decideIdentifierSubfederation sourceIdentifier targetIdentifier
        ( PrimitiveAtlasMapFederation
            (IdentifierStringProjectionAtlasMapFederation sourceIdentifier)
          , PrimitiveAtlasMapFederation
            (IdentifierStringProjectionAtlasMapFederation targetIdentifier)
          ) -> decideIdentifierSubfederation sourceIdentifier targetIdentifier
        ( PrimitiveAtlasMapFederation sourcePrimitive
          , PrimitiveAtlasMapFederation targetPrimitive
          ) ->
            case (sourcePrimitive, targetPrimitive) of
              ( ToStringAtlasMapFederation sourceValue _
                , ToStringAtlasMapFederation targetValue _
                ) -> decideValueSubfederation sourceValue targetValue
              _ ->
                primitiveSubfederationDecision
                  sourcePrimitive targetPrimitive
        (SequentialAtlasMapFederation _, SequentialAtlasMapFederation _) ->
          decidePointwiseSubfederation
            (sequenceOperands source)
            (sequenceOperands target)
        ( SequentialAtlasMapFederation _
          , ConcatenatedAtlasMapFederation _ _
          ) ->
            decideCoalitionComponents
              (sequenceOperands source)
              (Just (concatenationOperands target))
        ( ConcatenatedAtlasMapFederation _ _
          , SequentialAtlasMapFederation _
          ) ->
            decideCoalitionComponents
              (Just (concatenationOperands source))
              (sequenceOperands target)
        ( ExpansionAtlasMapFederation _ _
          , ExpansionAtlasMapFederation _ _
          ) ->
            decideExpansionSubfederation source target
        ( ConcatenatedAtlasMapFederation _ _
          , ConcatenatedAtlasMapFederation _ _
          ) ->
            decidePointwiseSubfederation
              (Just (concatenationOperands source))
              (Just (concatenationOperands target))
        _ -> DecisionUndecidable
  where
    sourceFederation = interpretedAtlasMapFederation source
    targetFederation = interpretedAtlasMapFederation target

-- An Either is a federation union: every source alternative must occur in the
-- target, but it may occur in any target branch. Branch tags are selection
-- routes only, so neither association nor order affects inclusion.
decideAllEitherAlternatives
  :: EvaluatedEither
  -> InterpretedValue
  -> Decision ()
decideAllEitherAlternatives source target =
  mapDecision
    (const ())
    (decideAll
      [ decideValueSubfederation
          (evaluatedEitherLeft source)
          target
      , decideValueSubfederation
          (evaluatedEitherRight source)
          target
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

decideIdentifierSubfederation
  :: EvaluatedDependentIdentifierType
  -> EvaluatedDependentIdentifierType
  -> Decision ()
decideIdentifierSubfederation source target
  | identifierDependenciesCompatible
      (evaluatedIdentifierDependency source)
      (evaluatedIdentifierDependency target) =
        decideValueSubfederation
          (evaluatedIdentifierUnderlying source)
          (evaluatedIdentifierUnderlying target)
  | otherwise = DecisionRefuted

decideExpansionSubfederation
  :: InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideExpansionSubfederation source target =
  case (expansionOperands source, expansionOperands target) of
    (Just (sourceLeft, sourceRight), Just (targetLeft, targetRight)) ->
      mapDecision
        (const ())
        (decideAll
          [ decideValueSubfederation sourceLeft targetLeft
          , decideValueSubfederation sourceRight targetRight
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
  :: Maybe [InterpretedValue]
  -> Maybe [InterpretedValue]
  -> Decision ()
decidePointwiseSubfederation
    (Just sourceMembers)
    (Just targetMembers)
  | length sourceMembers == length targetMembers =
      mapDecision
        (const ())
        (decideAll
          (zipWith decideValueSubfederation sourceMembers targetMembers))
decidePointwiseSubfederation _ _ = DecisionRefuted

-- A sequence and its explicit concatenation describe the same ordered
-- federation exactly when every component is a coalition. Other
-- sequence/concatenation pairs retain their distinct construction semantics.
decideCoalitionComponents
  :: Maybe [InterpretedValue]
  -> Maybe [InterpretedValue]
  -> Decision ()
decideCoalitionComponents sourceMembers targetMembers =
  case (sourceMembers, targetMembers) of
    (Just source, Just target)
      | all valueIsCoalition (source <> target) ->
          decidePointwiseSubfederation sourceMembers targetMembers
    _ -> DecisionRefuted

valueIsCoalition :: InterpretedValue -> Bool
valueIsCoalition =
  federationIsCoalition . interpretedAtlasMapFederation

patternCompatible :: Maybe (String, Bool) -> Maybe (String, Bool) -> Bool
patternCompatible _ Nothing = True
patternCompatible (Just source) (Just target) = source == target
patternCompatible Nothing (Just _) = False


decideMetaType :: InterpretedValue -> BuiltinMetaType -> Decision ()
decideMetaType source target =
  if accepted then DecisionProved () else DecisionRefuted
  where
    accepted = case (interpretedForm source, target) of
      (BuiltinMetaTypeForm actual, expected) | actual == expected -> True
      (BuiltinMetaTypeForm (ASTMetaType _), ASTMetaType Nothing) -> True
      (BuiltinMetaTypeForm NatRangeMetaType, IntRangeMetaType) -> True
      (NaturalRangeForm _, NatRangeMetaType) -> True
      (ValuedNaturalRangeForm _, NatRangeMetaType) -> True
      (NaturalRangeForm _, IntRangeMetaType) -> True
      (ValuedNaturalRangeForm _, IntRangeMetaType) -> True
      (IntegerRangeForm _, IntRangeMetaType) -> True
      (ValuedIntegerRangeForm _, IntRangeMetaType) -> True
      (_, StringTemplateMetaType) -> federationProducesStrings (interpretedAtlasMapFederation source)
      _ -> False
