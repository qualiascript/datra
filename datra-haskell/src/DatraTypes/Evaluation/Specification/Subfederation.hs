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
  | AssignmentForm assignment <- interpretedForm source =
      decideValueSubfederation
        (evaluatedSpecificationTarget assignment)
        target
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
            (IdentifierTypeAtlasMapFederation sourceIdentifier)
          , PrimitiveAtlasMapFederation
            (IdentifierTypeAtlasMapFederation targetIdentifier)
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
  :: EvaluatedIdentifierType
  -> EvaluatedIdentifierType
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
