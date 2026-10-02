-- | Inclusion rules owned by structural Datra types.
module Evaluation.TypeFamily.Structural.Subfederation
  ( decideStructuralSubfederation
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationDecision (..)
  , AtlasMapFederationExpression (..)
  )
import Evaluation.Federation (decidePrimitiveSubfederation)
import Evaluation.Federation.Structure
  ( concatenationOperands
  , expansionOperands
  , sequenceOperands
  )
import Evaluation.Map (makeAtlasMap)
import Evaluation.Numerical
  ( nonnegativeFederationInComplementedInteger )
import Evaluation.Specification.Composition (selectFederationMember)
import Evaluation.Specification.Decision
import Evaluation.Specification.String (federationProducesStrings)
import Evaluation.Value

type SubfederationDecider =
  InterpretedValue -> InterpretedValue -> Decision ()

-- | Decide inclusion for the structural family. Recursive comparisons are
-- routed back through the central decider so nested values can change family.
decideStructuralSubfederation
  :: SubfederationDecider
  -> InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideStructuralSubfederation decideSubfederation source target
  | SkipForm sourcePayload <- interpretedForm source
  , SkipForm targetPayload <- interpretedForm target =
      decideSubfederation sourcePayload targetPayload
  | SkipForm _ <- interpretedForm source = DecisionRefuted
  | SkipForm _ <- interpretedForm target = DecisionRefuted
  | CoalizationForm sourceOperand <- interpretedForm source
  , CoalizationForm targetOperand <- interpretedForm target =
      decideSubfederation sourceOperand targetOperand
  | CoalizationForm _ <- interpretedForm target
  , Just included <- nonnegativeFederationInComplementedInteger
      (interpretedSemantics source) (interpretedSemantics target) =
      if included then DecisionProved () else DecisionRefuted
  | CoalizationForm sourceOperand <- interpretedForm source =
      decideSubfederation sourceOperand target
  | CoalizationForm _ <- interpretedForm target
  , interpretedValueHasTotalMap source =
      mapDecision (const ()) (selectFederationMember source target)
  | CoalizationForm targetOperand <- interpretedForm target =
      decideSubfederation source targetOperand
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
  | Just targetMembers <- sequenceOperands target =
      decideSequenceSubfederation
        decideSubfederation
        (maybe [source] id (sequenceOperands source))
        targetMembers
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
    ConcatenatedAtlasMapFederation _ _
      | not (isConcatenatedFederation sourceFederation)
      , not (isSequentialFederation sourceFederation) ->
          decideAny
            [ decideSubfederation source member
            | member <- concatenationOperands target
            ]
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
          ) -> DecisionRefuted
        ( ConcatenatedAtlasMapFederation _ _
          , SequentialAtlasMapFederation _
          ) -> DecisionRefuted
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
    isConcatenatedFederation federation =
      case federation of
        ConcatenatedAtlasMapFederation _ _ -> True
        _ -> False
    isSequentialFederation federation =
      case federation of
        SequentialAtlasMapFederation _ -> True
        _ -> False

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

decideSequenceSubfederation
  :: SubfederationDecider
  -> [InterpretedValue]
  -> [InterpretedValue]
  -> Decision ()
decideSequenceSubfederation _ [] [] = DecisionProved ()
decideSequenceSubfederation _ _ [] = DecisionRefuted
decideSequenceSubfederation decideSubfederation sources
    (target : remainingTargets) =
  decideAny (consumeSource <> [consumeUnit])
  where
    consumeSource = case sources of
      [] -> []
      source : remainingSources ->
        [ mapDecision
            (const ())
            (decideAll
              [ decideSubfederation source target
              , decideSequenceSubfederation
                  decideSubfederation remainingSources remainingTargets
              ])
        ]
    consumeUnit =
      mapDecision
        (const ())
        (decideAll
          [ decideSubfederation (makeAtlasMap 0 []) target
          , decideSequenceSubfederation
              decideSubfederation sources remainingTargets
          ])

isNonAlternativeMember :: InterpretedValue -> Bool
isNonAlternativeMember member =
  case interpretedForm member of
    EitherForm _ -> False
    _ -> True
