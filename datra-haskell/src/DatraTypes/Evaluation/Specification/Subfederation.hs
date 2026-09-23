-- | Inclusion decisions between evaluated Atlas-map federations.
module Evaluation.Specification.Subfederation
  ( decideValueSubfederation
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
import Evaluation.Specification.Composition (selectFederationMember)
import Evaluation.Specification.Decision
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
  | interpretedValueHasTotalMap source =
      mapDecision (const ()) (selectFederationMember source target)
  | otherwise =
      case (interpretedForm source, interpretedForm target) of
        (EitherForm sourceEither, EitherForm targetEither) ->
          decideEitherSubfederation sourceEither targetEither
        (EitherForm _, _) -> DecisionRefuted
        (_, EitherForm targetEither) ->
          decideAny
            [ decideValueSubfederation
                source (evaluatedEitherLeft targetEither)
            , decideValueSubfederation
                source (evaluatedEitherRight targetEither)
            ]
        _ -> decideNonEitherSubfederation source target

decideNonEitherSubfederation
  :: InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideNonEitherSubfederation source target =
      case ( interpretedAtlasMapFederation source
           , interpretedAtlasMapFederation target
           ) of
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
            primitiveSubfederationDecision sourcePrimitive targetPrimitive
        (SequentialAtlasMapFederation _, SequentialAtlasMapFederation _) ->
          decidePointwiseSubfederation
            (sequenceOperands source)
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

-- Tagged alternatives preserve their left/right injection. The right branch
-- may itself be an Either, which permits the canonical right-associated tree
-- to embed a shorter union into a longer one without reordering alternatives.
decideEitherSubfederation
  :: EvaluatedEither
  -> EvaluatedEither
  -> Decision ()
decideEitherSubfederation source target =
  mapDecision
    (const ())
    (decideAll
      [ decideValueSubfederation
          (evaluatedEitherLeft source)
          (evaluatedEitherLeft target)
      , decideValueSubfederation
          (evaluatedEitherRight source)
          (evaluatedEitherRight target)
      ])

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
