-- | Observable projections carried by successful string-backed specifications.
module Evaluation.Specification.Projection
  ( specificationProjection
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (PrimitiveAtlasMapFederation) )
import BooleanType (DatraBoolean (..))
import Evaluation.Construction (makeAsciiString)
import Evaluation.Error (InterpretingError)
import Evaluation.Identifier (identifierNameFederationFor)
import Evaluation.Map (makeAtlasMapPreservingSingleton)
import Evaluation.Specification (specifyValues)
import Evaluation.Value

-- | Present retained matching evidence as an ordinary finite map. String
-- templates expose the complete source string followed by their interpolation
-- selections. Dependent identifiers expose their selected name followed by
-- the specification of their underlying values.
specificationProjection
  :: EvaluatedSpecification
  -> Either InterpretingError (Maybe InterpretedValue)
specificationProjection specification =
  projectionFor source target member
  where
    source = evaluatedSpecificationSourceValue specification
    target = evaluatedSpecificationTarget specification
    member = evaluatedSpecificationMember specification

projectionFor
  :: InterpretedValue
  -> InterpretedValue
  -> EvaluatedAtlasMapFederationMember
  -> Either InterpretingError (Maybe InterpretedValue)
projectionFor source target member =
  case (interpretedForm source, interpretedForm target, member) of
    ( DependentIdentifierTypeForm sourceIdentifier
      , DependentIdentifierTypeForm targetIdentifier
      , EvaluatedDependentIdentifierTypeMember
          (Just _)
          _
      ) -> do
        let supplied = evaluatedIdentifierUnderlying sourceIdentifier
        sourceName <- identifierNameFederationFor sourceIdentifier supplied
        underlying <- specifyValues
          supplied
          (evaluatedIdentifierUnderlying targetIdentifier)
        pure (Just (projectionMap [sourceName, underlying]))
    ( DependentIdentifierTypeForm sourceIdentifier
      , DependentIdentifierTypeForm targetIdentifier
      , EvaluatedDependentIdentifierTypeMember
          Nothing
          underlyingMember
      ) ->
        projectionFor
          (evaluatedIdentifierUnderlying sourceIdentifier)
          (evaluatedIdentifierUnderlying targetIdentifier)
          underlyingMember
    (_, EitherForm alternatives, EvaluatedEitherMember side selected) ->
      projectionFor
        source
        (case side of
          DatraFalse -> evaluatedEitherLeft alternatives
          DatraTrue -> evaluatedEitherRight alternatives)
        selected
    (_, TemplateForm underlying, _) -> do
      maybeHoles <- templateHoles underlying member
      pure $ do
        holes <- maybeHoles
        sourceString <- concreteString source
        if null holes
          then Nothing
          else Just (projectionMap (sourceString : holes))
    _ -> pure Nothing

projectionMap :: [InterpretedValue] -> InterpretedValue
projectionMap = makeAtlasMapPreservingSingleton 2

concreteString
  :: InterpretedValue
  -> Maybe InterpretedValue
concreteString value =
  case interpretedForm value of
    AsciiStringForm _ -> Just value
    SpecificationForm specification ->
      concreteString (evaluatedSpecificationSourceValue specification)
    AssignmentForm specification ->
      concreteString (evaluatedSpecificationSourceValue specification)
    DependentIdentifierTypeForm identifier ->
      concreteString (evaluatedIdentifierUnderlying identifier)
    _ -> Nothing

templateHoles
  :: InterpretedValue
  -> EvaluatedAtlasMapFederationMember
  -> Either InterpretingError (Maybe [InterpretedValue])
templateHoles target member =
  case interpretedForm target of
    TemplateForm underlying -> templateHoles underlying member
    CoalizationForm underlying ->
      case member of
        EvaluatedDependentSumMember selected ->
          Just . pure <$> specifyValues selected target
        _ -> templateHoles underlying member
    DependentSumForm _ ->
      case member of
        EvaluatedDependentSumMember selected ->
          Just . pure <$> specifyValues selected target
        _ -> pure Nothing
    ConcatenatedMapForm left right ->
      case member of
        EvaluatedConcatenatedAtlasMapMember [leftMember, rightMember] ->
          combineHoles
            <$> templateHoles left leftMember
            <*> templateHoles right rightMember
        _ -> pure Nothing
    AsciiStringForm _ -> pure (Just [])
    IdentifierValueTypeForm ->
      case member of
        EvaluatedAsciiStringMember characters ->
          Just . pure <$> specifyValues (makeAsciiString characters) target
        _ -> pure Nothing
    ToStringForm ->
      case (interpretedAtlasMapFederation target, member) of
        ( PrimitiveAtlasMapFederation
            (ToStringAtlasMapFederation original _)
          , EvaluatedToStringMember selected _
          ) -> Just . pure <$> specifyValues selected original
        _ -> pure Nothing
    _ -> pure Nothing

combineHoles :: Maybe [value] -> Maybe [value] -> Maybe [value]
combineHoles left right = (<>) <$> left <*> right
