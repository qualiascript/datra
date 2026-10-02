-- | Decompose a concrete string-template specification into its source string
-- and the pointwise specifications selected for each interpolation.
module Extract
  ( extractValue
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (PrimitiveAtlasMapFederation) )
import Evaluation.Construction (makeAsciiString)
import Evaluation.Error
  ( InterpretingError (ExpectedStringTemplateSpecification) )
import Evaluation.Federation.Structure (sequenceOperands)
import Evaluation.Map (makeAtlasMap)
import Evaluation.Specification (specifyValues)
import Evaluation.Value

extractValue
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
extractValue stringType value =
  case interpretedForm value of
    SpecificationForm specification ->
      extractSpecification stringType specification
    AssignmentForm specification ->
      extractSpecification stringType specification
    AsciiStringForm _ -> assembleExtraction stringType value []
    SequentialMapForm
      | Just members <- sequenceOperands value ->
          makeAtlasMap 2 <$> traverse (extractValue stringType) members
    _ -> extractionExpected value

extractSpecification
  :: InterpretedValue
  -> EvaluatedSpecification
  -> Either InterpretingError InterpretedValue
extractSpecification stringType specification =
  extractContext
    stringType
    (evaluatedSpecificationSourceValue specification)
    (evaluatedSpecificationTarget specification)
    (evaluatedSpecificationMember specification)

-- Identifier assignments retain the same selection witness under one
-- identifier wrapper. Extract deliberately forgets that wrapper and works on
-- the underlying string-template specification.
extractContext
  :: InterpretedValue
  -> InterpretedValue
  -> InterpretedValue
  -> EvaluatedAtlasMapFederationMember
  -> Either InterpretingError InterpretedValue
extractContext stringType source target member =
  case (interpretedForm source, interpretedForm target, member) of
    ( DependentIdentifierTypeForm sourceIdentifier
      , DependentIdentifierTypeForm targetIdentifier
      , EvaluatedDependentIdentifierTypeMember underlyingMember
      ) ->
        extractContext
          stringType
          (evaluatedIdentifierUnderlying sourceIdentifier)
          (evaluatedIdentifierUnderlying targetIdentifier)
          underlyingMember
    _ -> do
      sourceString <- requireConcreteString source
      holes <- extractTemplateHoles target member
      assembleExtraction stringType sourceString holes

requireConcreteString
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
requireConcreteString value =
  case interpretedForm value of
    AsciiStringForm _ -> Right value
    SpecificationForm specification ->
      requireConcreteString
        (evaluatedSpecificationSourceValue specification)
    AssignmentForm specification ->
      requireConcreteString
        (evaluatedSpecificationSourceValue specification)
    DependentIdentifierTypeForm identifier ->
      requireConcreteString (evaluatedIdentifierUnderlying identifier)
    _ -> extractionExpected value

assembleExtraction
  :: InterpretedValue
  -> InterpretedValue
  -> [InterpretedValue]
  -> Either InterpretingError InterpretedValue
assembleExtraction stringType source holes = do
  extractedHoles <-
    case holes of
      [] -> pure <$> specifyValues source stringType
      _ -> Right holes
  pure (makeAtlasMap 2 (source : extractedHoles))

extractTemplateHoles
  :: InterpretedValue
  -> EvaluatedAtlasMapFederationMember
  -> Either InterpretingError [InterpretedValue]
extractTemplateHoles target member =
  case interpretedForm target of
    TemplateForm underlying ->
      extractTemplateHoles underlying member
    CoalizationForm underlying ->
      extractTemplateHoles underlying member
    DependentSumForm _ ->
      case member of
        EvaluatedDependentSumMember selected ->
          pure <$> specifyValues selected target
        _ -> extractionExpected target
    ConcatenatedMapForm left right ->
      case member of
        EvaluatedConcatenatedAtlasMapMember [leftMember, rightMember] ->
          (<>)
            <$> extractTemplateHoles left leftMember
            <*> extractTemplateHoles right rightMember
        _ -> extractionExpected target
    AsciiStringForm _ -> Right []
    IdentifierValueTypeForm ->
      case member of
        EvaluatedAsciiStringMember characters ->
          pure <$> specifyValues (makeAsciiString characters) target
        _ -> extractionExpected target
    ToStringForm ->
      case (interpretedAtlasMapFederation target, member) of
        ( PrimitiveAtlasMapFederation
            (ToStringAtlasMapFederation original _)
          , EvaluatedToStringMember selected _
          ) -> pure <$> specifyValues selected original
        _ -> extractionExpected target
    _ -> extractionExpected target

extractionExpected
  :: InterpretedValue
  -> Either InterpretingError result
extractionExpected =
  Left
    . ExpectedStringTemplateSpecification
    . interpretedValueKind
