-- | Decompose a concrete string-template specification into its source string
-- and the pointwise specifications selected for each interpolation.
module Extract
  ( extractValue
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (PrimitiveAtlasMapFederation) )
import Evaluation.Construction (makeAsciiString, makeStringType)
import Evaluation.Error
  ( InterpretingError (ExpectedStringTemplateSpecification) )
import Evaluation.Map (makeAtlasMap)
import Evaluation.Specification (specifyValues)
import Evaluation.Value

extractValue
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
extractValue value =
  case interpretedForm value of
    SpecificationForm specification -> extractSpecification specification
    AssignmentForm specification -> extractSpecification specification
    AsciiStringForm _ -> assembleExtraction value []
    _ -> extractionExpected value

extractSpecification
  :: EvaluatedSpecification
  -> Either InterpretingError InterpretedValue
extractSpecification specification =
  extractContext
    (evaluatedSpecificationSourceValue specification)
    (evaluatedSpecificationTarget specification)
    (evaluatedSpecificationMember specification)

-- Identifier assignments retain the same selection witness under one
-- identifier wrapper. Extract deliberately forgets that wrapper and works on
-- the underlying string-template specification.
extractContext
  :: InterpretedValue
  -> InterpretedValue
  -> EvaluatedAtlasMapFederationMember
  -> Either InterpretingError InterpretedValue
extractContext source target member =
  case (interpretedForm source, interpretedForm target, member) of
    ( IdentifierTypeForm sourceIdentifier
      , IdentifierTypeForm targetIdentifier
      , EvaluatedIdentifierTypeMember underlyingMember
      ) ->
        extractContext
          (evaluatedIdentifierUnderlying sourceIdentifier)
          (evaluatedIdentifierUnderlying targetIdentifier)
          underlyingMember
    _ -> do
      sourceString <- requireConcreteString source
      holes <- extractTemplateHoles target member
      assembleExtraction sourceString holes

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
    IdentifierTypeForm identifier ->
      requireConcreteString (evaluatedIdentifierUnderlying identifier)
    _ -> extractionExpected value

assembleExtraction
  :: InterpretedValue
  -> [InterpretedValue]
  -> Either InterpretingError InterpretedValue
assembleExtraction source holes = do
  extractedHoles <-
    case holes of
      [] -> pure <$> specifyValues source makeStringType
      _ -> Right holes
  pure (makeAtlasMap 2 (source : extractedHoles))

extractTemplateHoles
  :: InterpretedValue
  -> EvaluatedAtlasMapFederationMember
  -> Either InterpretingError [InterpretedValue]
extractTemplateHoles target member =
  case interpretedForm target of
    StringTemplateForm underlying ->
      extractTemplateHoles underlying member
    ConcatenatedMapForm left right ->
      case member of
        EvaluatedConcatenatedAtlasMapMember [leftMember, rightMember] ->
          (<>)
            <$> extractTemplateHoles left leftMember
            <*> extractTemplateHoles right rightMember
        _ -> extractionExpected target
    AsciiStringForm _ -> Right []
    StringTypeForm ->
      case member of
        EvaluatedAsciiStringMember characters ->
          pure <$> specifyValues (makeAsciiString characters) target
        _ -> extractionExpected target
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
