-- | Evaluated dependent and constant identifier types.
module Evaluation.Identifier
  ( dependentIdentifierTypeValue
  , simpleIdentifierTypeValue
  , inferredIdentifierAssignmentValue
  , identifierStringProjectionValue
  , requireCanonicalTypeAnnotation
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression
      ( PrimitiveAtlasMapFederation
      , SingletonAtlasMapFederation
      )
  )
import Evaluation.Construction (makeAsciiString)
import Evaluation.Error
  ( InterpretingError (NonCanonicalIdentifierTypeAnnotation) )
import Evaluation.Value

-- | Identifier annotations participate in canonical source syntax. A weak
-- Datra type can still be named as a value, but cannot define the annotated
-- member family of an identifier.
requireCanonicalTypeAnnotation
  :: InterpretedValue
  -> Either InterpretingError ()
requireCanonicalTypeAnnotation annotation =
  case datraCanonicalType (interpretedDatraType annotation) of
    Just _ -> Right ()
    Nothing -> Left NonCanonicalIdentifierTypeAnnotation

dependentIdentifierTypeValue
  :: String
  -> (CanonicalResult -> String)
  -> InterpretedValue
  -> InterpretedValue
dependentIdentifierTypeValue familyKey identifierStringFor =
  makeDependentIdentifierTypeValue
    (DependentIdentifierDependency familyKey identifierStringFor)

simpleIdentifierTypeValue
  :: String
  -> InterpretedValue
  -> InterpretedValue
simpleIdentifierTypeValue identifierString underlying
  | interpretedCanonicalResult underlying == CanonicalMap 0 [] =
      makeAsciiString identifierString
  | otherwise =
      makeDependentIdentifierTypeValue
        (SimpleIdentifierDependency identifierString)
        underlying

-- | An inferred assignment may bind a non-total value such as a type.  Its
-- federation remains the dependent identifier family, while its canonical
-- presentation records that the value was explicitly supplied.
inferredIdentifierAssignmentValue
  :: String
  -> InterpretedValue
  -> InterpretedValue
inferredIdentifierAssignmentValue identifierString underlying =
  (simpleIdentifierTypeValue identifierString underlying)
    { interpretedSemantics = AssignmentSemantics
        identifierString
        (interpretedSemantics underlying)
        (interpretedSemantics underlying)
    }

identifierStringProjectionValue
  :: EvaluatedDependentIdentifierType
  -> InterpretedValue
identifierStringProjectionValue evaluated = value
  where
    dependency = evaluatedIdentifierDependency evaluated
    underlying = evaluatedIdentifierUnderlying evaluated
    underlyingResult = interpretedCanonicalResult underlying
    isTotal = interpretedValueHasTotalMap underlying
    representativeString =
      identifierDependencyRepresentativeString
        dependency
        (if isTotal then Just underlyingResult else Nothing)
    representative = makeAsciiString representativeString
    semantics =
      IdentifierStringProjectionSemantics
        dependency
        (interpretedSemantics underlying)
        isTotal
    resultMap =
      (interpretedMap representative)
        { interpretedMapComponents = [semantics] }
    value =
      makeEvaluatedIdentifierValue
        (if isTotal
          then structuralDatraType
          else weakStructuralDatraType)
        (IdentifierStringProjectionForm evaluated)
        (IdentifierStringProjectionAtlasMapFederation evaluated)
        underlying
        resultMap
        semantics

makeDependentIdentifierTypeValue
  :: IdentifierDependency
  -> InterpretedValue
  -> InterpretedValue
makeDependentIdentifierTypeValue dependency underlying = value
  where
    evaluated = EvaluatedDependentIdentifierType dependency underlying
    underlyingResult = interpretedCanonicalResult underlying
    isTotal = interpretedValueHasTotalMap underlying
    representativeString =
      identifierDependencyRepresentativeString
        dependency
        (if isTotal then Just underlyingResult else Nothing)
    identifierStringValue = makeAsciiString representativeString
    finalValues =
      appendOrdinalOrderedValues
        (singletonOrdinalOrderedValues identifierStringValue)
        (singletonOrdinalOrderedValues underlying)
    semantics =
      DependentIdentifierTypeSemantics
        dependency
        (interpretedSemantics underlying)
        isTotal
    valueMap =
      InterpretedMap
        2
        finalValues
        [ interpretedSemantics identifierStringValue
        , interpretedSemantics underlying
        ]
    value =
      makeEvaluatedIdentifierValue
        canonicalType
        (DependentIdentifierTypeForm evaluated)
        (DependentIdentifierTypeAtlasMapFederation evaluated)
        underlying
        valueMap
        semantics
    canonicalType
      | isTotal = structuralDatraType
      | otherwise =
          case dependency of
            SimpleIdentifierDependency _ ->
              structuralDatraTypeWith
                (datraStringRepresentation
                  (interpretedDatraType underlying))
            DependentIdentifierDependency {} ->
              weakStructuralDatraType

-- | Identifier types and their string projections preserve the totality of
-- the underlying value. This is also the exact boundary between their
-- singleton and primitive federation representations.
makeEvaluatedIdentifierValue
  :: DatraType
  -> ValueForm
  -> InterpretedAtlasMapFederationPrimitive
  -> InterpretedValue
  -> InterpretedMap
  -> ValueSemantics
  -> InterpretedValue
makeEvaluatedIdentifierValue canonicalType form primitive underlying valueMap semantics =
  makeInterpretedValue
    canonicalType
    form
    NoInsertion
    valueMap
    (if isTotal
      then SingletonAtlasMapFederation valueMap
      else PrimitiveAtlasMapFederation primitive)
    (if isTotal
      then TotalInterpretedMap
      else NonTotalInterpretedMap)
    semantics
  where
    isTotal = interpretedValueHasTotalMap underlying
