-- | Evaluated dependent and constant identifier types.
module Evaluation.Identifier
  ( identifierTypeValue
  , simpleIdentifierTypeValue
  , identifierStringProjectionValue
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression
      ( PrimitiveAtlasMapFederation
      , SingletonAtlasMapFederation
      )
  )
import Evaluation.Construction (makeAsciiString)
import Evaluation.Value

identifierTypeValue
  :: String
  -> (CanonicalResult -> String)
  -> InterpretedValue
  -> InterpretedValue
identifierTypeValue familyKey identifierStringFor =
  makeIdentifierTypeValue
    (DependentIdentifierDependency familyKey identifierStringFor)

simpleIdentifierTypeValue
  :: String
  -> InterpretedValue
  -> InterpretedValue
simpleIdentifierTypeValue identifierString underlying
  | interpretedCanonicalResult underlying == CanonicalMap 0 [] =
      makeAsciiString identifierString
  | otherwise =
      makeIdentifierTypeValue
        (SimpleIdentifierDependency identifierString)
        underlying

identifierStringProjectionValue
  :: EvaluatedIdentifierType
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
        (IdentifierStringProjectionForm evaluated)
        (IdentifierStringProjectionAtlasMapFederation evaluated)
        underlying
        resultMap
        semantics

makeIdentifierTypeValue
  :: IdentifierDependency
  -> InterpretedValue
  -> InterpretedValue
makeIdentifierTypeValue dependency underlying = value
  where
    evaluated = EvaluatedIdentifierType dependency underlying
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
      IdentifierTypeSemantics
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
        (IdentifierTypeForm evaluated)
        (IdentifierTypeAtlasMapFederation evaluated)
        underlying
        valueMap
        semantics

-- | Identifier types and their string projections preserve the totality of
-- the underlying value. This is also the exact boundary between their
-- singleton and primitive federation representations.
makeEvaluatedIdentifierValue
  :: ValueForm
  -> InterpretedAtlasMapFederationPrimitive
  -> InterpretedValue
  -> InterpretedMap
  -> ValueSemantics
  -> InterpretedValue
makeEvaluatedIdentifierValue form primitive underlying valueMap semantics =
  makeInterpretedValue
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
