-- | Evaluated dependent and constant identifier types.
module Evaluation.Identifier
  ( identifierTypeValue
  , simpleIdentifierTypeValue
  , identifierStringProjectionValue
  , identifierDependencyStringFor
  , identifierDependenciesCompatible
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
  makeIdentifierType
    (DependentIdentifierDependency familyKey identifierStringFor)

simpleIdentifierTypeValue
  :: String
  -> InterpretedValue
  -> InterpretedValue
simpleIdentifierTypeValue identifierString =
  makeIdentifierType (SimpleIdentifierDependency identifierString)

identifierStringProjectionValue
  :: EvaluatedIdentifierType
  -> InterpretedValue
identifierStringProjectionValue evaluated = value
  where
    dependency = evaluatedIdentifierDependency evaluated
    underlying = evaluatedIdentifierUnderlying evaluated
    representativeString =
      case dependency of
        SimpleIdentifierDependency identifierString -> identifierString
        DependentIdentifierDependency familyKey identifierStringFor
          | interpretedValueHasTotalMap underlying ->
              identifierStringFor (interpretedCanonicalResult underlying)
          | otherwise -> familyKey
    representative = makeAsciiString representativeString
    semantics =
      IdentifierStringProjectionSemantics
        dependency
        (interpretedSemantics underlying)
        (interpretedValueHasTotalMap underlying)
    resultMap =
      (interpretedMap representative)
        { interpretedMapComponents = [semantics] }
    federation
      | interpretedValueHasTotalMap underlying =
          SingletonAtlasMapFederation resultMap
      | otherwise =
          PrimitiveAtlasMapFederation
            (IdentifierStringProjectionAtlasMapFederation evaluated)
    value =
      makeInterpretedValue
        (IdentifierStringProjectionForm evaluated)
        NoInsertion
        resultMap
        federation
        (if interpretedValueHasTotalMap underlying
          then TotalInterpretedMap
          else NonTotalInterpretedMap)
        semantics

makeIdentifierType
  :: IdentifierDependency
  -> InterpretedValue
  -> InterpretedValue
makeIdentifierType dependency underlying = value
  where
    evaluated = EvaluatedIdentifierType dependency underlying
    representativeString =
      case dependency of
        SimpleIdentifierDependency identifierString -> identifierString
        DependentIdentifierDependency familyKey identifierStringFor
          | interpretedValueHasTotalMap underlying ->
              identifierStringFor (interpretedCanonicalResult underlying)
          | otherwise -> familyKey
    identifierStringValue = makeAsciiString representativeString
    finalValues =
      appendOrdinalOrderedValues
        (singletonOrdinalOrderedValues identifierStringValue)
        (singletonOrdinalOrderedValues underlying)
    semantics =
      IdentifierTypeSemantics
        dependency
        (interpretedSemantics underlying)
        (interpretedValueHasTotalMap underlying)
    valueMap =
      InterpretedMap
        2
        finalValues
        [ interpretedSemantics identifierStringValue
        , interpretedSemantics underlying
        ]
    federation
      | interpretedValueHasTotalMap underlying =
          SingletonAtlasMapFederation valueMap
      | otherwise =
          PrimitiveAtlasMapFederation
            (IdentifierTypeAtlasMapFederation evaluated)
    value =
      makeInterpretedValue
        (IdentifierTypeForm evaluated)
        NoInsertion
        valueMap
        federation
        (if interpretedValueHasTotalMap underlying
          then TotalInterpretedMap
          else NonTotalInterpretedMap)
        semantics

identifierDependencyStringFor
  :: IdentifierDependency
  -> CanonicalResult
  -> String
identifierDependencyStringFor dependency value =
  case dependency of
    SimpleIdentifierDependency identifierString -> identifierString
    DependentIdentifierDependency _ identifierStringFor ->
      identifierStringFor value

-- | Constant dependencies agree by identifier string. Dependent dependencies are
-- comparable when they carry the same stable family key.
identifierDependenciesCompatible
  :: IdentifierDependency
  -> IdentifierDependency
  -> Bool
identifierDependenciesCompatible left right =
  case (left, right) of
    (SimpleIdentifierDependency leftString,
      SimpleIdentifierDependency rightString) ->
        leftString == rightString
    (DependentIdentifierDependency leftKey _,
      DependentIdentifierDependency rightKey _) ->
        leftKey == rightKey
    _ -> False
