-- | Evaluated dependent and constant identifier types.
module Evaluation.Identifier
  ( identifierTypeValue
  , simpleIdentifierTypeValue
  , identifierNameProjectionValue
  , identifierDependencyNameFor
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
identifierTypeValue key nameFor =
  makeIdentifierType (DependentIdentifierDependency key nameFor)

simpleIdentifierTypeValue
  :: String
  -> InterpretedValue
  -> InterpretedValue
simpleIdentifierTypeValue name =
  makeIdentifierType (SimpleIdentifierDependency name)

identifierNameProjectionValue
  :: EvaluatedIdentifierType
  -> InterpretedValue
identifierNameProjectionValue evaluated = value
  where
    dependency = evaluatedIdentifierDependency evaluated
    underlying = evaluatedIdentifierUnderlying evaluated
    representativeName =
      case dependency of
        SimpleIdentifierDependency name -> name
        DependentIdentifierDependency key nameFor
          | interpretedValueHasTotalMap underlying ->
              nameFor (interpretedCanonicalResult underlying)
          | otherwise -> key
    representative = makeAsciiString representativeName
    semantics =
      IdentifierNameProjectionSemantics
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
            (IdentifierNameProjectionAtlasMapFederation evaluated)
    value =
      makeInterpretedValue
        (IdentifierNameProjectionForm evaluated)
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
    representativeName =
      case dependency of
        SimpleIdentifierDependency name -> name
        DependentIdentifierDependency key nameFor
          | interpretedValueHasTotalMap underlying ->
              nameFor (interpretedCanonicalResult underlying)
          | otherwise -> key
    nameValue = makeAsciiString representativeName
    finalValues =
      appendOrdinalOrderedValues
        (singletonOrdinalOrderedValues nameValue)
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
        [interpretedSemantics nameValue, interpretedSemantics underlying]
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

identifierDependencyNameFor
  :: IdentifierDependency
  -> CanonicalResult
  -> String
identifierDependencyNameFor dependency value =
  case dependency of
    SimpleIdentifierDependency name -> name
    DependentIdentifierDependency _ nameFor -> nameFor value

-- | Constant dependencies agree by name. Dependent dependencies are
-- comparable when they carry the same stable family key.
identifierDependenciesCompatible
  :: IdentifierDependency
  -> IdentifierDependency
  -> Bool
identifierDependenciesCompatible left right =
  case (left, right) of
    (SimpleIdentifierDependency leftName,
      SimpleIdentifierDependency rightName) ->
        leftName == rightName
    (DependentIdentifierDependency leftKey _,
      DependentIdentifierDependency rightKey _) ->
        leftKey == rightKey
    _ -> False
