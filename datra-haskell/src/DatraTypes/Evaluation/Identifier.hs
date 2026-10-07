-- | Evaluated dependent and constant identifier types.
module Evaluation.Identifier
  ( dependentIdentifierTypeValue
  , dependentIdentifierTemplateTypeValue
  , identifierTemplateTypeValue
  , identifierNameFederationFor
  , simpleIdentifierTypeValue
  , inferredIdentifierAssignmentValue
  , identifierStringProjectionValue
  , withTrailingIdentifierMarker
  , hasTrailingIdentifierMarker
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
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)

-- | Identifier annotations participate in canonical source syntax. A
-- noncanonical Datra type can still be named as a value, but cannot define
-- the annotated member family of an identifier.
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
    Nothing
    Nothing
    False

-- | A source-level identifier string expression evaluated with its supplied
-- specification as contextual @it@.  The already-instantiated federation is
-- retained for ordinary map access; the family evaluator is retained for
-- matching against narrower supplied specifications.
dependentIdentifierTemplateTypeValue
  :: String
  -> InterpretedValue
  -> (InterpretedValue -> Either InterpretingError InterpretedValue)
  -> InterpretedValue
  -> InterpretedValue
dependentIdentifierTemplateTypeValue familyKey nameFederation nameFamily =
  makeDependentIdentifierTypeValue
    (DependentIdentifierDependency familyKey (const familyKey))
    (Just nameFederation)
    (Just nameFamily)
    True

-- | An identifier whose spelling is selected from an ordinary string
-- federation.  The federation is retained for name admission and inversion;
-- its rendered source remains the stable dependency key.
identifierTemplateTypeValue
  :: String
  -> InterpretedValue
  -> InterpretedValue
  -> InterpretedValue
identifierTemplateTypeValue familyKey nameFederation =
  makeDependentIdentifierTypeValue
    (DependentIdentifierDependency familyKey (const familyKey))
    (Just nameFederation)
    (Just (const (Right nameFederation)))
    True

-- | Instantiate an identifier's name federation at the supplied
-- specification.  Constant identifiers and host-defined dependent identifiers
-- use the same interface as source-level string-expression families.
identifierNameFederationFor
  :: EvaluatedDependentIdentifierType
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
identifierNameFederationFor identifier supplied =
  case evaluatedIdentifierNameFamily identifier of
    Just nameFamily -> nameFamily supplied
    Nothing ->
      Right (makeAsciiString
        (identifierDependencyStringFor
          (evaluatedIdentifierDependency identifier)
          (interpretedSemanticResult supplied)))

simpleIdentifierTypeValue
  :: String
  -> InterpretedValue
  -> InterpretedValue
simpleIdentifierTypeValue identifierString underlying
  | interpretedSemanticResult underlying == CanonicalMap 0 [] =
      makeAsciiString identifierString
  | otherwise =
      makeDependentIdentifierTypeValue
        (SimpleIdentifierDependency identifierString)
        Nothing
        Nothing
        True
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

-- | Append compiler-owned metadata to an identifier's map view without
-- changing the identifier's denotation, callable form, or federation. The
-- metadata lives at the final index so import code can inspect it without
-- relying on rendered canonical syntax.
withTrailingIdentifierMarker :: String -> InterpretedValue -> InterpretedValue
withTrailingIdentifierMarker marker value
  | hasTrailingIdentifierMarker marker value = value
  | otherwise = value
      { interpretedMap = markedMap
      , interpretedTotalAtlasMap =
          case interpretedTotalAtlasMap value of
            Just _ -> Just (InterpretedTotalAtlasMap markedMap)
            Nothing -> Nothing
      }
  where
    markerValue = makeAsciiString marker
    sourceMap = interpretedMap value
    markedMap = sourceMap
      { interpretedMapPageCardinality =
          interpretedMapPageCardinality sourceMap + 1
      , interpretedMapFinalValues = appendOrdinalOrderedValues
          (interpretedMapFinalValues sourceMap)
          (singletonOrdinalOrderedValues markerValue)
      , interpretedMapComponents =
          interpretedMapComponents sourceMap
            <> [interpretedSemantics markerValue]
      }

hasTrailingIdentifierMarker :: String -> InterpretedValue -> Bool
hasTrailingIdentifierMarker marker value =
  case naturalAtOrdinal (interpretedMapFinalOrderType valueMap) of
    Just count
      | count > 0
      , Just finalValue <- interpretedMapValueAt
          valueMap (finiteOrdinal (count - 1)) ->
          interpretedSemanticResult finalValue == CanonicalAsciiString marker
    _ -> False
  where
    valueMap = interpretedMap value

identifierStringProjectionValue
  :: EvaluatedDependentIdentifierType
  -> InterpretedValue
identifierStringProjectionValue evaluated = value
  where
    dependency = evaluatedIdentifierDependency evaluated
    underlying = evaluatedIdentifierUnderlying evaluated
    underlyingResult = interpretedSemanticResult underlying
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
          else makeNonCanonicalDatraType StructuralTypeFamily)
        (IdentifierStringProjectionForm evaluated)
        (IdentifierStringProjectionAtlasMapFederation evaluated)
        isTotal
        resultMap
        semantics

makeDependentIdentifierTypeValue
  :: IdentifierDependency
  -> Maybe InterpretedValue
  -> Maybe (InterpretedValue -> Either InterpretingError InterpretedValue)
  -> Bool
  -> InterpretedValue
  -> InterpretedValue
makeDependentIdentifierTypeValue
    dependency nameFederation nameFamily isCanonical underlying = value
  where
    evaluated = EvaluatedDependentIdentifierType
      dependency underlying nameFederation nameFamily isCanonical
    underlyingResult = interpretedSemanticResult underlying
    isTotal = interpretedValueHasTotalMap underlying
      && maybe True interpretedValueHasTotalMap nameFederation
    representativeString =
      identifierDependencyRepresentativeString
        dependency
        (if isTotal then Just underlyingResult else Nothing)
    identifierStringValue = maybe
      (makeAsciiString representativeString)
      id
      nameFederation
    finalValues =
      appendOrdinalOrderedValues
        (singletonOrdinalOrderedValues identifierStringValue)
        (singletonOrdinalOrderedValues underlying)
    semantics =
      DependentIdentifierTypeSemantics
        dependency
        (interpretedSemantics underlying)
        isTotal
        isCanonical
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
        isTotal
        valueMap
        semantics
    canonicalType
      | isTotal = structuralDatraType
      | isCanonical =
          structuralTypeWithCanonicalityOf underlying
      | otherwise =
          case dependency of
            SimpleIdentifierDependency _ ->
              structuralTypeWithCanonicalityOf underlying
            DependentIdentifierDependency {} ->
              makeNonCanonicalDatraType StructuralTypeFamily
    structuralTypeWithCanonicalityOf source =
      case datraCanonicalType (interpretedDatraType source) of
        Just _ -> structuralDatraType
        Nothing -> makeNonCanonicalDatraType StructuralTypeFamily

-- | Totality is established by the caller from every component of the
-- identifier's two-position map. This is also the exact boundary between its
-- singleton and primitive federation representations.
makeEvaluatedIdentifierValue
  :: DatraType
  -> ValueForm
  -> InterpretedAtlasMapFederationPrimitive
  -> Bool
  -> InterpretedMap
  -> ValueSemantics
  -> InterpretedValue
makeEvaluatedIdentifierValue canonicalType form primitive isTotal valueMap semantics =
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
