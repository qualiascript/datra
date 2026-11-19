-- | Evaluated dependent and constant identifier types.
module Evaluation.Identifier
  ( dependentArgumentTypeValue
  , dependentArgumentTemplateTypeValue
  , identifierTemplateTypeValue
  , identifierNameFederationFor
  , identifierValueAtUnderlying
  , evaluatedIdentifierType
  , simpleIdentifierName
  , identifierUnderlyingValue
  , privateSimpleIdentifier
  , privateIdentifierUnderlying
  , simpleIdentifierTypeValue
  , integerComplementValue
  , inferredIdentifierAssignmentValue
  , identifierStringProjectionValue
  , canonicalValueMarker
  , definitionMarker
  , withTrailingIdentifierMarker
  , hasTrailingIdentifierMarker
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression
      ( PrimitiveAtlasMapFederation
      , SingletonAtlasMapFederation
      )
  )
import Evaluation.Construction (makeAsciiString)
import Evaluation.Error (InterpretingError)
import Evaluation.Value
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import DatraLanguage.Identifier (isPrivateIdentifier)

-- | Compiler-owned metadata identifying an identifier whose declared name is
-- its canonical presentation.
canonicalValueMarker :: String
canonicalValueMarker = "val"

-- | Compiler-owned metadata identifying a declaration whose binding cannot
-- be replaced inconsistently by an overlapping declaration.
definitionMarker :: String
definitionMarker = "def"

evaluatedIdentifierType
  :: InterpretedValue
  -> Maybe EvaluatedDependentArgumentType
evaluatedIdentifierType value =
  case interpretedForm value of
    DependentArgumentTypeForm identifier -> Just identifier
    IdentifierStringProjectionForm identifier -> Just identifier
    AssignmentForm specification ->
      evaluatedIdentifierType (evaluatedSpecificationTarget specification)
    SpecificationForm specification ->
      evaluatedIdentifierType (evaluatedSpecificationTarget specification)
    _ -> Nothing

simpleIdentifierName :: InterpretedValue -> Maybe String
simpleIdentifierName = interpretedSimpleIdentifierName

identifierUnderlyingValue :: InterpretedValue -> Maybe InterpretedValue
identifierUnderlyingValue value =
  evaluatedIdentifierUnderlying <$> evaluatedIdentifierType value

privateSimpleIdentifier :: EvaluatedDependentArgumentType -> Bool
privateSimpleIdentifier identifier =
  case evaluatedIdentifierDependency identifier of
    SimpleIdentifierDependency name -> isPrivateIdentifier name
    DependentArgumentDependency {} -> False

privateIdentifierUnderlying :: InterpretedValue -> Maybe InterpretedValue
privateIdentifierUnderlying value = do
  identifier <- evaluatedIdentifierType value
  if privateSimpleIdentifier identifier
    then Just (evaluatedIdentifierUnderlying identifier)
    else Nothing

dependentArgumentTypeValue
  :: String
  -> (CanonicalResult -> String)
  -> InterpretedValue
  -> InterpretedValue
dependentArgumentTypeValue familyKey identifierStringFor =
  makeDependentArgumentTypeValue
    (DependentArgumentDependency familyKey identifierStringFor)
    Nothing
    Nothing
    False

-- | A source-level identifier string expression evaluated with its supplied
-- specification as contextual @it@.  The already-instantiated federation is
-- retained for ordinary map access; the family evaluator is retained for
-- matching against narrower supplied specifications.
dependentArgumentTemplateTypeValue
  :: String
  -> InterpretedValue
  -> (InterpretedValue -> Either InterpretingError InterpretedValue)
  -> InterpretedValue
  -> InterpretedValue
dependentArgumentTemplateTypeValue familyKey nameFederation nameFamily =
  makeDependentArgumentTypeValue
    (DependentArgumentDependency familyKey (const familyKey))
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
  makeDependentArgumentTypeValue
    (DependentArgumentDependency familyKey (const familyKey))
    (Just nameFederation)
    (Just (const (Right nameFederation)))
    True

-- | Instantiate an identifier's name federation at the supplied
-- specification.  Constant identifiers and host-defined dependent arguments
-- use the same interface as source-level string-expression families.
identifierNameFederationFor
  :: EvaluatedDependentArgumentType
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

-- | Select one underlying member of an identifier family without erasing
-- the identifier that distinguishes that member. Canonical aliases are
-- resolved before reaching this operation; values that still have an
-- identifier form therefore denote identifier-family members themselves.
identifierValueAtUnderlying
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe InterpretedValue
identifierValueAtUnderlying family underlying = do
  identifier <- evaluatedIdentifierType family
  isCanonical <- case interpretedSemanticSemantics family of
    DependentArgumentTypeSemantics _ _ _ canonical -> Just canonical
    _ -> Nothing
  nameFederation <- case evaluatedIdentifierDependency identifier of
    SimpleIdentifierDependency _ ->
      Just (evaluatedIdentifierNameFederation identifier)
    DependentArgumentDependency {} ->
      Just (either (const Nothing) Just
        (identifierNameFederationFor identifier underlying))
  pure (makeDependentArgumentTypeValue
    (evaluatedIdentifierDependency identifier)
    nameFederation
    (evaluatedIdentifierNameFamily identifier)
    isCanonical
    underlying)

simpleIdentifierTypeValue
  :: String
  -> InterpretedValue
  -> InterpretedValue
simpleIdentifierTypeValue identifierString underlying =
  makeDependentArgumentTypeValue
    (SimpleIdentifierDependency identifierString)
    Nothing
    Nothing
    True
    underlying

-- | The ordinary Datra value selecting the complemented half of Int/IntLimit.
-- Numerical construction depends on this typed constructor, not on its
-- identifier spellings.
integerComplementValue :: InterpretedValue
integerComplementValue =
  simpleIdentifierTypeValue "Just" (makeAsciiString "Complement")

-- | An inferred assignment may bind a non-total value such as a type.  Its
-- federation remains the dependent argument family, while its canonical
-- presentation records that the value was explicitly supplied.
inferredIdentifierAssignmentValue
  :: String
  -> InterpretedValue
  -> InterpretedValue
inferredIdentifierAssignmentValue identifierString underlying =
  (makeDependentArgumentTypeValue
      (SimpleIdentifierDependency identifierString)
      Nothing
      Nothing
      True
      underlying)
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
  | otherwise = marked
  where
    marked = value
      { interpretedMap = markedMap
      , interpretedTotalAtlasMap =
          case interpretedTotalAtlasMap value of
            Just _ -> Just (InterpretedTotalAtlasMap markedMap)
            Nothing -> Nothing
      }
    markerValue = makeAsciiString marker
    sourceMap = interpretedMap value
    markedMap = sourceMap
      { interpretedMapPageCardinality =
          interpretedMapPageCardinality sourceMap + 1
      , interpretedMapFinalValues = markedFinalValues
      , interpretedMapCheckedValueAt =
          Right . ordinalOrderedValueAt markedFinalValues
      , interpretedMapComponents =
          interpretedMapComponents sourceMap
            <> [interpretedSemantics markerValue]
      }
    markedFinalValues = appendOrdinalOrderedValues
      (interpretedMapFinalValues sourceMap)
      (singletonOrdinalOrderedValues markerValue)

hasTrailingIdentifierMarker :: String -> InterpretedValue -> Bool
hasTrailingIdentifierMarker marker value =
  case naturalAtOrdinal (interpretedMapFinalOrderType valueMap) of
    Just count
      | count > 0
      , Just finalValue <- interpretedMapValueAt
          valueMap (finiteOrdinal (count - 1)) ->
          case interpretedForm finalValue of
            AsciiStringForm found -> found == marker
            _ -> False
    _ -> False
  where
    valueMap = interpretedMap value

identifierStringProjectionValue
  :: EvaluatedDependentArgumentType
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
        structuralDatraType
        (IdentifierStringProjectionForm evaluated)
        (IdentifierStringProjectionAtlasMapFederation evaluated)
        isTotal
        resultMap
        semantics

makeDependentArgumentTypeValue
  :: IdentifierDependency
  -> Maybe InterpretedValue
  -> Maybe (InterpretedValue -> Either InterpretingError InterpretedValue)
  -> Bool
  -> InterpretedValue
  -> InterpretedValue
makeDependentArgumentTypeValue
    dependency nameFederation nameFamily isCanonical underlying = value
  where
    evaluated = EvaluatedDependentArgumentType
      dependency underlying nameFederation nameFamily
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
      DependentArgumentTypeSemantics
        dependency
        (interpretedSemantics underlying)
        isTotal
        isCanonical
    valueMap =
      InterpretedMap
        2
        finalValues
        (Right . ordinalOrderedValueAt finalValues)
        [ interpretedSemantics identifierStringValue
        , interpretedSemantics underlying
        ]
    base =
      makeEvaluatedIdentifierValue
        canonicalType
        (DependentArgumentTypeForm evaluated)
        (DependentArgumentTypeAtlasMapFederation evaluated)
        isTotal
        valueMap
        semantics
    value = base
    canonicalType = structuralDatraType

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
