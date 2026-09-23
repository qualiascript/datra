-- | Internal pointwise conversion used by string-template interpolation.
-- There is deliberately no surface-language name for this operation.
module Evaluation.ToString
  ( toStringValue
  , weakToStringValue
  , stringTemplateValue
  , stringFederationConcatenationIsInjective
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (..)
  )
import Data.List (isInfixOf, nub)
import Evaluation.Construction (makeAsciiString)
import Evaluation.Error
  ( InterpretingError (NonInjectiveStringInterpolation) )
import Evaluation.ToString.Injectivity (proveInjectiveToString)
import Evaluation.Value

-- | Convert a total value to its canonical source spelling, or retain a
-- pointwise string-federation map for a non-total value. Strings are identity
-- values so their source delimiters never become data.
toStringValue
  :: (CanonicalResult -> String)
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
toStringValue renderCanonical source =
  case interpretedForm source of
    AsciiStringForm _ -> Right source
    StringTypeForm -> Right source
    ToStringForm -> Right source
    WeakToStringForm -> Right source
    StringTemplateForm _ -> Right source
    _
      | interpretedValueHasTotalMap source ->
          Right
            (makeAsciiString
              (renderCanonical (interpretedCanonicalResult source)))
      | otherwise ->
          case proveInjectiveToString source of
            Just proof -> Right (pointwiseFederation proof)
            Nothing -> Left NonInjectiveStringInterpolation
  where
    pointwiseFederation proof =
      makeInterpretedValue
        ToStringForm
        NoInsertion
        emptyInterpretedMap
        (PrimitiveAtlasMapFederation
          (ToStringAtlasMapFederation source proof))
        NonTotalInterpretedMap
        (ToStringSemantics (interpretedSemantics source))

-- | Use the ordinary injective conversion whenever it is available. Only an
-- unprovable conversion constructs the explicitly non-invertible weak form.
weakToStringValue
  :: (CanonicalResult -> String)
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
weakToStringValue renderCanonical source =
  case toStringValue renderCanonical source of
    Right value -> Right value
    Left NonInjectiveStringInterpolation ->
      Right
        (makeInterpretedValue
          WeakToStringForm
          NoInsertion
          emptyInterpretedMap
          (PrimitiveAtlasMapFederation
            (WeakToStringAtlasMapFederation source))
          NonTotalInterpretedMap
          (WeakToStringSemantics (interpretedSemantics source)))
    Left err -> Left err

-- | Retain the ordinary concatenation result while recording that its members
-- are the pointwise outputs of one string template.
stringTemplateValue :: InterpretedValue -> InterpretedValue
stringTemplateValue value =
  case interpretedForm value of
    AsciiStringForm _ -> value
    StringTypeForm -> value
    ToStringForm -> value
    WeakToStringForm -> value
    StringTemplateForm _ -> value
    _ ->
      makeInterpretedValue
        (StringTemplateForm value)
        (interpretedInsertionCapability value)
        (interpretedMap value)
        (interpretedAtlasMapFederation value)
        (if interpretedValueHasTotalMap value
          then TotalInterpretedMap
          else NonTotalInterpretedMap)
        (StringTemplateSemantics (interpretedSemantics value))

-- | Decide the string-specific case omitted by generic Atlas federation
-- concatenation: a fixed nonempty delimiter makes the product injective when
-- at least one adjacent variable side excludes it.
stringFederationConcatenationIsInjective
  :: InterpretedAtlasMapFederation
  -> InterpretedAtlasMapFederation
  -> Bool
stringFederationConcatenationIsInjective left right =
  finiteLanguagesAreInjective
    || trailingBoundaryIsInjective
    || leadingBoundaryIsInjective
  where
    finiteLanguagesAreInjective =
      case (federationExactStrings left, federationExactStrings right) of
        (Just leftStrings, Just rightStrings) ->
          let concatenations =
                [leftString <> rightString
                | leftString <- leftStrings
                , rightString <- rightStrings
                ]
          in length concatenations == length (nub concatenations)
        _ -> False
    trailingBoundaryIsInjective =
      case trailingStringDelimiter left of
        Just (prefix, delimiter) ->
          not (null delimiter)
            && ( stringFederationExcludes delimiter prefix
                  || stringFederationExcludes delimiter right
               )
        Nothing -> False
    leadingBoundaryIsInjective =
      case leadingStringDelimiter right of
        Just (delimiter, suffix) ->
          not (null delimiter)
            && ( stringFederationExcludes delimiter left
                  || stringFederationExcludes delimiter suffix
               )
        Nothing -> False

federationExactStrings
  :: InterpretedAtlasMapFederation
  -> Maybe [String]
federationExactStrings federation =
  case federation of
    SingletonAtlasMapFederation valueMap ->
      case interpretedMapComponents valueMap of
        [AsciiStringSemantics characters] -> Just [characters]
        _ -> Nothing
    PrimitiveAtlasMapFederation primitive ->
      case primitive of
        ToStringAtlasMapFederation _ proof ->
          injectiveToStringExactStrings proof
        WeakToStringAtlasMapFederation _ -> Nothing
        _ -> Nothing
    ConcatenatedAtlasMapFederation left right -> do
      leftStrings <- federationExactStrings left
      rightStrings <- federationExactStrings right
      pure
        [leftString <> rightString
        | leftString <- leftStrings
        , rightString <- rightStrings
        ]
    SequentialAtlasMapFederation _ -> Nothing
    ExpansionAtlasMapFederation _ _ -> Nothing

trailingStringDelimiter
  :: InterpretedAtlasMapFederation
  -> Maybe (InterpretedAtlasMapFederation, String)
trailingStringDelimiter
    (ConcatenatedAtlasMapFederation left right) =
      (\delimiter -> (left, delimiter)) <$> singletonAsciiString right
trailingStringDelimiter _ = Nothing

leadingStringDelimiter
  :: InterpretedAtlasMapFederation
  -> Maybe (String, InterpretedAtlasMapFederation)
leadingStringDelimiter
    (ConcatenatedAtlasMapFederation left right) =
      (\delimiter -> (delimiter, right)) <$> singletonAsciiString left
leadingStringDelimiter _ = Nothing

singletonAsciiString
  :: InterpretedAtlasMapFederation
  -> Maybe String
singletonAsciiString (SingletonAtlasMapFederation valueMap) =
  case interpretedMapComponents valueMap of
    [AsciiStringSemantics characters] -> Just characters
    _ -> Nothing
singletonAsciiString _ = Nothing

stringFederationExcludes
  :: String
  -> InterpretedAtlasMapFederation
  -> Bool
stringFederationExcludes delimiter federation =
  case federation of
    SingletonAtlasMapFederation valueMap ->
      case interpretedMapComponents valueMap of
        [AsciiStringSemantics characters] ->
          not (delimiter `isInfixOf` characters)
        _ -> False
    PrimitiveAtlasMapFederation primitive ->
      case primitive of
        ToStringAtlasMapFederation _ proof ->
          case injectiveToStringCharacterAlphabet proof of
            Nothing -> False
            Just alphabet -> any (`notElem` alphabet) delimiter
        WeakToStringAtlasMapFederation _ -> False
        StringTypeAtlasMapFederation -> False
        _ -> False
    SequentialAtlasMapFederation members ->
      all (stringFederationExcludes delimiter) members
    ExpansionAtlasMapFederation leftValue rightValue ->
      stringFederationExcludes delimiter leftValue
        && stringFederationExcludes delimiter rightValue
    ConcatenatedAtlasMapFederation leftValue rightValue ->
      stringFederationExcludes delimiter leftValue
        && stringFederationExcludes delimiter rightValue
