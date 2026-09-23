-- | Internal pointwise conversion used by string-template interpolation.
-- There is deliberately no surface-language name for this operation.
module Evaluation.ToString
  ( toStringValue
  , stringTemplateValue
  , stringFederationConcatenationIsInjective
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (..)
  )
import Data.List (isInfixOf)
import DatraOrdinal (naturalAtOrdinal)
import Evaluation.Construction (makeAsciiString)
import Evaluation.Error (InterpretingError (AmbiguousStringTemplate))
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
    StringTemplateForm -> Right source
    _
      | interpretedValueHasTotalMap source ->
          Right
            (makeAsciiString
              (renderCanonical (interpretedCanonicalResult source)))
      | toStringConversionIsInjective (interpretedSemantics source) ->
          Right pointwiseFederation
      | otherwise -> Left AmbiguousStringTemplate
  where
    pointwiseFederation =
      makeInterpretedValue
        ToStringForm
        NoInsertion
        emptyInterpretedMap
        (PrimitiveAtlasMapFederation
          (ToStringAtlasMapFederation source))
        NonTotalInterpretedMap
        (ToStringSemantics (interpretedSemantics source))

data StringConversionProperties = StringConversionProperties
  { conversionIsInjective :: Bool
  , conversionCharacterAlphabet :: Maybe String
  }

stringConversionProperties
  :: ValueSemantics
  -> StringConversionProperties
stringConversionProperties semantics =
  case semantics of
    ExplicitSemantics {} -> knownAlphabet "0123456789"
    IntegerSemantics {} -> knownAlphabet "-0123456789"
    NaturalRangeSemantics {} -> numericRange
    ValuedNaturalRangeSemantics {} -> numericRange
    NaturalTypeSemantics -> naturalNumber
    IntegerRangeSemantics {} -> numericRange
    ValuedIntegerRangeSemantics {} -> numericRange
    IntegerTypeSemantics -> integerNumber
    StringTypeSemantics -> injectiveUnknownAlphabet
    EitherSemantics left right
      | isBooleanPair left right ->
          StringConversionProperties True (Just "falsetru")
    IdentifierTypeSemantics _ underlying _ ->
      (stringConversionProperties underlying)
        { conversionCharacterAlphabet = Nothing }
    IdentifierStringProjectionSemantics _ underlying _ ->
      (stringConversionProperties underlying)
        { conversionCharacterAlphabet = Nothing }
    ToStringSemantics source -> stringConversionProperties source
    _ -> unknownConversion
  where
    isBooleanPair left right =
      case (booleanConstructor left, booleanConstructor right) of
        (Just False, Just True) -> True
        (Just True, Just False) -> True
        _ -> False

    booleanConstructor semanticsValue =
      case semanticsValue of
        IdentifierTypeSemantics
            (SimpleIdentifierDependency identifier)
            (ExplicitSemantics 1 ordinalValue)
            True
          | identifier == "False"
          , naturalAtOrdinal ordinalValue == Just 0 -> Just False
          | identifier == "True"
          , naturalAtOrdinal ordinalValue == Just 1 -> Just True
        _ -> Nothing

    naturalNumber =
      StringConversionProperties True (Just "0123456789")
    integerNumber =
      StringConversionProperties True (Just "-0123456789")
    numericRange =
      StringConversionProperties
        True (Just " -0123456789.rangeftoupwds")
    injectiveUnknownAlphabet = StringConversionProperties True Nothing
    knownAlphabet = StringConversionProperties False . Just
    unknownConversion = StringConversionProperties False Nothing

toStringConversionIsInjective :: ValueSemantics -> Bool
toStringConversionIsInjective =
  conversionIsInjective . stringConversionProperties

-- | Retain the ordinary concatenation result while recording that its members
-- are the pointwise outputs of one string template.
stringTemplateValue :: InterpretedValue -> InterpretedValue
stringTemplateValue value =
  case interpretedForm value of
    AsciiStringForm _ -> value
    StringTypeForm -> value
    ToStringForm -> value
    StringTemplateForm -> value
    _ ->
      makeInterpretedValue
        StringTemplateForm
        (interpretedInsertionCapability value)
        (interpretedMap value)
        (interpretedAtlasMapFederation value)
        (if interpretedValueHasTotalMap value
          then TotalInterpretedMap
          else NonTotalInterpretedMap)
        (interpretedSemantics value)

-- | Decide the string-specific case omitted by generic Atlas federation
-- concatenation: a fixed nonempty delimiter makes the product injective when
-- at least one adjacent variable side excludes it.
stringFederationConcatenationIsInjective
  :: InterpretedAtlasMapFederation
  -> InterpretedAtlasMapFederation
  -> Bool
stringFederationConcatenationIsInjective left right =
  trailingBoundaryIsInjective || leadingBoundaryIsInjective
  where
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
        ToStringAtlasMapFederation source ->
          renderedSemanticsExclude
            delimiter (interpretedSemantics source)
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

renderedSemanticsExclude :: String -> ValueSemantics -> Bool
renderedSemanticsExclude delimiter semantics =
  case conversionCharacterAlphabet (stringConversionProperties semantics) of
    Nothing -> False
    Just alphabet -> any (`notElem` alphabet) delimiter
