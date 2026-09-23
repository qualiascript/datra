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
import Data.List (isInfixOf, nub)
import DatraLanguage.AST.Reserved qualified as Reserved
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
    StringTemplateForm _ -> Right source
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
  , conversionExactStrings :: Maybe [String]
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
    EitherSemantics left right ->
      eitherConversionProperties
        (stringConversionProperties left)
        (stringConversionProperties right)
    IdentifierTypeSemantics dependency underlying True
      | Just rendered <- reservedConstructorString dependency underlying ->
          exactStrings [rendered]
    IdentifierTypeSemantics _ underlying _ ->
      (stringConversionProperties underlying)
        { conversionCharacterAlphabet = Nothing
        , conversionExactStrings = Nothing
        }
    IdentifierStringProjectionSemantics _ underlying _ ->
      (stringConversionProperties underlying)
        { conversionCharacterAlphabet = Nothing
        , conversionExactStrings = Nothing
        }
    ToStringSemantics source -> stringConversionProperties source
    StringTemplateSemantics source -> stringConversionProperties source
    _ -> unknownConversion
  where
    naturalNumber =
      StringConversionProperties True (Just "0123456789") Nothing
    integerNumber =
      StringConversionProperties True (Just "-0123456789") Nothing
    numericRange =
      StringConversionProperties
        True (Just " -0123456789.rangeftoupwds") Nothing
    injectiveUnknownAlphabet =
      StringConversionProperties True Nothing Nothing
    knownAlphabet alphabet =
      StringConversionProperties False (Just alphabet) Nothing
    unknownConversion = StringConversionProperties False Nothing Nothing

reservedConstructorString
  :: IdentifierDependency
  -> ValueSemantics
  -> Maybe String
reservedConstructorString dependency underlying =
  case (dependency, underlying) of
    (SimpleIdentifierDependency "False", ExplicitSemantics 1 ordinalValue)
      | naturalAtOrdinal ordinalValue == Just 0 ->
          reserved Reserved.FalseSymbol
    (SimpleIdentifierDependency "True", ExplicitSemantics 1 ordinalValue)
      | naturalAtOrdinal ordinalValue == Just 1 ->
          reserved Reserved.TrueSymbol
    (SimpleIdentifierDependency "Nothing", MapSemantics 0 []) ->
      reserved Reserved.NothingSymbol
    _ -> Nothing
  where
    reserved = Just . Reserved.reservedSymbolIdentifierString

eitherConversionProperties
  :: StringConversionProperties
  -> StringConversionProperties
  -> StringConversionProperties
eitherConversionProperties left right =
  StringConversionProperties
    ( conversionIsInjective left
        && conversionIsInjective right
        && conversionLanguagesAreDisjoint left right
    )
    (unionMaybe unionLists
      (conversionCharacterAlphabet left)
      (conversionCharacterAlphabet right))
    (unionMaybe unionLists
      (conversionExactStrings left)
      (conversionExactStrings right))

conversionLanguagesAreDisjoint
  :: StringConversionProperties
  -> StringConversionProperties
  -> Bool
conversionLanguagesAreDisjoint left right =
  case (conversionExactStrings left, conversionExactStrings right) of
    (Just leftStrings, Just rightStrings) ->
      all (`notElem` rightStrings) leftStrings
    (Just leftStrings, Nothing) ->
      case conversionCharacterAlphabet right of
        Just alphabet -> all (stringExcludedByAlphabet alphabet) leftStrings
        Nothing -> False
    (Nothing, Just rightStrings) ->
      case conversionCharacterAlphabet left of
        Just alphabet -> all (stringExcludedByAlphabet alphabet) rightStrings
        Nothing -> False
    (Nothing, Nothing) -> False

stringExcludedByAlphabet :: String -> String -> Bool
stringExcludedByAlphabet alphabet = any (`notElem` alphabet)

exactStrings :: [String] -> StringConversionProperties
exactStrings strings =
  StringConversionProperties
    True
    (Just (nub (concat strings)))
    (Just strings)

unionMaybe
  :: (value -> value -> value)
  -> Maybe value
  -> Maybe value
  -> Maybe value
unionMaybe combine (Just left) (Just right) = Just (combine left right)
unionMaybe _ _ _ = Nothing

unionLists :: Eq value => [value] -> [value] -> [value]
unionLists left right = nub (left <> right)

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
        ToStringAtlasMapFederation source ->
          conversionExactStrings
            (stringConversionProperties (interpretedSemantics source))
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
