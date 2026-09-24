-- | Proof construction for injective canonical string conversion.
--
-- The certificate combines the facts needed by string concatenation with the
-- canonical codec used by specification. Ordinary Datra constructors inherit
-- injectivity compositionally; only semantic erasures must opt out.
module Evaluation.ToString.Injectivity
  ( proveInjectiveToString
  ) where

import Data.List (nub)
import DatraLanguage.AST.Reserved qualified as Reserved
import DatraOrdinal (naturalAtOrdinal)
import Evaluation.Value
import IdentifierValueType (identifierValueCharacterAlphabet)

data StringConversionProperties = StringConversionProperties
  { conversionIsInjective :: Bool
  , conversionCharacterAlphabet :: Maybe String
  , conversionExactStrings :: Maybe [String]
  }

proveInjectiveToString
  :: (String -> [InterpretedValue])
  -> InterpretedValue
  -> Maybe ProvenInjectiveToString
proveInjectiveToString decodeCanonical source =
  let properties = stringConversionProperties (interpretedSemantics source)
  in if conversionIsInjective properties
      then
        Just
          ProvenInjectiveToString
            { injectiveToStringCharacterAlphabet =
                conversionCharacterAlphabet properties
            , injectiveToStringExactStrings =
                conversionExactStrings properties
            , invertInjectiveToString = decodeToStringMember decodeCanonical
            }
      else Nothing

stringConversionProperties
  :: ValueSemantics
  -> StringConversionProperties
stringConversionProperties semantics =
  case semantics of
    BuiltinMetaTypeSemantics _ -> unknownConversion
    FunctionSemantics {} -> unknownConversion
    ExplicitSemantics {} -> knownAlphabet "0123456789"
    IntegerSemantics {} -> knownAlphabet "-0123456789"
    NaturalRangeSemantics {} -> numericRange
    ValuedNaturalRangeSemantics {} -> numericRange
    NaturalTypeSemantics -> naturalNumber
    IntegerRangeSemantics {} -> numericRange
    ValuedIntegerRangeSemantics {} -> numericRange
    IntegerTypeSemantics -> integerNumber
    AsciiStringSemantics {} -> injectiveUnknownAlphabet
    StringTypeSemantics -> injectiveUnknownAlphabet
    IdentifierValueTypeSemantics ->
      StringConversionProperties
        True (Just identifierValueCharacterAlphabet) Nothing
    EitherSemantics left right ->
      eitherConversionProperties
        (stringConversionProperties left)
        (stringConversionProperties right)
    RangeConcatenationSemantics {} -> injectiveUnknownAlphabet
    ConcatenationSemantics members -> compositeProperties members
    DependentIdentifierTypeSemantics dependency underlying True
      | Just rendered <- reservedConstructorString dependency underlying ->
          exactStrings [rendered]
    DependentIdentifierTypeSemantics
        (SimpleIdentifierDependency _) underlying _ ->
      structuralWrapperProperties underlying
    DependentIdentifierTypeSemantics (DependentIdentifierDependency {}) _ _ ->
      unknownConversion
    -- A projection may erase the underlying member entirely: a constant
    -- identifier family maps every member to the same string, and a dependent
    -- family needs its own future proof that generated names are distinct.
    IdentifierStringProjectionSemantics {} -> unknownConversion
    ToStringSemantics source -> stringConversionProperties source
    WeakToStringSemantics _ -> unknownConversion
    StringTemplateSemantics source -> stringConversionProperties source
    AssignmentSemantics _ typeAnnotation givenValue ->
      compositeProperties [typeAnnotation, givenValue]
    MapSemantics _ components -> compositeProperties components
    ArgumentMapSemantics _ components -> compositeProperties components
    SpecificationSemantics source target ->
      compositeProperties [source, target]
    FormulationSemantics {} -> injectiveUnknownAlphabet
    RangeSemantics {} -> injectiveUnknownAlphabet
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
      StringConversionProperties True (Just alphabet) Nothing
    unknownConversion = StringConversionProperties False Nothing Nothing

    structuralWrapperProperties underlying =
      (stringConversionProperties underlying)
        { conversionCharacterAlphabet = Nothing
        , conversionExactStrings = Nothing
        }

    compositeProperties members =
      StringConversionProperties
        (all (conversionIsInjective . stringConversionProperties) members)
        Nothing
        Nothing

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
    )
    (unionMaybe unionLists
      (conversionCharacterAlphabet left)
      (conversionCharacterAlphabet right))
    (unionMaybe unionLists
      (conversionExactStrings left)
      (conversionExactStrings right))

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

decodeToStringMember
  :: (String -> [InterpretedValue])
  -> String
  -> ToStringInverseDecision
decodeToStringMember decodeCanonical characters =
  case decodeCanonical characters of
    [] -> ToStringInverseRejected
    candidates -> ToStringInverseMatched candidates
