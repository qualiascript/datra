-- | Proof construction for injective canonical string conversion.
--
-- The certificate combines the facts needed by string concatenation with the
-- inverse used by specification. Future value families extend this module
-- when their canonical representation can prove both properties.
module Evaluation.ToString.Injectivity
  ( proveInjectiveToString
  ) where

import BooleanType (DatraBoolean (..))
import Data.List (nub)
import DatraLanguage.AST.Reserved qualified as Reserved
import DatraOrdinal (naturalAtOrdinal)
import Evaluation.Construction (makeInteger, makeNatural)
import Evaluation.Value
import IdentifierValueType (identifierValueCharacterAlphabet)
import Numeric.Natural (Natural)

data StringConversionProperties = StringConversionProperties
  { conversionIsInjective :: Bool
  , conversionCharacterAlphabet :: Maybe String
  , conversionExactStrings :: Maybe [String]
  }

proveInjectiveToString
  :: InterpretedValue
  -> Maybe ProvenInjectiveToString
proveInjectiveToString source =
  let properties = stringConversionProperties (interpretedSemantics source)
  in if conversionIsInjective properties
      then
        Just
          ProvenInjectiveToString
            { injectiveToStringCharacterAlphabet =
                conversionCharacterAlphabet properties
            , injectiveToStringExactStrings =
                conversionExactStrings properties
            , invertInjectiveToString = invertToStringMember source
            }
      else Nothing

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
    IdentifierValueTypeSemantics ->
      StringConversionProperties
        True (Just identifierValueCharacterAlphabet) Nothing
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
    -- A projection may erase the underlying member entirely: a constant
    -- identifier family maps every member to the same string, and a dependent
    -- family needs its own future proof that generated names are distinct.
    IdentifierStringProjectionSemantics {} -> unknownConversion
    ToStringSemantics source -> stringConversionProperties source
    WeakToStringSemantics source ->
      (stringConversionProperties source)
        { conversionIsInjective = True }
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

invertToStringMember
  :: InterpretedValue
  -> String
  -> ToStringInverseDecision
invertToStringMember source characters =
  case interpretedForm source of
    ValuedNaturalRangeForm _ ->
      maybe ToStringInverseRejected
        (ToStringInverseMatched . makeNatural)
        (readCanonical characters :: Maybe Natural)
    ValuedIntegerRangeForm _ ->
      maybe ToStringInverseRejected
        (ToStringInverseMatched . makeInteger)
        (readCanonical characters :: Maybe Integer)
    BooleanForm flag ->
      invertReservedValue
        (case flag of
          DatraFalse -> Reserved.FalseSymbol
          DatraTrue -> Reserved.TrueSymbol)
    NothingForm -> invertReservedValue Reserved.NothingSymbol
    EitherForm alternatives ->
      combineInverseDecisions
        (invertToStringMember
          (evaluatedEitherLeft alternatives) characters)
        (invertToStringMember
          (evaluatedEitherRight alternatives) characters)
    _ -> ToStringInverseUndecidable
  where
    invertReservedValue symbol
      | characters == Reserved.reservedSymbolIdentifierString symbol =
          ToStringInverseMatched source
      | otherwise = ToStringInverseRejected

combineInverseDecisions
  :: ToStringInverseDecision
  -> ToStringInverseDecision
  -> ToStringInverseDecision
combineInverseDecisions
    (ToStringInverseMatched candidate)
    ToStringInverseRejected = ToStringInverseMatched candidate
combineInverseDecisions
    ToStringInverseRejected
    (ToStringInverseMatched candidate) = ToStringInverseMatched candidate
combineInverseDecisions ToStringInverseRejected ToStringInverseRejected =
  ToStringInverseRejected
combineInverseDecisions
    (ToStringInverseMatched candidate)
    ToStringInverseUndecidable = ToStringInverseMatched candidate
combineInverseDecisions
    ToStringInverseUndecidable
    (ToStringInverseMatched candidate) = ToStringInverseMatched candidate
combineInverseDecisions _ _ = ToStringInverseUndecidable

readCanonical :: (Read value, Show value) => String -> Maybe value
readCanonical characters =
  case reads characters of
    [(value, "")]
      | show value == characters -> Just value
    _ -> Nothing
