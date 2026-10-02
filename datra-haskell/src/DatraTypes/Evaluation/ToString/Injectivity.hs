-- | Proof construction for injective canonical string conversion.
--
-- The certificate combines the facts needed by string concatenation with the
-- canonical codec used by specification. Ordinary Datra constructors inherit
-- injectivity compositionally; only semantic erasures must opt out.
module Evaluation.ToString.Injectivity
  ( proveInjectiveToString
  ) where

import Data.List (isInfixOf, nub)
import DatraLanguage.AST.Reserved qualified as Reserved
import DatraOrdinal (naturalAtOrdinal)
import Evaluation.Value
import Evaluation.Numerical
  ( complementedIntegerTypeIncludesInfinity )
import IdentifierValueType (identifierValueCharacterAlphabet)

data StringConversionProperties = StringConversionProperties
  { conversionIsInjective :: Bool
  , conversionCharacterAlphabet :: Maybe String
  , conversionExactStrings :: Maybe [String]
  , conversionExcludesSubstring :: String -> Bool
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
            , injectiveToStringExcludesSubstring =
                conversionExcludesSubstring properties
            , invertInjectiveToString = decodeToStringMember decodeCanonical
            }
      else Nothing

stringConversionProperties
  :: ValueSemantics
  -> StringConversionProperties
stringConversionProperties semantics
  | Just includesInfinity <-
      complementedIntegerTypeIncludesInfinity semantics =
      complementedIntegerProperties includesInfinity
  | otherwise = case semantics of
    BuiltinMetaTypeSemantics AnyMetaType -> injectiveUnknownAlphabet
    BuiltinMetaTypeSemantics TemplateMetaType -> injectiveUnknownAlphabet
    BuiltinMetaTypeSemantics _ -> unknownConversion
    FunctionSemantics {} -> injectiveUnknownAlphabet
    ExplicitSemantics {} -> knownAlphabet "0123456789"
    IntegerSemantics {} -> knownAlphabet "-0123456789"
    NaturalRangeSemantics {} -> numericRange
    ValuedNaturalRangeSemantics {} -> naturalNumber
    NaturalTypeSemantics -> naturalNumber
    IntegerRangeSemantics {} -> numericRange
    ValuedIntegerRangeSemantics {} -> integerNumber
    IntegerTypeSemantics -> integerNumber
    AsciiStringSemantics {} -> injectiveUnknownAlphabet
    IdentifierValueTypeSemantics ->
      knownAlphabet identifierValueCharacterAlphabet
    EitherSemantics left right ->
      eitherConversionProperties
        (stringConversionProperties left)
        (stringConversionProperties right)
    SkipSemantics _ -> exactStrings ["*"]
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
    TemplateSemantics source -> stringConversionProperties source
    DependentSumSemantics _ -> injectiveUnknownAlphabet
    CharacterListSemantics -> injectiveUnknownAlphabet
    AssignmentSemantics _ typeAnnotation givenValue ->
      compositeProperties [typeAnnotation, givenValue]
    CoalizationSemantics operand -> structuralWrapperProperties operand
    MapSemantics _ components -> compositeProperties components
    ArgumentMapSemantics _ components -> compositeProperties components
    SpecificationSemantics source target ->
      compositeProperties [source, target]
    FormulationSemantics {} -> injectiveUnknownAlphabet
    RangeSemantics {} -> injectiveUnknownAlphabet
  where
    naturalNumber =
      knownAlphabet "0123456789"
    integerNumber =
      knownAlphabet "-0123456789"
    numericRange =
      knownAlphabet " -0123456789.rangeftoupwds"
    injectiveUnknownAlphabet =
      StringConversionProperties True Nothing Nothing (const False)
    knownAlphabet alphabet =
      StringConversionProperties
        True
        (Just alphabet)
        Nothing
        (\substring -> any (`notElem` alphabet) substring)
    unknownConversion =
      StringConversionProperties False Nothing Nothing (const False)

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
        (const False)

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
    (\substring ->
      conversionExcludesSubstring left substring
        && conversionExcludesSubstring right substring)

exactStrings :: [String] -> StringConversionProperties
exactStrings strings =
  StringConversionProperties
    True
    (Just (nub (concat strings)))
    (Just strings)
    (\substring -> all (not . isInfixOf substring) strings)

data StringLanguageSegment
  = FixedString String
  | SomeCharacters String

complementedIntegerProperties :: Bool -> StringConversionProperties
complementedIntegerProperties includesInfinity =
  StringConversionProperties
    True
    Nothing
    Nothing
    (\substring ->
      not (null substring)
        && all (not . languageCanContain substring) presentations)
  where
    magnitude = SomeCharacters "0123456789"
    magnitudes =
      [ [magnitude] ]
        <> [ [FixedString "Infinity"] | includesInfinity ]
    presentations =
      magnitudes
        <> map (FixedString "-" :) magnitudes
        <> [ FixedString "(" : value
              <> [FixedString suffix]
           | value <- magnitudes
           , suffix <- ["; nothing)", "; Just : $Complement)"]
           ]

languageCanContain :: String -> [StringLanguageSegment] -> Bool
languageCanContain substring segments =
  any (containsCompatibleWindow substring . expandSegments segments)
    (segmentLengths substring segments)

segmentLengths
  :: String
  -> [StringLanguageSegment]
  -> [[Int]]
segmentLengths substring = traverse lengths
  where
    maximumUsefulLength = max 1 (length substring)
    lengths (FixedString fixed) = [length fixed]
    lengths (SomeCharacters _) = [1 .. maximumUsefulLength]

expandSegments
  :: [StringLanguageSegment]
  -> [Int]
  -> [Either Char String]
expandSegments segments lengths =
  concat (zipWith expand segments lengths)
  where
    expand (FixedString fixed) _ = map Left fixed
    expand (SomeCharacters alphabet) count = replicate count (Right alphabet)

containsCompatibleWindow :: String -> [Either Char String] -> Bool
containsCompatibleWindow substring characters =
  any (and . zipWith compatible substring)
    (windows (length substring) characters)
  where
    compatible expected (Left actual) = expected == actual
    compatible expected (Right alphabet) = expected `elem` alphabet

windows :: Int -> [value] -> [[value]]
windows width values
  | width <= 0 = [[]]
  | length values < width = []
  | otherwise = take width values : windows width (drop 1 values)

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
