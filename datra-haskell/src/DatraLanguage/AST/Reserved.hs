-- | Reserved context-binding identifiers and syntax-only words.
module DatraLanguage.AST.Reserved
  ( ReservedWord (..)
  , reservedWordText
  , ReservedSymbol (..)
  , reservedSymbols
  , reservedSymbolIdentifierString
  , reservedSymbolIdentifiersAreUnique
  , reservedIdentifierStrings
  , isReservedIdentifierString
  ) where

import DatraLanguage.AST.Operator
  ( Operator (..)
  , operatorCanonicalSymbol
  )

data ReservedWord
  = ThenWord
  | ElseWord
  | ToWord
  | UpwardsWord
  | DownwardsWord
  deriving (Bounded, Enum, Eq, Show)

reservedWordText :: ReservedWord -> String
reservedWordText ThenWord = "then"
reservedWordText ElseWord = "else"
reservedWordText ToWord = "to"
reservedWordText UpwardsWord = "upwards"
reservedWordText DownwardsWord = "downwards"

-- | A reserved identifier whose value is supplied by the language context.
-- Some are currently parser forms or interpreter/FFI bootstraps; a future
-- Datra standard library can provide ordinary definitions for the same names.
data ReservedSymbol
  = BooleanTypeSymbol
  | StringTypeSymbol
  | IntegerTypeSymbol
  | NaturalTypeSymbol
  | IfSymbol
  | RangeSymbol
  | FromSymbol
  | FalseSymbol
  | TrueSymbol
  | NothingSymbol
  deriving (Bounded, Enum, Eq, Show)

reservedSymbols :: [ReservedSymbol]
reservedSymbols
  | reservedSymbolIdentifiersAreUnique = [minBound .. maxBound]
  | otherwise = error "reserved symbols must have unique identifier strings"

-- | The unique simple-identifier spelling reserved for a context binding.
reservedSymbolIdentifierString :: ReservedSymbol -> String
reservedSymbolIdentifierString BooleanTypeSymbol = "Bool"
reservedSymbolIdentifierString StringTypeSymbol = "String"
reservedSymbolIdentifierString IntegerTypeSymbol = "Int"
reservedSymbolIdentifierString NaturalTypeSymbol = "Nat"
reservedSymbolIdentifierString IfSymbol = "if"
reservedSymbolIdentifierString RangeSymbol = "range"
reservedSymbolIdentifierString FromSymbol = "from"
reservedSymbolIdentifierString FalseSymbol = "false"
reservedSymbolIdentifierString TrueSymbol = "true"
reservedSymbolIdentifierString NothingSymbol = "nothing"

reservedSymbolIdentifiersAreUnique :: Bool
reservedSymbolIdentifiersAreUnique =
  allDifferent
    (map reservedSymbolIdentifierString
      ([minBound .. maxBound] :: [ReservedSymbol]))
  where
    allDifferent [] = True
    allDifferent (value : remaining) =
      value `notElem` remaining && allDifferent remaining

reservedIdentifierStrings :: [String]
reservedIdentifierStrings =
  map reservedSymbolIdentifierString reservedSymbols
    <> map reservedWordText identifierReservedWords
    <> map operatorCanonicalSymbol
      [ MinusOperator
      , SubfederationOperator
      , BooleanAndOperator
      , BooleanOrOperator
      , BooleanNotOperator
      , EitherOperator
      , OptionalOperator
      ]
  where
    -- These words introduce or delimit expressions wherever an identifier
    -- could begin. Range continuations (to/upwards/downwards) are contextual
    -- and deliberately remain valid bare identifier names.
    identifierReservedWords =
      filter reservesIdentifier
        ([minBound .. maxBound] :: [ReservedWord])
    reservesIdentifier ToWord = False
    reservesIdentifier UpwardsWord = False
    reservesIdentifier DownwardsWord = False
    reservesIdentifier _ = True

isReservedIdentifierString :: String -> Bool
isReservedIdentifierString value = value `elem` reservedIdentifierStrings
