-- | Reserved context-binding identifiers and syntax-only words.
module DatraLanguage.AST.Reserved
  ( ReservedWord (..)
  , reservedWordText
  , ReservedSymbol (..)
  , reservedSymbols
  , reservedSymbolIdentifierString
  , reservedSymbolIdentifiersAreUnique
  ) where

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
reservedWordText UpwardsWord = "up"
reservedWordText DownwardsWord = "down"

-- | A reserved identifier whose value is supplied by the language context.
-- Some are currently parser forms or interpreter/FFI bootstraps; a future
-- Datra standard library can provide ordinary definitions for the same names.
data ReservedSymbol
  = BooleanTypeSymbol
  | StringTypeSymbol
  | IdentifierValueTypeSymbol
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
reservedSymbolIdentifierString StringTypeSymbol = "Str"
reservedSymbolIdentifierString IdentifierValueTypeSymbol = "IdenStr"
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
