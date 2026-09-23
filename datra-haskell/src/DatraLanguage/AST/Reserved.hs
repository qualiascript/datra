-- | The word-like symbols reserved by Datra syntax.
module DatraLanguage.AST.Reserved
  ( ReservedWord (..)
  , reservedWordText
  , BuiltInIdentifier (..)
  , builtInIdentifierText
  , reservedIdentifierStrings
  , isReservedIdentifierString
  ) where

import DatraLanguage.AST.Operator
  ( Operator (..)
  , operatorCanonicalSymbol
  )

data ReservedWord
  = FalseWord
  | TrueWord
  | NothingWord
  | BooleanTypeWord
  | StringTypeWord
  | IntegerTypeWord
  | NaturalTypeWord
  | IfWord
  | ThenWord
  | ElseWord
  | FromWord
  | WithinWord
  | ToWord
  | UpwardsWord
  | DownwardsWord
  deriving (Bounded, Enum, Eq, Show)

reservedWordText :: ReservedWord -> String
reservedWordText FalseWord = "false"
reservedWordText TrueWord = "true"
reservedWordText NothingWord = "nothing"
reservedWordText BooleanTypeWord = "Bool"
reservedWordText StringTypeWord = "String"
reservedWordText IntegerTypeWord = "Int"
reservedWordText NaturalTypeWord = "Nat"
reservedWordText IfWord = "if"
reservedWordText ThenWord = "then"
reservedWordText ElseWord = "else"
reservedWordText FromWord = "from"
reservedWordText WithinWord = "within"
reservedWordText ToWord = "to"
reservedWordText UpwardsWord = "upwards"
reservedWordText DownwardsWord = "downwards"

data BuiltInIdentifier
  = FalseIdentifier
  | TrueIdentifier
  | NothingIdentifier
  deriving (Bounded, Enum, Eq, Show)

builtInIdentifierText :: BuiltInIdentifier -> String
builtInIdentifierText FalseIdentifier = "False"
builtInIdentifierText TrueIdentifier = "True"
builtInIdentifierText NothingIdentifier = "Nothing"

reservedIdentifierStrings :: [String]
reservedIdentifierStrings =
  map reservedWordText identifierReservedWords
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
      [ FalseWord
      , TrueWord
      , NothingWord
      , BooleanTypeWord
      , StringTypeWord
      , IntegerTypeWord
      , NaturalTypeWord
      , IfWord
      , ThenWord
      , ElseWord
      , FromWord
      , WithinWord
      ]

isReservedIdentifierString :: String -> Bool
isReservedIdentifierString value = value `elem` reservedIdentifierStrings
