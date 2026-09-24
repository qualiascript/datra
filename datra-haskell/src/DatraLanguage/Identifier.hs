-- | Shared lexical facts about Datra identifier names.
module DatraLanguage.Identifier
  ( IdentifierSpelling (..)
  , identifierSpellingValue
  , isPrivateIdentifier
  , isLeadingIdentifierCharacter
  , isIdentifierCharacter
  , isAsciiCharacter
  ) where

import Data.Char (ord)
import DatraLanguage.AST.Reserved qualified as Reserved

data IdentifierSpelling
  = BareIdentifier String
  | FullStringIdentifier String

-- | Quoted identifiers may contain reserved words; bare identifiers may not.
identifierSpellingValue :: IdentifierSpelling -> Maybe String
identifierSpellingValue (FullStringIdentifier value) = Just value
identifierSpellingValue (BareIdentifier value)
  | Reserved.isReservedIdentifierString value = Nothing
  | otherwise = Just value

-- | Leading underscores make a binding private to its defining scope or turn
-- a function parameter name into a positional-only implementation detail.
isPrivateIdentifier :: String -> Bool
isPrivateIdentifier ('_' : _) = True
isPrivateIdentifier _ = False

isLeadingIdentifierCharacter :: Char -> Bool
isLeadingIdentifierCharacter character =
  isAsciiLetter character || character == '_'

isIdentifierCharacter :: Char -> Bool
isIdentifierCharacter character =
  isLeadingIdentifierCharacter character
    || isAsciiDigit character
    || character == '\''

isAsciiLetter :: Char -> Bool
isAsciiLetter character =
  ('a' <= character && character <= 'z')
    || ('A' <= character && character <= 'Z')

isAsciiDigit :: Char -> Bool
isAsciiDigit character = '0' <= character && character <= '9'

isAsciiCharacter :: Char -> Bool
isAsciiCharacter character = ord character < 256
