-- | Shared lexical facts about Datra identifier names.
module DatraLanguage.Identifier
  ( IdentifierSpelling (..)
  , identifierSpellingValue
  , isPrivateIdentifier
  , isIdentifierValue
  , isIdentifierCharacter
  , isAsciiCharacter
  ) where

import Data.Char (ord)

data IdentifierSpelling
  = BareIdentifier String
  | FullStringIdentifier String

identifierSpellingValue :: IdentifierSpelling -> Maybe String
identifierSpellingValue (FullStringIdentifier value) = Just value
identifierSpellingValue (BareIdentifier value) = Just value

-- | Leading underscores make a binding private to its defining scope or turn
-- a function parameter name into a positional-only implementation detail.
isPrivateIdentifier :: String -> Bool
isPrivateIdentifier ('_' : _) = True
isPrivateIdentifier _ = False

-- | A bare identifier is nonempty and uses the identifier alphabet without a
-- leading digit.
isIdentifierValue :: String -> Bool
isIdentifierValue [] = False
isIdentifierValue value@(first : _) =
  not (isAsciiDigit first) && all isIdentifierCharacter value

isIdentifierCharacter :: Char -> Bool
isIdentifierCharacter character =
  isAsciiLetter character
    || isAsciiDigit character
    || character == '_'
    || character == '\''

isAsciiLetter :: Char -> Bool
isAsciiLetter character =
  ('a' <= character && character <= 'z')
    || ('A' <= character && character <= 'Z')

isAsciiDigit :: Char -> Bool
isAsciiDigit character = '0' <= character && character <= '9'

isAsciiCharacter :: Char -> Bool
isAsciiCharacter character = ord character < 256
