-- | Shared lexical facts about Datra identifier names.
module DatraLanguage.Identifier
  ( IdentifierSpelling (..)
  , identifierSpellingValue
  , isPrivateIdentifier
  , isIdentifierValue
  , identifierNaturalValue
  , isIdentifierCharacter
  , isAsciiCharacter
  ) where

import Data.Char (ord)
import Numeric.Natural (Natural)

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

-- | A bare identifier is nonempty and uses the identifier alphabet. Numeric
-- meaning is supplied later by the standard library, so all-numeric spellings
-- are identifiers at the lexical boundary too.
isIdentifierValue :: String -> Bool
isIdentifierValue [] = False
isIdentifierValue value = all isIdentifierCharacter value

-- | Decode precisely the all-ASCII-digit identifier language. Using
-- 'Natural' keeps the conversion total for arbitrarily long spellings.
identifierNaturalValue :: String -> Maybe Natural
identifierNaturalValue [] = Nothing
identifierNaturalValue value = go 0 value
  where
    go result [] = Just result
    go result (character : remaining)
      | isAsciiDigit character =
          go
            (result * 10
              + fromIntegral (ord character - ord '0'))
            remaining
      | otherwise = Nothing

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
