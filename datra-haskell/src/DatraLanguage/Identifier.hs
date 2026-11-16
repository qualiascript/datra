-- | Shared lexical facts about Datra identifier names.
module DatraLanguage.Identifier
  ( privateIdentifierPrefixCharacter
  , identifierPrimeCharacter
  , isPrivateIdentifier
  , isIdentifierValue
  , identifierNaturalValue
  , canonicalNaturalValue
  , isIdentifierCharacter
  , isAsciiCharacter
  ) where

import Data.Char (ord)
import Numeric.Natural (Natural)

-- | Leading underscores make a binding private to its defining scope or turn
-- a function parameter name into a positional-only implementation detail.
privateIdentifierPrefixCharacter :: Char
privateIdentifierPrefixCharacter = '_'

identifierPrimeCharacter :: Char
identifierPrimeCharacter = '\''

isPrivateIdentifier :: String -> Bool
isPrivateIdentifier (prefix : _) =
  prefix == privateIdentifierPrefixCharacter
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

-- | Decode the unique decimal presentation emitted for a natural. This is
-- deliberately stricter than 'identifierNaturalValue': numeric identifiers
-- may contain leading zeroes, while an inverse string codec must accept only
-- the presentation produced by its renderer.
canonicalNaturalValue :: String -> Maybe Natural
canonicalNaturalValue value = do
  natural <- identifierNaturalValue value
  if show natural == value then Just natural else Nothing

isIdentifierCharacter :: Char -> Bool
isIdentifierCharacter character =
  isAsciiLetter character
    || isAsciiDigit character
    || character == privateIdentifierPrefixCharacter
    || character == identifierPrimeCharacter

isAsciiLetter :: Char -> Bool
isAsciiLetter character =
  ('a' <= character && character <= 'z')
    || ('A' <= character && character <= 'Z')

isAsciiDigit :: Char -> Bool
isAsciiDigit character = '0' <= character && character <= '9'

isAsciiCharacter :: Char -> Bool
isAsciiCharacter character = ord character < 256
