-- | Strings which have Datra's compact @$identifier@ spelling.
--
-- This module is the single definition of the compact-string language. Both
-- source parsing and evaluated @IdenStr@ membership delegate to it.
module IdentifierValueType
  ( IdentifierValueType
  , identifierValue
  , identifierValueText
  , isIdentifierValue
  , isIdentifierValueCharacter
  , identifierValueCharacterAlphabet
  ) where

newtype IdentifierValueType = IdentifierValue
  { identifierValueText :: String
  }
  deriving (Eq, Show)

identifierValue :: String -> Maybe IdentifierValueType
identifierValue value
  | isIdentifierValue value = Just (IdentifierValue value)
  | otherwise = Nothing

-- | A simple identifier is a nonempty string over the identifier alphabet
-- containing at least one non-digit. No character has a positional role.
isIdentifierValue :: String -> Bool
isIdentifierValue [] = False
isIdentifierValue value =
  all isIdentifierValueCharacter value
    && any (not . isAsciiDigit) value

-- | Every character which can occur somewhere in an identifier value. This
-- language fact lets template concatenation prove that delimiters such as a
-- space cannot occur inside an @IdenStr@ interpolation.
identifierValueCharacterAlphabet :: String
identifierValueCharacterAlphabet =
  ['a' .. 'z'] <> ['A' .. 'Z'] <> ['0' .. '9'] <> "_'"

isIdentifierValueCharacter :: Char -> Bool
isIdentifierValueCharacter character =
  isAsciiAlphaNumeric character || character == '_' || character == '\''


isAsciiAlphaNumeric :: Char -> Bool
isAsciiAlphaNumeric character =
  ('a' <= character && character <= 'z')
    || ('A' <= character && character <= 'Z')
    || isAsciiDigit character

isAsciiDigit :: Char -> Bool
isAsciiDigit character = '0' <= character && character <= '9'
