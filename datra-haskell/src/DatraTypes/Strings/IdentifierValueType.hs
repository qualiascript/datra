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

-- | Compact strings start with an ASCII letter, digit, underscore, or
-- apostrophe. A leading underscore or apostrophe requires an immediately
-- following ASCII alphanumeric character. The complete string must contain at
-- least one non-digit.
isIdentifierValue :: String -> Bool
isIdentifierValue [] = False
isIdentifierValue value@(first : rest) =
  isIdentifierValueInitialCharacter first
    && all isIdentifierValueCharacter rest
    && any (not . isAsciiDigit) value
    && validSpecialPrefix value

-- | Every character which can occur somewhere in an identifier value. This
-- language fact lets template concatenation prove that delimiters such as a
-- space cannot occur inside an @IdenStr@ interpolation.
identifierValueCharacterAlphabet :: String
identifierValueCharacterAlphabet =
  ['a' .. 'z'] <> ['A' .. 'Z'] <> ['0' .. '9'] <> "_'"

isIdentifierValueCharacter :: Char -> Bool
isIdentifierValueCharacter character =
  character `elem` identifierValueCharacterAlphabet

isIdentifierValueInitialCharacter :: Char -> Bool
isIdentifierValueInitialCharacter = isIdentifierValueCharacter

validSpecialPrefix :: String -> Bool
validSpecialPrefix (prefix : following : _)
  | prefix == '_' || prefix == '\'' = isAsciiAlphaNumeric following
validSpecialPrefix [prefix]
  | prefix == '_' || prefix == '\'' = False
validSpecialPrefix _ = True

isAsciiAlphaNumeric :: Char -> Bool
isAsciiAlphaNumeric character =
  ('a' <= character && character <= 'z')
    || ('A' <= character && character <= 'Z')
    || isAsciiDigit character

isAsciiDigit :: Char -> Bool
isAsciiDigit character = '0' <= character && character <= '9'
