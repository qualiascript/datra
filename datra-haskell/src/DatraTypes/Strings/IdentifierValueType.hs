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

-- | Compact strings start with an ASCII letter, digit, or underscore. Later
-- characters may additionally be apostrophes. Underscores may not be doubled
-- or trailing, and the complete string must contain at least one non-digit.
isIdentifierValue :: String -> Bool
isIdentifierValue [] = False
isIdentifierValue value@(first : rest) =
  isIdentifierValueInitialCharacter first
    && all isIdentifierValueCharacter rest
    && any (not . isAsciiDigit) value
    && last value /= '_'
    && not (hasDoubledUnderscore value)
  where
    hasDoubledUnderscore ('_' : '_' : _) = True
    hasDoubledUnderscore (_ : remaining) =
      hasDoubledUnderscore remaining
    hasDoubledUnderscore [] = False

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
isIdentifierValueInitialCharacter character =
  isIdentifierValueCharacter character && character /= '\''

isAsciiDigit :: Char -> Bool
isAsciiDigit character = '0' <= character && character <= '9'
