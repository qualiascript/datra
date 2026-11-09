-- | The lexical language shared by bare identifiers and compact @$value@
-- string literals.
module DatraLanguage.IdentifierSyntax
  ( isIdentifierValue
  , isIdentifierValueCharacter
  , identifierValueCharacterAlphabet
  ) where

-- | A simple identifier is a nonempty string over the identifier alphabet
-- whose first character is not a digit.
isIdentifierValue :: String -> Bool
isIdentifierValue [] = False
isIdentifierValue value@(first : _) =
  not (isAsciiDigit first)
    && all isIdentifierValueCharacter value

-- | Every character which can occur somewhere in an identifier spelling.
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
