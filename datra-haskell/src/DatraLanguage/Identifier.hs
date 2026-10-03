-- | Shared lexical facts about Datra identifier names.
module DatraLanguage.Identifier
  ( IdentifierSpelling (..)
  , IdentifierPolicy (..)
  , ShadowingConsistency (..)
  , identifierSpellingValue
  , identifierPolicy
  , public
  , isPrivateIdentifier
  , requiresShadowingConsistency
  , isLeadingIdentifierCharacter
  , isIdentifierCharacter
  , isAsciiCharacter
  ) where

import Data.Char (ord)

-- | Private names are never assigned a public shadowing policy. Keeping these
-- cases in a sum makes "private and shadowing-consistent" unrepresentable.
data IdentifierPolicy
  = PrivateIdentifier
  | PublicIdentifier ShadowingConsistency
  deriving (Eq, Show)

data ShadowingConsistency
  = UnrestrictedShadowing
  | ConsistentShadowing
  deriving (Eq, Show)

-- | Keep exactly the named bindings whose identifiers are externally visible.
-- Module export maps and function argument routing share this operation so a
-- leading underscore has one meaning throughout the language.
public :: [(String, value)] -> [(String, value)]
public = filter (not . isPrivateIdentifier . fst)

data IdentifierSpelling
  = BareIdentifier String
  | FullStringIdentifier String

identifierSpellingValue :: IdentifierSpelling -> Maybe String
identifierSpellingValue (FullStringIdentifier value) = Just value
identifierSpellingValue (BareIdentifier value) = Just value

-- | Leading underscores make a binding private to its defining scope or turn
-- a function parameter name into a positional-only implementation detail.
isPrivateIdentifier :: String -> Bool
isPrivateIdentifier name =
  case identifierPolicy name of
    PrivateIdentifier -> True
    PublicIdentifier _ -> False

-- | An apostrophe-prefixed name requires every later binding under the same
-- name to reduce to the value already denoted by that name. This classification
-- applies to quoted names as well as compact identifiers.
requiresShadowingConsistency :: String -> Bool
requiresShadowingConsistency name =
  case identifierPolicy name of
    PublicIdentifier ConsistentShadowing -> True
    PrivateIdentifier -> False
    PublicIdentifier UnrestrictedShadowing -> False

identifierPolicy :: String -> IdentifierPolicy
identifierPolicy ('_' : _) = PrivateIdentifier
identifierPolicy ('\'' : _) = PublicIdentifier ConsistentShadowing
identifierPolicy _ = PublicIdentifier UnrestrictedShadowing

isLeadingIdentifierCharacter :: Char -> Bool
isLeadingIdentifierCharacter character =
  isAsciiLetter character || character == '_' || character == '\''

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
