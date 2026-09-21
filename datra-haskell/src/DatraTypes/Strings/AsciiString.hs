{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

-- | Finite strings whose characters are selected from the ASCII map.
--
-- Empty strings use the explicit empty ordered-map presentation. Nonempty
-- strings use a two-page indexed Atlas map with one page-1 cell per character.
module AsciiString
  ( AsciiString
  , AsciiStringCharacter
  , asciiString
  , asciiStringLength
  , asciiStringValue
  , appendAsciiStrings
  , asciiStringCharacterPosition
  , asciiStringCharacterValue
  , asciiStringCharacterAt
  ) where

import AsciiMap
  ( AsciiCharacter
  , AsciiMap
  , asciiCharacterValue
  , asciiMap
  )
import Control.Monad (join)
import Data.Char (ord)
import DatraOrdinal (naturalAtOrdinal)
import Dominion (Dominion, dominion)
import EllipsisNatural
  ( EllipsisNaturalElement
  , ellipsisNatural
  )
import MapOperators.AccessOperator
  ( AccessElement
  , accessElementValue
  , accessOperator
  )
import MapOperators.IndexedAtlasMap (indexedAtlasMap)
import MapOperators.OrderedAtlasMap
  ( HasOrderedAtlasMap (..)
  , OrderedAtlasMap (..)
  , orderedAtlasMapCardinality
  , orderedAtlasMapValueAt
  )
import Numeric.Natural (Natural)
import Prelude

import qualified Data.Map.Strict as Map

-- | One ASCII character together with its position in a particular string.
-- The existential access source records the EllipsisNatural that selected the
-- character. Position, rather than character value, is the dominion rank so
-- repeated characters remain distinct members of the final page.
type role AsciiStringCharacter nominal
data AsciiStringCharacter asciiScope where
  AsciiStringCharacter
    :: Natural
    -> AccessElement
         (EllipsisNaturalElement indexScope)
         (AsciiCharacter asciiScope)
    -> AsciiStringCharacter asciiScope

-- | A finite sequence of ASCII characters. The constructor is hidden so every
-- nonempty value retains the dense finite-page invariant.
type role AsciiString nominal
newtype AsciiString asciiScope = AsciiString
  { getAsciiStringOrderedAtlasMap
      :: OrderedAtlasMap (AsciiStringCharacter asciiScope)
  }

-- | Introduce a string by accessing the ASCII map once for each character.
-- Returns 'Nothing' when any supplied character lies outside that map.
asciiString
  :: Prelude.String
  -> (forall asciiScope. AsciiString asciiScope -> result)
  -> Maybe result
asciiString characters useString =
  asciiMap $ \ascii -> do
    positionedCharacters <-
      traverse
        (selectAsciiCharacter ascii)
        (zip [0 ..] characters)
    pure
      (useString
        (AsciiString (orderedCharacters positionedCharacters)))

selectAsciiCharacter
  :: AsciiMap asciiScope
  -> (Natural, Char)
  -> Maybe (AsciiStringCharacter asciiScope)
selectAsciiCharacter ascii (position, character) =
  join
    (ellipsisNatural (fromIntegral (ord character)) $ \index -> do
      selected <- accessOperator ascii index
      accessed <- orderedAtlasMapValueAt selected 0
      pure (AsciiStringCharacter position accessed))

orderedCharacters
  :: [AsciiStringCharacter asciiScope]
  -> OrderedAtlasMap (AsciiStringCharacter asciiScope)
orderedCharacters [] = EmptyOrderedAtlasMap
orderedCharacters characters@(first : _) =
  NonEmptyOrderedAtlasMap
    (indexedAtlasMap
      (naturalLength characters)
      first
      (asciiStringCharacterDominion characters))

asciiStringCharacterDominion
  :: [AsciiStringCharacter asciiScope]
  -> Dominion (AsciiStringCharacter asciiScope)
asciiStringCharacterDominion characters =
  dominion
    asciiStringCharacterPosition
    (`Map.lookup` charactersByPosition)
    (const ())
  where
    charactersByPosition =
      Map.fromList
        (map (\character ->
          (asciiStringCharacterPosition character, character)) characters)

naturalLength :: [value] -> Natural
naturalLength = foldl' (\lengthSoFar _ -> lengthSoFar + 1) 0

-- | The zero-based position occupied by a selected character.
asciiStringCharacterPosition :: AsciiStringCharacter scope -> Natural
asciiStringCharacterPosition (AsciiStringCharacter position _) = position

-- | Recover a selected character's ordinary value.
asciiStringCharacterValue :: AsciiStringCharacter scope -> Char
asciiStringCharacterValue (AsciiStringCharacter _ selected) =
  asciiCharacterValue (accessElementValue selected)

-- | The finite number of characters in the string.
asciiStringLength :: AsciiString scope -> Natural
asciiStringLength (AsciiString characters) =
  case naturalAtOrdinal (orderedAtlasMapCardinality characters) of
    Just lengthValue -> lengthValue
    Nothing -> 0

-- | Recover the ordinary Haskell string in page-1 order.
asciiStringValue :: AsciiString scope -> Prelude.String
asciiStringValue value = collect 0
  where
    collect position
      | position == asciiStringLength value = []
      | otherwise =
          case asciiStringCharacterAt value position of
            Just character -> character : collect (position + 1)
            Nothing -> []

-- | Concatenate two strings and introduce the result with a fresh scope.
appendAsciiStrings
  :: AsciiString leftScope
  -> AsciiString rightScope
  -> (forall scope. AsciiString scope -> result)
  -> Maybe result
appendAsciiStrings left right =
  asciiString (asciiStringValue left <> asciiStringValue right)

-- | Look up a character by its zero-based page-1 position.
asciiStringCharacterAt
  :: AsciiString scope
  -> Natural
  -> Maybe Char
asciiStringCharacterAt (AsciiString characters) position =
  asciiStringCharacterValue
    <$> orderedAtlasMapValueAt characters position

instance HasOrderedAtlasMap (AsciiString scope) where
  type OrderedAtlasElement (AsciiString scope) = AsciiStringCharacter scope
  orderedAtlasMap = getAsciiStringOrderedAtlasMap
