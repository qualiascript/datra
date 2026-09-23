{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Finite strings whose characters are selected from the ASCII map.
--
-- Empty strings use the explicit empty ordered-map presentation. Nonempty
-- strings use a two-page indexed Atlas map with one page-1 cell per character.
module AsciiString
  ( AsciiString
  , AsciiStringCharacter
  , ConcatenatedAsciiStringCharacter
  , AsciiStringElement
  , asciiString
  , asciiStringLength
  , asciiStringValue
  , appendAsciiStrings
  , accessAsciiString
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
  , HasSuperEllipsisInsertion
      ( InsertionSource
      )
  , accessElementValue
  , accessOperator
  )
import MapOperators.ConcatOperator (Concat (..))
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
newtype AsciiString character = AsciiString
  { getAsciiStringOrderedAtlasMap
      :: OrderedAtlasMap character
  }

-- | Character witnesses that can be observed through an ASCII string.
class AsciiStringElement character where
  asciiStringElementValue :: character -> Char

instance AsciiStringElement (AsciiStringCharacter scope) where
  asciiStringElementValue = asciiStringCharacterValue

instance
    (AsciiStringElement left, AsciiStringElement right) =>
    AsciiStringElement (Either left right) where
  asciiStringElementValue (Left value) = asciiStringElementValue value
  asciiStringElementValue (Right value) = asciiStringElementValue value

instance AsciiStringElement value =>
    AsciiStringElement (AccessElement source value) where
  asciiStringElementValue = asciiStringElementValue . accessElementValue

-- | A character retained from one side of an underlying map concatenation.
data ConcatenatedAsciiStringCharacter left right =
  ConcatenatedAsciiStringCharacter
    Natural
    (Either left right)

instance
    (AsciiStringElement left, AsciiStringElement right) =>
    AsciiStringElement (ConcatenatedAsciiStringCharacter left right) where
  asciiStringElementValue
      (ConcatenatedAsciiStringCharacter _ character) =
    asciiStringElementValue character

-- | Introduce a string by accessing the ASCII map once for each character.
-- Returns 'Nothing' when any supplied character lies outside that map.
asciiString
  :: Prelude.String
  -> (forall asciiScope.
       AsciiString (AsciiStringCharacter asciiScope)
       -> result)
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
orderedCharacters = orderedCharactersBy asciiStringCharacterPosition

orderedCharactersBy
  :: (character -> Natural)
  -> [character]
  -> OrderedAtlasMap character
orderedCharactersBy _ [] = EmptyOrderedAtlasMap
orderedCharactersBy position characters@(first : _) =
  NonEmptyOrderedAtlasMap
    (indexedAtlasMap
      (naturalLength characters)
      first
      (positionedDominion position characters))

positionedDominion
  :: (character -> Natural)
  -> [character]
  -> Dominion character
positionedDominion position characters =
  dominion
    position
    (`Map.lookup` charactersByPosition)
    (const ())
  where
    charactersByPosition =
      Map.fromList
        (map (\character ->
          (position character, character)) characters)

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
asciiStringValue
  :: AsciiStringElement character
  => AsciiString character
  -> Prelude.String
asciiStringValue value = collect 0
  where
    collect position
      | position == asciiStringLength value = []
      | otherwise =
          case asciiStringCharacterAt value position of
            Just character -> character : collect (position + 1)
            Nothing -> []

-- | Concatenate the underlying ordered Atlas maps and retain string behavior.
appendAsciiStrings
  :: AsciiString left
  -> AsciiString right
  -> AsciiString (ConcatenatedAsciiStringCharacter left right)
appendAsciiStrings (AsciiString left) (AsciiString right) =
  AsciiString
    (orderedCharactersBy
      concatenatedPosition
      ( zipWith
          ConcatenatedAsciiStringCharacter
          [0 ..]
          (map Left (orderedValues left) <> map Right (orderedValues right))
      ))
  where
    concatenatedPosition
      (ConcatenatedAsciiStringCharacter position _) = position

orderedValues :: OrderedAtlasMap value -> [value]
orderedValues values =
  case naturalAtOrdinal (orderedAtlasMapCardinality values) of
    Nothing -> []
    Just cardinality -> collect 0 cardinality
  where
    collect position cardinality
      | position == cardinality = []
      | otherwise =
          case orderedAtlasMapValueAt values position of
            Just value -> value : collect (position + 1) cardinality
            Nothing -> []

-- | Access the underlying ordered Atlas map and retain string behavior.
accessAsciiString
  :: HasSuperEllipsisInsertion operand
  => AsciiString character
  -> operand
  -> Maybe
       (AsciiString
         (AccessElement (InsertionSource operand) character))
accessAsciiString (AsciiString characters) operand =
  AsciiString <$> accessOperator characters operand

-- | Look up a character by its zero-based page-1 position.
asciiStringCharacterAt
  :: AsciiStringElement character
  => AsciiString character
  -> Natural
  -> Maybe Char
asciiStringCharacterAt (AsciiString characters) position =
  asciiStringElementValue
    <$> orderedAtlasMapValueAt characters position

instance HasOrderedAtlasMap (AsciiString character) where
  type OrderedAtlasElement (AsciiString character) = character
  orderedAtlasMap = getAsciiStringOrderedAtlasMap

instance
    Concat (AsciiString left) (AsciiString right) where
  type ConcatResult (AsciiString left) (AsciiString right) =
    AsciiString (ConcatenatedAsciiStringCharacter left right)
  concatOperands = appendAsciiStrings
