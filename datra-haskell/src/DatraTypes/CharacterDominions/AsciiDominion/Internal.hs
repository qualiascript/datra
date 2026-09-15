{-# LANGUAGE RankNTypes #-}

-- | Hidden implementation of the 256-character ASCII dominion.
module AsciiDominion.Internal
  ( AsciiDominion
  , asciiCardinality
  , asciiDominion
  , asciiCharacterAt
  ) where

import Data.Char (chr)
import FiniteDominion.Internal
  ( FiniteDominion
  , finiteIndex
  , finiteSetDominion
  , finiteUnrank
  , finiteValue
  )
import Numeric.Natural (Natural)

import qualified Data.Set as Set

-- | A finite dominion containing the characters at code points 0 through 255.
type AsciiDominion scope = FiniteDominion scope Char

-- | The number of characters in 'AsciiDominion'.
asciiCardinality :: Natural
asciiCardinality = 256

-- | Introduce the 256-character dominion with a fresh abstract scope.
asciiDominion
  :: (forall scope. AsciiDominion scope -> result)
  -> result
asciiDominion = finiteSetDominion characters
  where
    characters = Set.fromDistinctAscList (map chr [0 .. 255])

-- | Look up the character whose code point equals the supplied rank.
asciiCharacterAt
  :: AsciiDominion scope
  -> Natural
  -> Maybe Char
asciiCharacterAt valueDominion valueRank =
  finiteValue . finiteUnrank <$> finiteIndex valueDominion valueRank
