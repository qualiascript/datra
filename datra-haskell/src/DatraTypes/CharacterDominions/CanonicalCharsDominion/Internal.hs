{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

-- | Hidden implementation of the canonical-character dominion.
module CanonicalCharsDominion.Internal
  ( CanonicalCharsDominion
  , CanonicalChar (..)
  , canonicalCharsCardinality
  , canonicalCharsDominion
  , canonicalCharValue
  , canonicalCharacterAt
  ) where

import AsciiDominion.Internal (asciiDominion)
import Data.Maybe (fromMaybe)
import Dominion.Internal (Dominion, dominion, rank, unrank)
import EllipsisInsertion.Internal
  ( EllipsisInsertion
  , EllipsisInsertionElement
  , ellipsisInsertionDominion
  , ellipsisInsertionElementValue
  , mergeDisjointEllipsisInsertions
  )
import EllipsisNatural.Internal (EllipsisNatural)
import EllipsisRange.Internal
  ( EllipsisRange (..)
  , EllipsisRangeElement
  , ellipsisRangeInsertion
  , mergeSeparatedEllipsisRanges
  )
import FiniteDominion.Internal
  ( FiniteElement
  , finiteAsDominion
  , finiteValue
  )
import Numeric.Natural (Natural)

data ApostropheScope
data DigitScope
data UppercaseScope
data UnderscoreScope
data LowercaseScope

type ApostropheAndDigitSelection =
  Either
    (EllipsisRangeElement ApostropheScope)
    (EllipsisRangeElement DigitScope)

type UppercaseAndUnderscoreSelection =
  Either
    (EllipsisRangeElement UppercaseScope)
    (EllipsisRangeElement UnderscoreScope)

type CanonicalCharSelection =
  Either
    ApostropheAndDigitSelection
    (Either
      UppercaseAndUnderscoreSelection
      (EllipsisRangeElement LowercaseScope))

-- | A character selected from 'AsciiDominion' by the canonical insertion.
newtype CanonicalChar scope = CanonicalChar
  { getCanonicalChar ::
      EllipsisInsertionElement
        CanonicalCharSelection
        (FiniteElement scope Char)
  }
  deriving (Eq, Show)

-- | The dominion of ASCII letters, digits, underscore, and apostrophe.
type CanonicalCharsDominion scope = Dominion (CanonicalChar scope)

-- | There are 26 lowercase letters, 26 uppercase letters, 10 digits, and two
-- punctuation characters.
canonicalCharsCardinality :: Natural
canonicalCharsCardinality = 64

-- | Introduce the canonical-character dominion with a fresh ASCII scope.
-- Ranks remain their absolute ASCII code points.
canonicalCharsDominion
  :: (forall scope. CanonicalCharsDominion scope -> result)
  -> result
canonicalCharsDominion useCanonical =
  asciiDominion $ \ascii ->
    let selected = ellipsisInsertionDominion
          (finiteAsDominion ascii)
          canonicalCharsInsertion
        valueDominion = dominion
          (rank selected . getCanonicalChar)
          (fmap CanonicalChar . unrank selected)
          (const ())
    in useCanonical valueDominion

-- | Forget the membership evidence and recover the selected character.
canonicalCharValue :: CanonicalChar scope -> Char
canonicalCharValue =
  finiteValue
    . ellipsisInsertionElementValue
    . getCanonicalChar

-- | Look up a canonical character by its absolute ASCII rank.
canonicalCharacterAt
  :: CanonicalCharsDominion scope
  -> Natural
  -> Maybe Char
canonicalCharacterAt valueDominion valueRank =
  canonicalCharValue <$> unrank valueDominion valueRank

canonicalCharsInsertion :: EllipsisInsertion CanonicalCharSelection
canonicalCharsInsertion =
  mergeDisjointEllipsisInsertions
    (fromMaybe
      (error "apostrophe and digit ranges are not separated")
      (mergeSeparatedEllipsisRanges apostropheRange digitRange))
    (mergeDisjointEllipsisInsertions
      (fromMaybe
        (error "uppercase and underscore ranges are not separated")
        (mergeSeparatedEllipsisRanges uppercaseRange underscoreRange))
      (ellipsisRangeInsertion lowercaseRange))

apostropheRange :: EllipsisNatural ApostropheScope
apostropheRange = EllipsisRange (Just 39) (Just 40)

digitRange :: EllipsisRange DigitScope
digitRange = EllipsisRange (Just 48) (Just 58)

uppercaseRange :: EllipsisRange UppercaseScope
uppercaseRange = EllipsisRange (Just 65) (Just 91)

underscoreRange :: EllipsisNatural UnderscoreScope
underscoreRange = EllipsisRange (Just 95) (Just 96)

lowercaseRange :: EllipsisRange LowercaseScope
lowercaseRange = EllipsisRange (Just 97) (Just 123)
