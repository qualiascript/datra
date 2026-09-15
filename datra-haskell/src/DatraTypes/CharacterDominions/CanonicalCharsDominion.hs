{-# LANGUAGE RankNTypes #-}

-- | The character dominion used to construct canonical identifiers.
module CanonicalCharsDominion
  ( CanonicalCharsDominion
  , CanonicalChar
  , canonicalCharsCardinality
  , canonicalCharsDominion
  , canonicalCharValue
  , canonicalCharacterAt
  ) where

import AsciiDominion (asciiDominion)
import Data.Maybe (fromMaybe)
import Dominion (Dominion, dominion, rank, unrank)
import EllipsisInsertion
  ( EllipsisInsertion
  , EllipsisInsertionElement
  , ellipsisInsertionDominion
  , ellipsisInsertionElementValue
  , mergeDisjointEllipsisInsertions
  )
import EllipsisNatural (EllipsisNatural, ellipsisNatural)
import EllipsisRange
  ( EllipsisRange
  , EllipsisRangeElement
  , ellipsisRange
  , ellipsisRangeInsertion
  , mergeSeparatedEllipsisRanges
  )
import FiniteDominion
  ( FiniteElement
  , finiteAsDominion
  , finiteValue
  )
import Numeric.Natural (Natural)

-- | A character carrying evidence that it belongs to the canonical character
-- dominion. Its insertion witness is used during construction and then erased.
newtype CanonicalChar scope = CanonicalChar
  { getCanonicalChar :: FiniteElement scope Char
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
    withEllipsisNatural 39 $ \apostropheRange ->
      withEllipsisRange 48 58 $ \digitRange ->
        withEllipsisRange 65 91 $ \uppercaseRange ->
          withEllipsisNatural 95 $ \underscoreRange ->
            withEllipsisRange 97 123 $ \lowercaseRange ->
              let asciiValues = finiteAsDominion ascii
                  selected = ellipsisInsertionDominion
                    asciiValues
                    (canonicalCharsInsertion
                      apostropheRange
                      digitRange
                      uppercaseRange
                      underscoreRange
                      lowercaseRange)
                  valueDominion = dominion
                    (rank asciiValues . getCanonicalChar)
                    (fmap insertionElementToCanonicalChar . unrank selected)
                    (const ())
              in useCanonical valueDominion

-- | Forget the membership evidence and recover the selected character.
canonicalCharValue :: CanonicalChar scope -> Char
canonicalCharValue = finiteValue . getCanonicalChar

-- | Look up a canonical character by its absolute ASCII rank.
canonicalCharacterAt
  :: CanonicalCharsDominion scope
  -> Natural
  -> Maybe Char
canonicalCharacterAt valueDominion valueRank =
  canonicalCharValue <$> unrank valueDominion valueRank

canonicalCharsInsertion
  :: EllipsisNatural apostropheScope
  -> EllipsisRange digitScope
  -> EllipsisRange uppercaseScope
  -> EllipsisNatural underscoreScope
  -> EllipsisRange lowercaseScope
  -> EllipsisInsertion
      (Either
        (Either
          (EllipsisRangeElement apostropheScope)
          (EllipsisRangeElement digitScope))
        (Either
          (Either
            (EllipsisRangeElement uppercaseScope)
            (EllipsisRangeElement underscoreScope))
          (EllipsisRangeElement lowercaseScope)))
canonicalCharsInsertion
    apostropheRange
    digitRange
    uppercaseRange
    underscoreRange
    lowercaseRange =
  mergeDisjointEllipsisInsertions
    (fromMaybe
      (error "apostrophe and digit ranges are not separated")
      (mergeSeparatedEllipsisRanges apostropheRange digitRange))
    (mergeDisjointEllipsisInsertions
      (fromMaybe
        (error "uppercase and underscore ranges are not separated")
        (mergeSeparatedEllipsisRanges uppercaseRange underscoreRange))
      (ellipsisRangeInsertion lowercaseRange))

insertionElementToCanonicalChar
  :: EllipsisInsertionElement selection (FiniteElement scope Char)
  -> CanonicalChar scope
insertionElementToCanonicalChar =
  CanonicalChar . ellipsisInsertionElementValue

withEllipsisNatural
  :: Natural
  -> (forall scope. EllipsisNatural scope -> result)
  -> result
withEllipsisNatural value useNatural =
  fromMaybe
    (error "an ellipsis natural must contain exactly one value")
    (ellipsisNatural value useNatural)

withEllipsisRange
  :: Natural
  -> Natural
  -> (forall scope. EllipsisRange scope -> result)
  -> result
withEllipsisRange lower upper useRange =
  fromMaybe
    (error "canonical character ranges must be nonempty")
    (ellipsisRange (Just lower) (Just upper) useRange)
