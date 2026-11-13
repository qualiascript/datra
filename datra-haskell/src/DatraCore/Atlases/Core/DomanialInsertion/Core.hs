{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Checked domanial insertions and their rank-image operations.
module DomanialInsertion.Core
  ( DomanialInsertion (..)
  , domanialInsertion
  , identityInsertion
  , identityInsertionApply
  , composeInsertions
  , pullbackDominion
  , rankImageInsertion
  , rankImage
  , rankImagePreimage
  , rankImageRoundTrip
  , rankImagePreimageSound
  ) where

import Dominion.Internal (Dominion (..))
import Numeric.Natural (Natural)

-- | An injective function between dominions. The executable left-inverse proof
-- establishes injectivity, exactly as Lean's `Function.Embedding` requires.
{-@
data DomanialInsertion a b = DomanialInsertion
  { applyInsertion :: a -> b
  , preimage :: b -> Maybe a
  , insertionLeftInverse :: x:a ->
      { proof:() |
          preimage (applyInsertion x) == Just x }
  }
@-}
data DomanialInsertion a b = DomanialInsertion
  { applyInsertion :: a -> b
  , preimage :: b -> Maybe a
  , insertionLeftInverse :: a -> ()
  }

-- | Construct an insertion. LiquidHaskell verifies the left-inverse proof.
{-@
domanialInsertion
  :: forward:(a -> b)
  -> backward:(b -> Maybe a)
  -> (x:a -> { proof:() | backward (forward x) == Just x })
  -> DomanialInsertion a b
@-}
-- ALIGN: INSERTION-INJECTIVE.
domanialInsertion
  :: (a -> b)
  -> (b -> Maybe a)
  -> (a -> ())
  -> DomanialInsertion a b
domanialInsertion = DomanialInsertion

{-@ reflect composeInsertionMap @-}
composeInsertionMap :: DomanialInsertion b c -> DomanialInsertion a b -> a -> c
composeInsertionMap second first value = applyInsertion second (applyInsertion first value)

{-@ reflect composeInsertionPreimage @-}
composeInsertionPreimage :: DomanialInsertion b c -> DomanialInsertion a b -> c -> Maybe a
composeInsertionPreimage second first value =
  case preimage second value of
    Nothing -> Nothing
    Just middle -> preimage first middle

{-@
composeInsertionRoundTrip
  :: second:DomanialInsertion b c
  -> first:DomanialInsertion a b
  -> value:a
  -> {proof:() | composeInsertionPreimage second first
       (composeInsertionMap second first value) == Just value}
@-}
-- ALIGN: INSERTION-COMPOSITION-ROUNDTRIP.
composeInsertionRoundTrip :: DomanialInsertion b c -> DomanialInsertion a b -> a -> ()
composeInsertionRoundTrip second first value =
  insertionLeftInverse second (applyInsertion first value) `seq` insertionLeftInverse first value

-- | Compose the maps and derive the certificate from both stored laws.
-- ALIGN: INSERTION-COMPOSITION.
-- ALIGN: INSERTION-COMPOSITION-INTERPRETATION.
composeInsertions
  :: DomanialInsertion b c
  -> DomanialInsertion a b
  -> DomanialInsertion a c
composeInsertions second first =
  DomanialInsertion
    (composeInsertionMap second first)
    (composeInsertionPreimage second first)
    (composeInsertionRoundTrip second first)

{-@ reflect identityMap @-}
identityMap :: a -> a
identityMap value = value

{-@ reflect identityPreimage @-}
identityPreimage :: a -> Maybe a
identityPreimage value = Just value

{-@ identityRoundTrip :: value:a ->
      {proof:() | identityPreimage (identityMap value) == Just value} @-}
-- ALIGN: INSERTION-IDENTITY-ROUNDTRIP.
identityRoundTrip :: a -> ()
identityRoundTrip _ = ()

-- ALIGN: INSERTION-IDENTITY.
{-@ reflect identityInsertion @-}
identityInsertion :: DomanialInsertion a a
identityInsertion = DomanialInsertion identityMap identityPreimage identityRoundTrip

-- | The public identity law does not require clients to unfold private helpers.
{-@ identityInsertionApply :: value:a -> {applyInsertion identityInsertion value == value} @-}
identityInsertionApply :: a -> ()
identityInsertionApply _ = ()

{-@ reflect pullbackUnrank @-}
-- ALIGN: INSERTION-PULLBACK-UNRANK.
pullbackUnrank :: Dominion b -> DomanialInsertion a b -> Natural -> Maybe a
pullbackUnrank target insertion valueRank =
  case unrank target valueRank of
    Nothing -> Nothing
    Just root -> preimage insertion root

{-@
pullbackRoundTrip
  :: target:Dominion b
  -> insertion:DomanialInsertion a b
  -> value:a
  -> {proof:() | pullbackUnrank target insertion
       (rankImage target insertion value) == Just value}
@-}
-- ALIGN: INSERTION-PULLBACK-ROUNDTRIP.
pullbackRoundTrip :: Dominion b -> DomanialInsertion a b -> a -> ()
pullbackRoundTrip (Dominion _ _ coherence) insertion value =
  coherence (applyInsertion insertion value) `seq` insertionLeftInverse insertion value

-- | Induce a source ranking. Its unranking retains the arbitrary off-image
-- behavior permitted by Dominion's round-trip contract.
-- ALIGN: INSERTION-PULLBACK-DOMINION.
-- ALIGN: INSERTION-PULLBACK-INTERPRETATION.
pullbackDominion :: Dominion b -> DomanialInsertion a b -> Dominion a
pullbackDominion target insertion =
  Dominion (rankImage target insertion) (pullbackUnrank target insertion)
    (pullbackRoundTrip target insertion)

-- | Encode an insertion's image using the target Dominion's ranks.
{-@ reflect rankImage @-}
-- ALIGN: INSERTION-RANK-IMAGE.
rankImage :: Dominion b -> DomanialInsertion a b -> a -> Natural
rankImage valueDominion insertion value =
  rank valueDominion (applyInsertion insertion value)

-- | Neither unranking nor a left inverse is required to reject values
-- outside its image. Check the resulting candidate against the requested rank.
{-@ reflect rankImagePreimage @-}
-- ALIGN: INSERTION-RANK-PREIMAGE.
rankImagePreimage :: Dominion b -> DomanialInsertion a b -> Natural -> Maybe a
rankImagePreimage valueDominion insertion valueRank =
  case unrank valueDominion valueRank of
    Nothing -> Nothing
    Just rootDatum -> case preimage insertion rootDatum of
      Nothing -> Nothing
      Just candidate ->
        if rankImage valueDominion insertion candidate == valueRank
          then Just candidate
          else Nothing

-- ALIGN: INSERTION-RANK-PACKAGE.
-- ALIGN: INSERTION-RANK-IMAGE-EQUIV.
-- ALIGN: INSERTION-RANK-IMAGE-EQUIV-RANK.
{-@ reflect rankImageInsertion @-}
{-@ rankImageInsertion :: valueDominion:Dominion b -> insertion:DomanialInsertion a b
      -> {result:DomanialInsertion a Natural |
           applyInsertion result == rankImage valueDominion insertion
           && preimage result == rankImagePreimage valueDominion insertion} @-}
rankImageInsertion :: Dominion b -> DomanialInsertion a b -> DomanialInsertion a Natural
rankImageInsertion valueDominion insertion =
  DomanialInsertion
    (rankImage valueDominion insertion)
    (rankImagePreimage valueDominion insertion)
    (rankImageRoundTrip valueDominion insertion)

-- ALIGN: INSERTION-RANK-ROUNDTRIP.
{-@ reflect rankImageRoundTrip @-}
{-@
rankImageRoundTrip
  :: valueDominion:Dominion b
  -> insertion:DomanialInsertion a b
  -> value:a
  -> {proof:() | rankImagePreimage valueDominion insertion
       (rankImage valueDominion insertion value) == Just value}
@-}
rankImageRoundTrip :: Dominion b -> DomanialInsertion a b -> a -> ()
rankImageRoundTrip (Dominion _ _ coherence) insertion value =
  coherence (applyInsertion insertion value) `seq` insertionLeftInverse insertion value

-- ALIGN: INSERTION-RANK-SOUND.
{-@
rankImagePreimageSound
  :: valueDominion:Dominion b
  -> insertion:DomanialInsertion a b
  -> valueRank:Natural
  -> {value:a | rankImagePreimage valueDominion insertion valueRank == Just value}
  -> {proof:() | rankImage valueDominion insertion value == valueRank}
@-}
rankImagePreimageSound :: Dominion b -> DomanialInsertion a b -> Natural -> a -> ()
rankImagePreimageSound valueDominion insertion valueRank _ =
  case unrank valueDominion valueRank of
    Nothing -> ()
    Just rootDatum -> case preimage insertion rootDatum of
      Nothing -> ()
      Just _ -> ()
