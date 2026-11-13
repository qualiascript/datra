{-# LANGUAGE CPP #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ qualif SequenceAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | Checked finite-member rank encoding and cell-restricted decoding.
module AtlasSequence.LiquidInternal
  ( AtlasSequenceDatum (..)
  , atlasSequenceDatumMember
  , atlasSequenceDatumRank
  , sequenceDatumRank
  , decodeSequenceDatum
  , decodeSequenceDatumRank
  , sequenceDatumLookup
  , sequenceDatumLookupRoundTrip
  , sequenceDatumLookupSound
  , sequenceDatumDominion
  , retagSequenceDatum
  , retagSequenceDatumRoundTrip
  , sequenceDatumPreimage
  , sequenceDatumPreimageRoundTrip
  , sequenceDatumMap
  , sequenceDatumInsertion
  ) where

import Numeric.Natural (Natural)
import Dominion.Internal (Dominion, dominion)
import DomanialInsertion.LiquidInternal (DomanialInsertion (..))

{-@ embed Natural as int @-}
{-@ invariant { value:Natural | value >= 0 } @-}

-- | A member's origin rank, with nominal cell identity. Cell membership and
-- the member-index bound are carried by the checked Dominion refinement.
type role AtlasSequenceDatum nominal
data AtlasSequenceDatum object = AtlasSequenceDatum Natural Natural
  deriving (Eq, Show)

-- ALIGN: SEQUENCE-DATUM-MEMBER.
{-@ reflect atlasSequenceDatumMember @-}
atlasSequenceDatumMember :: AtlasSequenceDatum object -> Natural
atlasSequenceDatumMember (AtlasSequenceDatum member _) = member

-- ALIGN: SEQUENCE-DATUM-ORIGIN-RANK.
{-@ reflect atlasSequenceDatumRank @-}
atlasSequenceDatumRank :: AtlasSequenceDatum object -> Natural
atlasSequenceDatumRank (AtlasSequenceDatum _ valueRank) = valueRank

-- ALIGN: SEQUENCE-DATUM-RANK.
{-@ reflect sequenceDatumRank @-}
sequenceDatumRank :: Natural -> AtlasSequenceDatum object -> Natural
sequenceDatumRank count (AtlasSequenceDatum member valueRank) = count * valueRank + member

-- ALIGN: SEQUENCE-DATUM-ENCODE.
{-@ reflect decodeSequenceDatum @-}
{-@ decodeSequenceDatum :: count:{v:Natural | v > 0} -> combinedRank:Natural
      -> {datum:AtlasSequenceDatum object |
           atlasSequenceDatumMember datum < count
           && sequenceDatumRank count datum == combinedRank} @-}
decodeSequenceDatum :: Natural -> Natural -> AtlasSequenceDatum object
decodeSequenceDatum count combinedRank =
  AtlasSequenceDatum (combinedRank `mod` count) (combinedRank `div` count)

-- ALIGN: SEQUENCE-DATUM-DECODE.
{-@ decodeSequenceDatumRank :: count:{v:Natural | v > 0}
      -> datum:{v:AtlasSequenceDatum object | atlasSequenceDatumMember v < count}
      -> { decodeSequenceDatum count (sequenceDatumRank count datum) == datum } @-}
decodeSequenceDatumRank :: Natural -> AtlasSequenceDatum object -> ()
decodeSequenceDatumRank _ (AtlasSequenceDatum _ _) = ()

{-@ type SequenceDatumIn o N P = {datum:AtlasSequenceDatum o |
      atlasSequenceDatumMember datum < N && P datum} @-}

-- ALIGN: SEQUENCE-DATUM-LOOKUP.
{-@ reflect sequenceDatumLookup @-}
{-@ sequenceDatumLookup :: count:{v:Natural | v > 0}
      -> contains:(AtlasSequenceDatum object -> Bool)
      -> Natural -> Maybe (SequenceDatumIn object {count} {contains}) @-}
sequenceDatumLookup
  :: Natural -> (AtlasSequenceDatum object -> Bool)
  -> Natural -> Maybe (AtlasSequenceDatum object)
sequenceDatumLookup count contains combinedRank =
  let candidate = decodeSequenceDatum count combinedRank
  in if contains candidate then Just candidate else Nothing

-- ALIGN: SEQUENCE-DATUM-LOOKUP-ROUNDTRIP.
{-@ sequenceDatumLookupRoundTrip :: count:{v:Natural | v > 0}
      -> contains:(AtlasSequenceDatum object -> Bool)
      -> datum:SequenceDatumIn object {count} {contains}
      -> { sequenceDatumLookup count contains (sequenceDatumRank count datum) == Just datum } @-}
sequenceDatumLookupRoundTrip
  :: Natural -> (AtlasSequenceDatum object -> Bool) -> AtlasSequenceDatum object -> ()
sequenceDatumLookupRoundTrip count _ datum = decodeSequenceDatumRank count datum

-- ALIGN: SEQUENCE-DATUM-LOOKUP-SOUND.
{-@ sequenceDatumLookupSound :: count:{v:Natural | v > 0}
      -> contains:(AtlasSequenceDatum object -> Bool)
      -> combinedRank:Natural
      -> datum:{v:AtlasSequenceDatum object | sequenceDatumLookup count contains combinedRank == Just v}
      -> { contains datum && atlasSequenceDatumMember datum < count
           && sequenceDatumRank count datum == combinedRank } @-}
sequenceDatumLookupSound
  :: Natural -> (AtlasSequenceDatum object -> Bool)
  -> Natural -> AtlasSequenceDatum object -> ()
sequenceDatumLookupSound count contains combinedRank _
  | contains (decodeSequenceDatum count combinedRank) = ()
  | otherwise = ()

-- ALIGN: SEQUENCE-ACCEPTED-DOMINION.
{-@ sequenceDatumDominion :: count:{v:Natural | v > 0}
      -> contains:(AtlasSequenceDatum object -> Bool)
      -> Dominion (SequenceDatumIn object {count} {contains}) @-}
sequenceDatumDominion
  :: Natural -> (AtlasSequenceDatum object -> Bool) -> Dominion (AtlasSequenceDatum object)
sequenceDatumDominion count contains =
  dominion (sequenceDatumRank count) (sequenceDatumLookup count contains)
    (sequenceDatumLookupRoundTrip count contains)

-- ALIGN: SEQUENCE-DATUM-RETAG.
{-@ reflect retagSequenceDatum @-}
{-@ retagSequenceDatum :: datum:AtlasSequenceDatum source
      -> {result:AtlasSequenceDatum target |
           atlasSequenceDatumMember result == atlasSequenceDatumMember datum
           && atlasSequenceDatumRank result == atlasSequenceDatumRank datum} @-}
retagSequenceDatum :: AtlasSequenceDatum source -> AtlasSequenceDatum target
retagSequenceDatum (AtlasSequenceDatum member valueRank) = AtlasSequenceDatum member valueRank

-- ALIGN: SEQUENCE-DATUM-RETAG-ROUNDTRIP.
{-@ retagSequenceDatumRoundTrip :: datum:AtlasSequenceDatum source
      -> { retagSequenceDatum (retagSequenceDatum datum) == datum } @-}
retagSequenceDatumRoundTrip :: AtlasSequenceDatum source -> ()
retagSequenceDatumRoundTrip (AtlasSequenceDatum _ _) = ()

{-@ type SequenceCellDatum o P = {datum:AtlasSequenceDatum o | P datum} @-}

-- ALIGN: SEQUENCE-DATA-PREIMAGE.
{-@ reflect sequenceDatumPreimage @-}
{-@ sequenceDatumPreimage :: contains:(AtlasSequenceDatum source -> Bool)
      -> AtlasSequenceDatum target -> Maybe (SequenceCellDatum source {contains}) @-}
sequenceDatumPreimage
  :: (AtlasSequenceDatum source -> Bool)
  -> AtlasSequenceDatum target -> Maybe (AtlasSequenceDatum source)
sequenceDatumPreimage contains datum =
  let candidate = retagSequenceDatum datum
  in if contains candidate
      then Just candidate else Nothing

-- ALIGN: SEQUENCE-DATA-PREIMAGE-ROUNDTRIP.
{-@ sequenceDatumPreimageRoundTrip :: contains:(AtlasSequenceDatum source -> Bool)
      -> datum:SequenceCellDatum source {contains}
      -> { sequenceDatumPreimage contains (retagSequenceDatum datum) == Just datum } @-}
sequenceDatumPreimageRoundTrip
  :: (AtlasSequenceDatum source -> Bool) -> AtlasSequenceDatum source -> ()
sequenceDatumPreimageRoundTrip _ datum = retagSequenceDatumRoundTrip datum

-- ALIGN: SEQUENCE-DATA-MEMBERSHIP-MAP.
{-@ reflect sequenceDatumMap @-}
{-@ sequenceDatumMap
      :: sourceContains:(AtlasSequenceDatum source -> Bool)
      -> targetContains:(AtlasSequenceDatum target -> Bool)
      -> preserves:(datum:SequenceCellDatum source {sourceContains}
           -> { targetContains (retagSequenceDatum datum) })
      -> datum:SequenceCellDatum source {sourceContains}
      -> {result:AtlasSequenceDatum target | targetContains result && result == retagSequenceDatum datum} @-}
sequenceDatumMap
  :: (AtlasSequenceDatum source -> Bool)
  -> (AtlasSequenceDatum target -> Bool) -> (AtlasSequenceDatum source -> ())
  -> AtlasSequenceDatum source -> AtlasSequenceDatum target
sequenceDatumMap _ _ preserves datum = preserves datum `seq` retagSequenceDatum datum

-- ALIGN: SEQUENCE-ACCEPTED-INSERTION.
{-@ sequenceDatumInsertion
      :: sourceContains:(AtlasSequenceDatum source -> Bool)
      -> targetContains:(AtlasSequenceDatum target -> Bool)
      -> preserves:(datum:SequenceCellDatum source {sourceContains}
           -> { targetContains (retagSequenceDatum datum) })
      -> DomanialInsertion (SequenceCellDatum source {sourceContains})
           (SequenceCellDatum target {targetContains}) @-}
sequenceDatumInsertion
  :: (AtlasSequenceDatum source -> Bool)
  -> (AtlasSequenceDatum target -> Bool) -> (AtlasSequenceDatum source -> ())
  -> DomanialInsertion (AtlasSequenceDatum source) (AtlasSequenceDatum target)
sequenceDatumInsertion sourceContains targetContains preserves =
  DomanialInsertion
    (sequenceDatumMap sourceContains targetContains preserves)
    (sequenceDatumPreimage sourceContains)
    (\datum -> sequenceDatumMap sourceContains targetContains preserves datum `seq`
      sequenceDatumPreimageRoundTrip sourceContains datum)
