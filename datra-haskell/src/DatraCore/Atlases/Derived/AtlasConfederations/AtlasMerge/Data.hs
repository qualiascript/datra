{-# LANGUAGE CPP #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
-- Retain the cell predicate while inferring packaged function domains.
{-@ qualif MergeAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | Checked tagged ranks and membership-filtered decoding for Atlas merge.
module AtlasMerge.Data
  ( AtlasMergeSide (..)
  , AtlasMergeDatum (..)
  , atlasMergeDatumSide
  , atlasMergeDatumRank
  , retagMergeDatum
  , retagMergeDatumRoundTrip
  , decodeMergeDatum
  , decodeMergeDatumRank
  , mergeDatumLookup
  , mergeDatumLookupRoundTrip
  , mergeDatumLookupSound
  , mergeDatumDominion
  , mergeDatumPreimage
  , mergeDatumPreimageRoundTrip
  , mergeDatumMap
  , mergeDatumInsertion
  ) where

import Numeric.Natural (Natural)
import Dominion.Internal (Dominion, dominion)
import DomanialInsertion.Core (DomanialInsertion (..))

{-@ embed Natural as int @-}
{-@ invariant { value:Natural | value >= 0 } @-}

-- | Which input Atlas supplied a cell or datum in a merge.
data AtlasMergeSide = AtlasMergeLeft | AtlasMergeRight
  deriving (Eq, Show)

-- | A tagged origin rank. Membership in a particular cell is a separate
-- predicate checked by 'mergeDatumLookup'. The phantom retains cell identity.
type role AtlasMergeDatum nominal
data AtlasMergeDatum object
  = AtlasMergeLeftDatum Natural
  | AtlasMergeRightDatum Natural
  deriving (Eq, Show)

{-@ reflect atlasMergeDatumSide @-}
-- ALIGN: MERGE-DATUM-SIDE.
atlasMergeDatumSide :: AtlasMergeDatum object -> AtlasMergeSide
atlasMergeDatumSide (AtlasMergeLeftDatum _) = AtlasMergeLeft
atlasMergeDatumSide (AtlasMergeRightDatum _) = AtlasMergeRight

-- | Even ranks identify the left extent; odd ranks identify the right.
-- ALIGN: MERGE-DATUM-RANK.
{-@ reflect atlasMergeDatumRank @-}
atlasMergeDatumRank :: AtlasMergeDatum object -> Natural
atlasMergeDatumRank (AtlasMergeLeftDatum valueRank) = 2 * valueRank
atlasMergeDatumRank (AtlasMergeRightDatum valueRank) = 2 * valueRank + 1

-- ALIGN: MERGE-DATUM-RETAG-RANK.
{-@ reflect retagMergeDatum @-}
{-@ retagMergeDatum :: datum:AtlasMergeDatum source
      -> { target:AtlasMergeDatum target |
           atlasMergeDatumRank target == atlasMergeDatumRank datum } @-}
retagMergeDatum :: AtlasMergeDatum source -> AtlasMergeDatum target
retagMergeDatum (AtlasMergeLeftDatum valueRank) = AtlasMergeLeftDatum valueRank
retagMergeDatum (AtlasMergeRightDatum valueRank) = AtlasMergeRightDatum valueRank

-- ALIGN: MERGE-DATUM-RETAG-ROUNDTRIP.
{-@ retagMergeDatumRoundTrip :: datum:AtlasMergeDatum source
      -> { retagMergeDatum (retagMergeDatum datum) == datum } @-}
retagMergeDatumRoundTrip :: AtlasMergeDatum source -> ()
retagMergeDatumRoundTrip (AtlasMergeLeftDatum _) = ()
retagMergeDatumRoundTrip (AtlasMergeRightDatum _) = ()

{-@ reflect decodeMergeDatum @-}
{-@ decodeMergeDatum :: combinedRank:Natural
      -> { datum:AtlasMergeDatum object | atlasMergeDatumRank datum == combinedRank } @-}
-- ALIGN: MERGE-DATUM-ENCODE.
decodeMergeDatum :: Natural -> AtlasMergeDatum object
decodeMergeDatum combinedRank
  | combinedRank `mod` 2 == 0 = AtlasMergeLeftDatum (combinedRank `div` 2)
  | otherwise = AtlasMergeRightDatum (combinedRank `div` 2)

{-@ decodeMergeDatumRank :: datum:AtlasMergeDatum object
      -> { decodeMergeDatum (atlasMergeDatumRank datum) == datum } @-}
-- ALIGN: MERGE-DATUM-DECODE.
decodeMergeDatumRank :: AtlasMergeDatum object -> ()
decodeMergeDatumRank (AtlasMergeLeftDatum _) = ()
decodeMergeDatumRank (AtlasMergeRightDatum _) = ()

{-@ type MergeDatumIn o P = { datum:AtlasMergeDatum o | P datum } @-}

{-@ reflect mergeDatumLookup @-}
{-@ mergeDatumLookup :: contains:(AtlasMergeDatum object -> Bool)
      -> Natural -> Maybe (MergeDatumIn object {contains}) @-}
-- ALIGN: MERGE-DATUM-LOOKUP.
mergeDatumLookup
  :: (AtlasMergeDatum object -> Bool)
  -> Natural
  -> Maybe (AtlasMergeDatum object)
mergeDatumLookup contains combinedRank =
  let candidate = decodeMergeDatum combinedRank
  in if contains candidate then Just candidate else Nothing

{-@ mergeDatumLookupRoundTrip :: contains:(AtlasMergeDatum object -> Bool)
      -> datum:{ datum:AtlasMergeDatum object | contains datum }
      -> { mergeDatumLookup contains (atlasMergeDatumRank datum) == Just datum } @-}
-- ALIGN: MERGE-DATUM-LOOKUP-ROUNDTRIP.
mergeDatumLookupRoundTrip
  :: (AtlasMergeDatum object -> Bool)
  -> AtlasMergeDatum object
  -> ()
mergeDatumLookupRoundTrip _ datum = decodeMergeDatumRank datum

{-@ mergeDatumLookupSound :: contains:(AtlasMergeDatum object -> Bool)
      -> combinedRank:Natural
      -> datum:{ datum:AtlasMergeDatum object |
           mergeDatumLookup contains combinedRank == Just datum }
      -> { contains datum && atlasMergeDatumRank datum == combinedRank } @-}
-- ALIGN: MERGE-DATUM-LOOKUP-SOUND.
mergeDatumLookupSound
  :: (AtlasMergeDatum object -> Bool)
  -> Natural
  -> AtlasMergeDatum object
  -> ()
mergeDatumLookupSound contains combinedRank _
  | contains (decodeMergeDatum combinedRank) = ()
  | otherwise = ()

-- | The carrier is restricted to ranks accepted by this cell's predicate.
{-@ mergeDatumDominion :: contains:(AtlasMergeDatum object -> Bool)
      -> Dominion (MergeDatumIn object {contains}) @-}
-- ALIGN: MERGE-ACCEPTED-DOMINION.
mergeDatumDominion :: (AtlasMergeDatum object -> Bool) -> Dominion (AtlasMergeDatum object)
mergeDatumDominion contains =
  dominion atlasMergeDatumRank (mergeDatumLookup contains)
    (mergeDatumLookupRoundTrip contains)

-- | Test membership after retagging back to the source cell.
{-@ reflect mergeDatumPreimage @-}
{-@ mergeDatumPreimage :: contains:(AtlasMergeDatum source -> Bool)
      -> AtlasMergeDatum target -> Maybe (MergeDatumIn source {contains}) @-}
-- ALIGN: MERGE-DATA-PREIMAGE.
mergeDatumPreimage
  :: (AtlasMergeDatum source -> Bool)
  -> AtlasMergeDatum target
  -> Maybe (AtlasMergeDatum source)
mergeDatumPreimage contains datum =
  let candidate = retagMergeDatum datum
  in if contains candidate then Just candidate else Nothing

{-@ mergeDatumPreimageRoundTrip :: contains:(AtlasMergeDatum source -> Bool)
      -> datum:MergeDatumIn source {contains}
      -> { mergeDatumPreimage contains (retagMergeDatum datum) == Just datum } @-}
-- ALIGN: MERGE-DATA-PREIMAGE-ROUNDTRIP.
mergeDatumPreimageRoundTrip
  :: (AtlasMergeDatum source -> Bool)
  -> AtlasMergeDatum source
  -> ()
mergeDatumPreimageRoundTrip _ datum = retagMergeDatumRoundTrip datum

{-@ reflect mergeDatumMap @-}
{-@ mergeDatumMap
      :: sourceContains:(AtlasMergeDatum source -> Bool)
      -> targetContains:(AtlasMergeDatum target -> Bool)
      -> preserves:(datum:MergeDatumIn source {sourceContains}
           -> { targetContains (retagMergeDatum datum) })
      -> datum:MergeDatumIn source {sourceContains}
      -> { result:AtlasMergeDatum target |
           targetContains result && result == retagMergeDatum datum } @-}
-- ALIGN: MERGE-DATA-MEMBERSHIP-MAP.
mergeDatumMap
  :: (AtlasMergeDatum source -> Bool)
  -> (AtlasMergeDatum target -> Bool)
  -> (AtlasMergeDatum source -> ())
  -> AtlasMergeDatum source
  -> AtlasMergeDatum target
mergeDatumMap _ _ preserves datum = preserves datum `seq` retagMergeDatum datum

-- | Package the restricted insertion from membership-preservation evidence.
{-@ mergeDatumInsertion
      :: sourceContains:(AtlasMergeDatum source -> Bool)
      -> targetContains:(AtlasMergeDatum target -> Bool)
      -> preserves:(datum:MergeDatumIn source {sourceContains}
           -> { targetContains (retagMergeDatum datum) })
      -> DomanialInsertion (MergeDatumIn source {sourceContains})
           (MergeDatumIn target {targetContains}) @-}
-- ALIGN: MERGE-ACCEPTED-INSERTION.
-- ALIGN: MERGE-ACCEPTED-INSERTION-PREIMAGE.
mergeDatumInsertion
  :: (AtlasMergeDatum source -> Bool)
  -> (AtlasMergeDatum target -> Bool)
  -> (AtlasMergeDatum source -> ())
  -> DomanialInsertion (AtlasMergeDatum source) (AtlasMergeDatum target)
mergeDatumInsertion sourceContains targetContains preserves =
  DomanialInsertion
    (mergeDatumMap sourceContains targetContains preserves)
    (mergeDatumPreimage sourceContains)
    (\datum -> mergeDatumMap sourceContains targetContains preserves datum `seq`
      mergeDatumPreimageRoundTrip sourceContains datum)
