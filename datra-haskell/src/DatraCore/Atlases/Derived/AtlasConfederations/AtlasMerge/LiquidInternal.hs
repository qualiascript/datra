{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Checked tagged ranks and membership-filtered decoding for Atlas merge.
module AtlasMerge.LiquidInternal
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
  ) where

import Numeric.Natural (Natural)

{-@ embed Natural as int @-}
{-@ invariant { value:Natural | value >= 0 } @-}

-- | Which input Atlas supplied a cell or datum in a merge.
data AtlasMergeSide = AtlasMergeLeft | AtlasMergeRight
  deriving (Eq, Show)

-- | A tagged origin rank. Membership in a particular cell is a separate
-- predicate checked by 'mergeDatumLookup'. The phantom retains cell identity.
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

{-@ reflect mergeDatumLookup @-}
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
