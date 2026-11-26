{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Ranked cell carriers with checked decoding and round-trip laws.
module RankedDominionAtlas.Data
  ( RankedDominionCellData (..), cellValue
  , extentAccepts, extentRank, extentUnrank, extentRoundTrip, extentDominion
  , regionAccepts, regionRank, regionUnrank, regionRoundTrip, regionDominion
  ) where

import Data.Kind (Type)
import Dominion (Dominion, dominion, rank, unrank, dominionCoherence, lookupRank, lookupRankRoundTrip)
import Numeric.Natural (Natural)

{-@ opaque-reflect rank @-}
{-@ opaque-reflect unrank @-}

data RankedDominionCellData value (object :: Type)
  = RankedDominionExtentDatum value
  | RankedDominionRegionDatum value
  deriving (Eq, Show)

-- ALIGN: RANKED-DATUM-VALUE.
{-@ reflect cellValue @-}
cellValue :: RankedDominionCellData value object -> value
cellValue (RankedDominionExtentDatum value) = value
cellValue (RankedDominionRegionDatum value) = value

{-@ reflect extentAccepts @-}
-- ALIGN: RANKED-EXTENT-MEMBERSHIP.
extentAccepts :: RankedDominionCellData value object -> Bool
extentAccepts (RankedDominionExtentDatum _) = True
extentAccepts (RankedDominionRegionDatum _) = False

{-@ reflect regionAccepts @-}
-- ALIGN: RANKED-REGION-MEMBERSHIP.
regionAccepts :: Dominion value -> Natural -> RankedDominionCellData value object -> Bool
regionAccepts _ _ (RankedDominionExtentDatum _) = False
regionAccepts owner selected (RankedDominionRegionDatum value) = rank owner value == selected

{-@ reflect extentRank @-}
-- ALIGN: RANKED-EXTENT-RANK.
extentRank :: Dominion value -> RankedDominionCellData value object -> Natural
extentRank owner datum = rank owner (cellValue datum)

{-@ reflect extentUnrank @-}
{-@ extentUnrank :: Dominion value -> Natural
      -> Maybe ({datum:RankedDominionCellData value object | extentAccepts datum}) @-}
-- ALIGN: RANKED-EXTENT-DECODE.
extentUnrank :: Dominion value -> Natural -> Maybe (RankedDominionCellData value object)
extentUnrank owner index = case unrank owner index of
  Nothing -> Nothing
  Just value -> Just (RankedDominionExtentDatum value)

{-@ extentRoundTrip :: owner:Dominion value
      -> datum:{RankedDominionCellData value object | extentAccepts datum}
      -> {extentUnrank owner (extentRank owner datum) == Just datum} @-}
-- ALIGN: RANKED-EXTENT-ROUNDTRIP.
extentRoundTrip :: Dominion value -> RankedDominionCellData value object -> ()
extentRoundTrip owner (RankedDominionExtentDatum value) = dominionCoherence owner value
extentRoundTrip _ (RankedDominionRegionDatum _) = ()

{-@ extentDominion :: owner:Dominion value
      -> {result:Dominion ({datum:RankedDominionCellData value object | extentAccepts datum}) |
           rank result == extentRank owner && unrank result == extentUnrank owner} @-}
-- ALIGN: RANKED-EXTENT-DOMINION.
-- ALIGN: RANKED-EXTENT-DOMINION-DECODE.
extentDominion :: Dominion value -> Dominion (RankedDominionCellData value object)
extentDominion owner = dominion (extentRank owner) (extentUnrank owner) (extentRoundTrip owner)

{-@ reflect regionRank @-}
-- ALIGN: RANKED-REGION-RANK.
regionRank :: RankedDominionCellData value object -> Natural
regionRank _ = 0

{-@ reflect regionUnrank @-}
{-@ regionUnrank :: owner:Dominion value -> selected:Natural -> Natural
      -> Maybe ({datum:RankedDominionCellData value object | regionAccepts owner selected datum}) @-}
-- ALIGN: RANKED-REGION-DECODE.
regionUnrank :: Dominion value -> Natural -> Natural -> Maybe (RankedDominionCellData value object)
regionUnrank owner selected index =
  if index == 0 then case lookupRank owner selected of
    Nothing -> Nothing
    Just value -> Just (RankedDominionRegionDatum value)
  else Nothing

{-@ regionRoundTrip :: owner:Dominion value -> selected:Natural
      -> datum:{RankedDominionCellData value object | regionAccepts owner selected datum}
      -> {regionUnrank owner selected (regionRank datum) == Just datum} @-}
-- ALIGN: RANKED-REGION-ROUNDTRIP.
regionRoundTrip :: Dominion value -> Natural -> RankedDominionCellData value object -> ()
regionRoundTrip _ _ (RankedDominionExtentDatum _) = ()
regionRoundTrip owner _ (RankedDominionRegionDatum value) = lookupRankRoundTrip owner value

{-@ regionDominion :: owner:Dominion value -> selected:Natural
      -> {result:Dominion ({datum:RankedDominionCellData value object | regionAccepts owner selected datum}) |
           rank result == regionRank && unrank result == regionUnrank owner selected} @-}
-- ALIGN: RANKED-REGION-DOMINION.
-- ALIGN: RANKED-REGION-DOMINION-DECODE.
regionDominion :: Dominion value -> Natural -> Dominion (RankedDominionCellData value object)
regionDominion owner selected = dominion regionRank (regionUnrank owner selected) (regionRoundTrip owner selected)
