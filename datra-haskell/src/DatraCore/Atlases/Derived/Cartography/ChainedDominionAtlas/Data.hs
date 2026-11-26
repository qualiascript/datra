{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Tagged carriers and checked cell Dominions for a chained Atlas.
module ChainedDominionAtlas.Data
  ( ChainedDominionCellData (..)
  , cellValue
  , extentAccepts
  , regionAccepts
  , extentRank
  , extentUnrank
  , extentRoundTrip
  , extentDominion
  , regionRank
  , regionUnrank
  , regionRoundTrip
  , regionDominion
  , regionToExtent
  , extentToRegion
  ) where

import Chain (Chain, chainPosition, chainPositionInjective)
import Dominion (Dominion, dominion, rank, unrank, dominionCoherence)
import Numeric.Natural (Natural)
import Data.Kind (Type)

{-@ opaque-reflect rank @-}
{-@ opaque-reflect unrank @-}

data ChainedDominionCellData value (object :: Type)
  = ChainedDominionExtentDatum value
  | ChainedDominionRegionDatum value
  deriving (Eq, Show)

{-@ reflect cellValue @-}
-- ALIGN: CHAINED-DATUM-VALUE.
cellValue :: ChainedDominionCellData value object -> value
cellValue (ChainedDominionExtentDatum value) = value
cellValue (ChainedDominionRegionDatum value) = value

{-@ reflect extentAccepts @-}
-- ALIGN: CHAINED-EXTENT-MEMBERSHIP.
extentAccepts :: ChainedDominionCellData value object -> Bool
extentAccepts (ChainedDominionExtentDatum _) = True
extentAccepts (ChainedDominionRegionDatum _) = False

{-@ reflect regionAccepts @-}
-- ALIGN: CHAINED-REGION-MEMBERSHIP.
regionAccepts :: Chain value -> value -> ChainedDominionCellData value object -> Bool
regionAccepts _ _ (ChainedDominionExtentDatum _) = False
regionAccepts owner selected (ChainedDominionRegionDatum value) =
  chainPosition owner value == chainPosition owner selected

{-@ reflect extentRank @-}
-- ALIGN: CHAINED-EXTENT-RANK.
extentRank :: Dominion value -> ChainedDominionCellData value object -> Natural
extentRank owner datum = rank owner (cellValue datum)

{-@ reflect extentUnrank @-}
{-@ extentUnrank :: Dominion value -> Natural
      -> Maybe ({datum:ChainedDominionCellData value object | extentAccepts datum}) @-}
-- ALIGN: CHAINED-EXTENT-DECODE.
extentUnrank :: Dominion value -> Natural -> Maybe (ChainedDominionCellData value object)
extentUnrank owner index = case unrank owner index of
  Nothing -> Nothing
  Just value -> Just (ChainedDominionExtentDatum value)

{-@ extentRoundTrip :: owner:Dominion value
      -> datum:{ChainedDominionCellData value object | extentAccepts datum}
      -> {extentUnrank owner (extentRank owner datum) == Just datum} @-}
-- ALIGN: CHAINED-EXTENT-ROUNDTRIP.
extentRoundTrip :: Dominion value -> ChainedDominionCellData value object -> ()
extentRoundTrip owner (ChainedDominionExtentDatum value) = dominionCoherence owner value
extentRoundTrip _ (ChainedDominionRegionDatum _) = ()

{-@ extentDominion :: owner:Dominion value
      -> {result:Dominion ({datum:ChainedDominionCellData value object | extentAccepts datum}) |
           rank result == extentRank owner && unrank result == extentUnrank owner} @-}
-- ALIGN: CHAINED-EXTENT-DOMINION.
-- ALIGN: CHAINED-EXTENT-DOMINION-DECODE.
extentDominion :: Dominion value -> Dominion (ChainedDominionCellData value object)
extentDominion owner = dominion (extentRank owner) (extentUnrank owner) (extentRoundTrip owner)

{-@ reflect regionRank @-}
-- ALIGN: CHAINED-REGION-RANK.
regionRank :: ChainedDominionCellData value object -> Natural
regionRank _ = 0

{-@ reflect regionUnrank @-}
{-@ regionUnrank :: owner:Chain value -> selected:value -> Natural
      -> Maybe ({datum:ChainedDominionCellData value object | regionAccepts owner selected datum}) @-}
-- ALIGN: CHAINED-REGION-DECODE.
regionUnrank :: Chain value -> value -> Natural -> Maybe (ChainedDominionCellData value object)
regionUnrank _ selected index =
  if index == 0 then Just (ChainedDominionRegionDatum selected) else Nothing

{-@ regionRoundTrip :: owner:Chain value -> selected:value
      -> datum:{ChainedDominionCellData value object | regionAccepts owner selected datum}
      -> {regionUnrank owner selected (regionRank datum) == Just datum} @-}
-- ALIGN: CHAINED-REGION-ROUNDTRIP.
regionRoundTrip :: Chain value -> value -> ChainedDominionCellData value object -> ()
regionRoundTrip _ _ (ChainedDominionExtentDatum _) = ()
regionRoundTrip owner selected (ChainedDominionRegionDatum value) =
  chainPositionInjective owner value selected

{-@ regionDominion :: owner:Chain value -> selected:value
      -> {result:Dominion ({datum:ChainedDominionCellData value object | regionAccepts owner selected datum}) |
           rank result == regionRank && unrank result == regionUnrank owner selected} @-}
-- ALIGN: CHAINED-REGION-DOMINION.
-- ALIGN: CHAINED-REGION-DOMINION-DECODE.
regionDominion :: Chain value -> value -> Dominion (ChainedDominionCellData value object)
regionDominion owner selected =
  dominion regionRank (regionUnrank owner selected) (regionRoundTrip owner selected)

{-@ reflect regionToExtent @-}
{-@ regionToExtent :: owner:Chain value -> selected:value
      -> {datum:ChainedDominionCellData value source | regionAccepts owner selected datum}
      -> {datum:ChainedDominionCellData value target | extentAccepts datum} @-}
-- ALIGN: CHAINED-REGION-TO-EXTENT.
regionToExtent :: Chain value -> value -> ChainedDominionCellData value source
  -> ChainedDominionCellData value target
regionToExtent _ _ datum = ChainedDominionExtentDatum (cellValue datum)

{-@ reflect extentToRegion @-}
{-@ extentToRegion :: owner:Chain value -> selected:value
      -> ChainedDominionCellData value target
      -> Maybe ({datum:ChainedDominionCellData value source | regionAccepts owner selected datum}) @-}
-- ALIGN: CHAINED-EXTENT-TO-REGION.
extentToRegion :: Chain value -> value -> ChainedDominionCellData value target
  -> Maybe (ChainedDominionCellData value source)
extentToRegion owner selected (ChainedDominionExtentDatum value)
  | chainPosition owner value == chainPosition owner selected = Just (ChainedDominionRegionDatum value)
  | otherwise = Nothing
extentToRegion _ _ (ChainedDominionRegionDatum _) = Nothing
