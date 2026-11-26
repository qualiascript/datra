{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | The checked data action of an extent and its singleton regions.
module ChainedDominionAtlas.Action
  ( ChainedDominionCell (..)
  , chainValueAt
  , chainedDominionCell
  , cellNormalization
  , cellAccepts
  , cellPrecedes
  , cellMap
  , cellPreimage
  , cellInsertion
  , cellIdentity
  , cellComposition
  , composedCellPreimage
  , cellInverseComposition
  , cellDisjoint
  ) where

import Chain (Chain, chainPosition, chainPositionInjective, chainIndex, chainObjectAt)
import ChainedDominionAtlas.Data
  ( ChainedDominionCellData (..), extentAccepts, regionAccepts
  , regionToExtent, extentToRegion )
import DomanialInsertion.Core (DomanialInsertion (..), insertionOn)
import PageElements.Structure
  ( PageElement, pageElementPage, pageElementPosition, normalizePageElementAt, clampPage )

data ChainedDominionCell value = ExtentCell | RegionCell value

{-@ reflect chainValueAt @-}
-- ALIGN: CHAINED-PAGE-SELECTION.
chainValueAt :: value -> Chain value -> PageElement scope object -> value
chainValueAt first owner occurrence = case chainIndex owner (pageElementPosition occurrence) of
  Nothing -> first
  Just index -> chainObjectAt index

{-@ reflect chainedDominionCell @-}
-- ALIGN: CHAINED-PAGE-CELL.
chainedDominionCell :: value -> Chain value -> PageElement scope object -> ChainedDominionCell value
chainedDominionCell first owner occurrence
  | pageElementPage occurrence == 0 = ExtentCell
  | otherwise = RegionCell (chainValueAt first owner occurrence)

{-@ cellNormalization :: first:value -> owner:Chain value -> occurrence:PageElement scope object
      -> {chainedDominionCell first owner (normalizePageElementAt 1 2 occurrence)
           == chainedDominionCell first owner occurrence} @-}
-- ALIGN: CHAINED-PAGE-NORMALIZATION.
cellNormalization :: value -> Chain value -> PageElement scope object -> ()
cellNormalization _ _ occurrence
  | pageElementPage occurrence == 0 = ()
  | pageElementPage occurrence <= 1 = ()
  | otherwise = ()

{-@ reflect cellAccepts @-}
-- ALIGN: CHAINED-CELL-MEMBERSHIP.
cellAccepts :: Chain value -> ChainedDominionCell value -> ChainedDominionCellData value object -> Bool
cellAccepts _ ExtentCell datum = extentAccepts datum
cellAccepts owner (RegionCell selected) datum = regionAccepts owner selected datum

-- | A region maps to the extent or to another occurrence of that region.
{-@ reflect cellPrecedes @-}
-- ALIGN: CHAINED-CELL-ORDER.
cellPrecedes :: Chain value -> ChainedDominionCell value -> ChainedDominionCell value -> Bool
cellPrecedes _ ExtentCell ExtentCell = True
cellPrecedes _ ExtentCell (RegionCell _) = False
cellPrecedes _ (RegionCell _) ExtentCell = True
cellPrecedes owner (RegionCell source) (RegionCell target) =
  chainPosition owner source == chainPosition owner target

{-@ reflect retagCell @-}
-- ALIGN: CHAINED-CELL-RETAG.
retagCell :: ChainedDominionCellData value source -> ChainedDominionCellData value target
retagCell (ChainedDominionExtentDatum value) = ChainedDominionExtentDatum value
retagCell (ChainedDominionRegionDatum value) = ChainedDominionRegionDatum value

{-@ retagAccepts :: owner:Chain value -> cell:ChainedDominionCell value
      -> datum:ChainedDominionCellData value s
      -> {cellAccepts owner cell (retagCell datum) == cellAccepts owner cell datum} @-}
-- ALIGN: CHAINED-CELL-RETAG-MEMBERSHIP.
retagAccepts :: Chain value -> ChainedDominionCell value -> ChainedDominionCellData value source -> ()
retagAccepts _ ExtentCell (ChainedDominionExtentDatum _) = ()
retagAccepts _ ExtentCell (ChainedDominionRegionDatum _) = ()
retagAccepts _ (RegionCell _) (ChainedDominionExtentDatum _) = ()
retagAccepts _ (RegionCell _) (ChainedDominionRegionDatum _) = ()

{-@ reflect cellMap @-}
{-@ cellMap :: owner:Chain value -> source:ChainedDominionCell value
      -> target:{ChainedDominionCell value | cellPrecedes owner source target}
      -> datum:{ChainedDominionCellData value s | cellAccepts owner source datum}
      -> {result:ChainedDominionCellData value t | cellAccepts owner target result} @-}
-- ALIGN: CHAINED-CELL-FORWARD.
cellMap :: Chain value -> ChainedDominionCell value -> ChainedDominionCell value
  -> ChainedDominionCellData value source -> ChainedDominionCellData value target
cellMap owner ExtentCell ExtentCell datum = retagAccepts owner ExtentCell datum `seq` retagCell datum
cellMap _ ExtentCell (RegionCell _) datum = retagCell datum
cellMap owner (RegionCell selected) ExtentCell datum = regionToExtent owner selected datum
cellMap owner (RegionCell source) (RegionCell target) datum =
  chainPositionInjective owner source target `seq`
    retagAccepts owner (RegionCell source) datum `seq` retagCell datum

{-@ reflect cellPreimage @-}
{-@ cellPreimage :: owner:Chain value -> source:ChainedDominionCell value
      -> target:{ChainedDominionCell value | cellPrecedes owner source target}
      -> datum:{ChainedDominionCellData value t | cellAccepts owner target datum}
      -> Maybe ({result:ChainedDominionCellData value s | cellAccepts owner source result}) @-}
-- ALIGN: CHAINED-CELL-INVERSE.
cellPreimage :: Chain value -> ChainedDominionCell value -> ChainedDominionCell value
  -> ChainedDominionCellData value target -> Maybe (ChainedDominionCellData value source)
cellPreimage owner ExtentCell ExtentCell datum =
  retagAccepts owner ExtentCell datum `seq` Just (retagCell datum)
cellPreimage _ ExtentCell (RegionCell _) datum = Just (retagCell datum)
cellPreimage owner (RegionCell selected) ExtentCell datum = extentToRegion owner selected datum
cellPreimage owner (RegionCell source) (RegionCell target) datum =
  chainPositionInjective owner source target `seq`
    retagAccepts owner (RegionCell target) datum `seq` Just (retagCell datum)

{-@ cellRoundTrip :: owner:Chain value -> source:ChainedDominionCell value
      -> target:{ChainedDominionCell value | cellPrecedes owner source target}
      -> datum:{ChainedDominionCellData value s | cellAccepts owner source datum}
      -> {cellPreimage owner source target (cellMap owner source target datum) == Just datum} @-}
-- ALIGN: CHAINED-CELL-ROUNDTRIP.
cellRoundTrip :: Chain value -> ChainedDominionCell value -> ChainedDominionCell value
  -> ChainedDominionCellData value source -> ()
cellRoundTrip _ ExtentCell ExtentCell (ChainedDominionExtentDatum _) = ()
cellRoundTrip _ ExtentCell ExtentCell (ChainedDominionRegionDatum _) = ()
cellRoundTrip _ ExtentCell (RegionCell _) _ = ()
cellRoundTrip _ (RegionCell _) ExtentCell (ChainedDominionExtentDatum _) = ()
cellRoundTrip _ (RegionCell _) ExtentCell (ChainedDominionRegionDatum _) = ()
cellRoundTrip _ (RegionCell _) (RegionCell _) (ChainedDominionExtentDatum _) = ()
cellRoundTrip _ (RegionCell _) (RegionCell _) (ChainedDominionRegionDatum _) = ()

{-@ cellInsertion :: owner:Chain value -> source:ChainedDominionCell value
      -> target:{ChainedDominionCell value | cellPrecedes owner source target}
      -> {result:DomanialInsertion
           ({datum:ChainedDominionCellData value s | cellAccepts owner source datum})
           ({datum:ChainedDominionCellData value t | cellAccepts owner target datum}) |
           applyInsertion result == cellMap owner source target
           && preimage result == cellPreimage owner source target} @-}
-- ALIGN: CHAINED-CELL-INSERTION.
-- ALIGN: CHAINED-CELL-INSERTION-FORWARD.
-- ALIGN: CHAINED-CELL-INSERTION-INVERSE.
cellInsertion :: Chain value -> ChainedDominionCell value -> ChainedDominionCell value
  -> DomanialInsertion (ChainedDominionCellData value source) (ChainedDominionCellData value target)
cellInsertion owner source target =
  insertionOn (cellAccepts owner source) (cellAccepts owner target)
    (cellMap owner source target) (cellPreimage owner source target) (cellRoundTrip owner source target)

{-@ cellIdentity :: owner:Chain value -> cell:ChainedDominionCell value
      -> datum:{ChainedDominionCellData value object | cellAccepts owner cell datum}
      -> {cellMap owner cell cell datum == datum && cellPreimage owner cell cell datum == Just datum} @-}
-- ALIGN: CHAINED-CELL-IDENTITY.
cellIdentity :: Chain value -> ChainedDominionCell value -> ChainedDominionCellData value object -> ()
cellIdentity _ ExtentCell (ChainedDominionExtentDatum _) = ()
cellIdentity _ ExtentCell (ChainedDominionRegionDatum _) = ()
cellIdentity _ (RegionCell _) (ChainedDominionExtentDatum _) = ()
cellIdentity _ (RegionCell _) (ChainedDominionRegionDatum _) = ()

{-@ cellComposition :: owner:Chain value -> source:ChainedDominionCell value
      -> middle:{ChainedDominionCell value | cellPrecedes owner source middle}
      -> target:{ChainedDominionCell value | cellPrecedes owner middle target}
      -> datum:{ChainedDominionCellData value object | cellAccepts owner source datum}
      -> {cellPrecedes owner source target
           && cellMap owner middle target (cellMap owner source middle datum) == cellMap owner source target datum} @-}
-- ALIGN: CHAINED-CELL-COMPOSITION.
cellComposition :: Chain value -> ChainedDominionCell value -> ChainedDominionCell value
  -> ChainedDominionCell value -> ChainedDominionCellData value object -> ()
cellComposition _ source middle target datum = case source of
  ExtentCell -> case middle of
    ExtentCell -> case target of
      ExtentCell -> case datum of
        ChainedDominionExtentDatum _ -> ()
        ChainedDominionRegionDatum _ -> ()
      RegionCell _ -> ()
    RegionCell _ -> ()
  RegionCell _ -> case middle of
    ExtentCell -> case target of
      ExtentCell -> case datum of
        ChainedDominionExtentDatum _ -> ()
        ChainedDominionRegionDatum _ -> ()
      RegionCell _ -> ()
    RegionCell _ -> case target of
      ExtentCell -> case datum of
        ChainedDominionExtentDatum _ -> ()
        ChainedDominionRegionDatum _ -> ()
      RegionCell _ -> case datum of
        ChainedDominionExtentDatum _ -> ()
        ChainedDominionRegionDatum _ -> ()

{-@ reflect composedCellPreimage @-}
{-@ composedCellPreimage :: owner:Chain value -> source:ChainedDominionCell value
      -> middle:{ChainedDominionCell value | cellPrecedes owner source middle}
      -> target:{ChainedDominionCell value | cellPrecedes owner middle target}
      -> datum:{ChainedDominionCellData value t | cellAccepts owner target datum}
      -> Maybe ({result:ChainedDominionCellData value s | cellAccepts owner source result}) @-}
-- ALIGN: CHAINED-CELL-COMPOSE-INVERSE.
composedCellPreimage :: Chain value -> ChainedDominionCell value -> ChainedDominionCell value
  -> ChainedDominionCell value -> ChainedDominionCellData value target
  -> Maybe (ChainedDominionCellData value source)
composedCellPreimage owner source middle target datum =
  case cellPreimage owner middle target datum of
    Nothing -> Nothing
    Just intermediate -> cellPreimage owner source middle intermediate

{-@ cellInverseComposition :: owner:Chain value -> source:ChainedDominionCell value
      -> middle:{ChainedDominionCell value | cellPrecedes owner source middle}
      -> target:{ChainedDominionCell value | cellPrecedes owner middle target}
      -> datum:{ChainedDominionCellData value object | cellAccepts owner target datum}
      -> {cellPrecedes owner source target
           && composedCellPreimage owner source middle target datum == cellPreimage owner source target datum} @-}
-- ALIGN: CHAINED-CELL-INVERSE-COMPOSITION.
cellInverseComposition :: Chain value -> ChainedDominionCell value -> ChainedDominionCell value
  -> ChainedDominionCell value -> ChainedDominionCellData value object -> ()
cellInverseComposition owner source middle target datum = case source of
  ExtentCell -> case middle of
    ExtentCell -> case target of
      ExtentCell -> case datum of
        ChainedDominionExtentDatum _ -> ()
        ChainedDominionRegionDatum _ -> ()
      RegionCell _ -> ()
    RegionCell _ -> ()
  RegionCell _ -> case middle of
    ExtentCell -> case target of
      ExtentCell -> case datum of
        ChainedDominionExtentDatum _ -> ()
        ChainedDominionRegionDatum _ -> ()
      RegionCell _ -> ()
    RegionCell selected -> case target of
      ExtentCell -> case datum of
        ChainedDominionExtentDatum value ->
          if chainPosition owner value == chainPosition owner selected then () else ()
        ChainedDominionRegionDatum _ -> ()
      RegionCell _ -> case datum of
        ChainedDominionExtentDatum _ -> ()
        ChainedDominionRegionDatum _ -> ()

{-@ cellDisjoint :: owner:Chain value -> left:value -> right:value
      -> leftDatum:{ChainedDominionCellData value l | cellAccepts owner (RegionCell left) leftDatum}
      -> rightDatum:{ChainedDominionCellData value r | cellAccepts owner (RegionCell right) rightDatum}
      -> {cellMap owner (RegionCell left) ExtentCell leftDatum == cellMap owner (RegionCell right) ExtentCell rightDatum
           => chainPosition owner left == chainPosition owner right} @-}
-- ALIGN: CHAINED-CELL-DISJOINT.
cellDisjoint :: Chain value -> value -> value -> ChainedDominionCellData value left
  -> ChainedDominionCellData value right -> ()
cellDisjoint _ _ _ (ChainedDominionExtentDatum _) _ = ()
cellDisjoint _ _ _ (ChainedDominionRegionDatum _) (ChainedDominionExtentDatum _) = ()
cellDisjoint _ _ _ (ChainedDominionRegionDatum _) (ChainedDominionRegionDatum _) = ()
