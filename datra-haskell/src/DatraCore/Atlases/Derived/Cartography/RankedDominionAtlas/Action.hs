{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Checked ranked-cell actions, retaining both raw insertion directions.
module RankedDominionAtlas.Action
  ( RankedDominionCell, ChainedDominionCell (..)
  , spineRank, cellAt, cellNormalization, cellAccepts, cellPrecedes, cellDominion
  , cellMap, cellPreimage, cellInsertion
  , cellIdentity, cellComposition, composedCellPreimage, cellInverseComposition, cellDisjoint
  ) where

import ChainedDominionAtlas.Action (ChainedDominionCell (..))
import RankedDominionAtlas.Data
  ( RankedDominionCellData (..), cellValue, extentAccepts, regionAccepts
  , extentDominion, regionDominion )
import DatraOrdinal (Ordinal, naturalAtOrdinal)
import Dominion (Dominion, rank)
import DomanialInsertion.Core (DomanialInsertion (..), insertionOn)
import PageElements.Structure
  ( PageElement, pageElementPage, pageElementPosition, normalizePageElementAt, clampPage )
import Numeric.Natural (Natural)

{-@ opaque-reflect rank @-}

-- The two-page cell shape is shared with the chained construction.
type RankedDominionCell = ChainedDominionCell Natural

{-@ reflect spineRank @-}
spineRank :: Ordinal -> Natural
spineRank position = case naturalAtOrdinal position of
  Nothing -> 0
  Just index -> index

{-@ reflect cellAt @-}
cellAt :: PageElement scope object -> RankedDominionCell
cellAt occurrence
  | pageElementPage occurrence == 0 = ExtentCell
  | otherwise = RegionCell (spineRank (pageElementPosition occurrence))

{-@ cellNormalization :: occurrence:PageElement scope object
      -> {cellAt (normalizePageElementAt 1 2 occurrence) == cellAt occurrence} @-}
cellNormalization :: PageElement scope object -> ()
cellNormalization occurrence
  | pageElementPage occurrence == 0 = ()
  | pageElementPage occurrence <= 1 = ()
  | otherwise = ()

{-@ reflect cellAccepts @-}
cellAccepts :: Dominion value -> RankedDominionCell -> RankedDominionCellData value object -> Bool
cellAccepts _ ExtentCell datum = extentAccepts datum
cellAccepts owner (RegionCell selected) datum = regionAccepts owner selected datum

{-@ reflect cellPrecedes @-}
cellPrecedes :: RankedDominionCell -> RankedDominionCell -> Bool
cellPrecedes ExtentCell ExtentCell = True
cellPrecedes ExtentCell (RegionCell _) = False
cellPrecedes (RegionCell _) ExtentCell = True
cellPrecedes (RegionCell source) (RegionCell target) = source == target

{-@ cellDominion :: owner:Dominion value -> cell:RankedDominionCell
      -> Dominion ({datum:RankedDominionCellData value object | cellAccepts owner cell datum}) @-}
cellDominion :: Dominion value -> RankedDominionCell -> Dominion (RankedDominionCellData value object)
cellDominion owner ExtentCell = extentDominion owner
cellDominion owner (RegionCell selected) = regionDominion owner selected

{-@ reflect retagCell @-}
retagCell :: RankedDominionCellData value source -> RankedDominionCellData value target
retagCell (RankedDominionExtentDatum value) = RankedDominionExtentDatum value
retagCell (RankedDominionRegionDatum value) = RankedDominionRegionDatum value

{-@ retagAccepts :: owner:Dominion value -> cell:RankedDominionCell
      -> datum:RankedDominionCellData value s
      -> {cellAccepts owner cell (retagCell datum) == cellAccepts owner cell datum} @-}
retagAccepts :: Dominion value -> RankedDominionCell -> RankedDominionCellData value source -> ()
retagAccepts _ ExtentCell (RankedDominionExtentDatum _) = ()
retagAccepts _ ExtentCell (RankedDominionRegionDatum _) = ()
retagAccepts _ (RegionCell _) (RankedDominionExtentDatum _) = ()
retagAccepts _ (RegionCell _) (RankedDominionRegionDatum _) = ()

-- These callbacks also describe raw data outside the accepted carriers.
{-@ reflect cellMap @-}
{-@ cellMap :: owner:Dominion value -> source:RankedDominionCell -> target:RankedDominionCell
      -> datum:RankedDominionCellData value s
      -> {result:RankedDominionCellData value t |
           (cellPrecedes source target && cellAccepts owner source datum) => cellAccepts owner target result} @-}
cellMap :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> RankedDominionCellData value source -> RankedDominionCellData value target
cellMap owner ExtentCell target datum = retagAccepts owner target datum `seq` retagCell datum
cellMap _ (RegionCell _) ExtentCell datum = RankedDominionExtentDatum (cellValue datum)
cellMap owner (RegionCell _) target datum = retagAccepts owner target datum `seq` retagCell datum

{-@ reflect cellPreimage @-}
{-@ cellPreimage :: owner:Dominion value -> source:RankedDominionCell -> target:RankedDominionCell
      -> datum:RankedDominionCellData value t
      -> Maybe ({result:RankedDominionCellData value s |
           (cellPrecedes source target && cellAccepts owner target datum) => cellAccepts owner source result}) @-}
cellPreimage :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> RankedDominionCellData value target -> Maybe (RankedDominionCellData value source)
cellPreimage owner ExtentCell _ datum = retagAccepts owner ExtentCell datum `seq` Just (retagCell datum)
cellPreimage owner (RegionCell selected) ExtentCell datum =
  if rank owner (cellValue datum) == selected then Just (RankedDominionRegionDatum (cellValue datum)) else Nothing
cellPreimage owner source (RegionCell _) datum = retagAccepts owner source datum `seq` Just (retagCell datum)

{-@ cellRoundTrip :: owner:Dominion value -> source:RankedDominionCell
      -> target:{RankedDominionCell | cellPrecedes source target}
      -> datum:{RankedDominionCellData value s | cellAccepts owner source datum}
      -> {cellPreimage owner source target (cellMap owner source target datum) == Just datum} @-}
cellRoundTrip :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> RankedDominionCellData value source -> ()
cellRoundTrip _ ExtentCell ExtentCell (RankedDominionExtentDatum _) = ()
cellRoundTrip _ ExtentCell ExtentCell (RankedDominionRegionDatum _) = ()
cellRoundTrip _ ExtentCell (RegionCell _) _ = ()
cellRoundTrip _ (RegionCell _) ExtentCell (RankedDominionExtentDatum _) = ()
cellRoundTrip _ (RegionCell _) ExtentCell (RankedDominionRegionDatum _) = ()
cellRoundTrip _ (RegionCell _) (RegionCell _) (RankedDominionExtentDatum _) = ()
cellRoundTrip _ (RegionCell _) (RegionCell _) (RankedDominionRegionDatum _) = ()

{-@ cellInsertion :: owner:Dominion value -> source:RankedDominionCell
      -> target:{RankedDominionCell | cellPrecedes source target}
      -> {result:DomanialInsertion
           ({datum:RankedDominionCellData value s | cellAccepts owner source datum})
           ({datum:RankedDominionCellData value t | cellAccepts owner target datum}) |
           applyInsertion result == cellMap owner source target
           && preimage result == cellPreimage owner source target} @-}
cellInsertion :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> DomanialInsertion (RankedDominionCellData value source) (RankedDominionCellData value target)
cellInsertion owner source target =
  insertionOn (cellAccepts owner source) (cellAccepts owner target)
    (cellMap owner source target) (cellPreimage owner source target) (cellRoundTrip owner source target)

{-@ cellIdentity :: owner:Dominion value -> cell:RankedDominionCell
      -> datum:RankedDominionCellData value object
      -> {cellMap owner cell cell datum == datum && cellPreimage owner cell cell datum == Just datum} @-}
cellIdentity :: Dominion value -> RankedDominionCell -> RankedDominionCellData value object -> ()
cellIdentity _ ExtentCell (RankedDominionExtentDatum _) = ()
cellIdentity _ ExtentCell (RankedDominionRegionDatum _) = ()
cellIdentity _ (RegionCell _) (RankedDominionExtentDatum _) = ()
cellIdentity _ (RegionCell _) (RankedDominionRegionDatum _) = ()

{-@ cellComposition :: owner:Dominion value -> source:RankedDominionCell
      -> middle:{RankedDominionCell | cellPrecedes source middle}
      -> target:{RankedDominionCell | cellPrecedes middle target}
      -> datum:RankedDominionCellData value object
      -> {cellPrecedes source target
           && cellMap owner middle target (cellMap owner source middle datum) == cellMap owner source target datum} @-}
cellComposition :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> RankedDominionCell -> RankedDominionCellData value object -> ()
cellComposition _ source middle target datum = case source of
  ExtentCell -> case middle of
    ExtentCell -> case target of
      ExtentCell -> case datum of
        RankedDominionExtentDatum _ -> ()
        RankedDominionRegionDatum _ -> ()
      RegionCell _ -> ()
    RegionCell _ -> ()
  RegionCell _ -> case middle of
    ExtentCell -> case target of
      ExtentCell -> case datum of
        RankedDominionExtentDatum _ -> ()
        RankedDominionRegionDatum _ -> ()
      RegionCell _ -> ()
    RegionCell _ -> case target of
      ExtentCell -> case datum of
        RankedDominionExtentDatum _ -> ()
        RankedDominionRegionDatum _ -> ()
      RegionCell _ -> case datum of
        RankedDominionExtentDatum _ -> ()
        RankedDominionRegionDatum _ -> ()

{-@ reflect composedCellPreimage @-}
composedCellPreimage :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> RankedDominionCell -> RankedDominionCellData value target -> Maybe (RankedDominionCellData value source)
composedCellPreimage owner source middle target datum =
  case cellPreimage owner middle target datum of
    Nothing -> Nothing
    Just intermediate -> cellPreimage owner source middle intermediate

{-@ cellInverseComposition :: owner:Dominion value -> source:RankedDominionCell
      -> middle:{RankedDominionCell | cellPrecedes source middle}
      -> target:{RankedDominionCell | cellPrecedes middle target}
      -> datum:RankedDominionCellData value object
      -> {cellPrecedes source target
           && composedCellPreimage owner source middle target datum == cellPreimage owner source target datum} @-}
cellInverseComposition :: Dominion value -> RankedDominionCell -> RankedDominionCell
  -> RankedDominionCell -> RankedDominionCellData value object -> ()
cellInverseComposition _ source middle target datum = case source of
  ExtentCell -> case middle of
    ExtentCell -> case target of
      ExtentCell -> case datum of
        RankedDominionExtentDatum _ -> ()
        RankedDominionRegionDatum _ -> ()
      RegionCell _ -> ()
    RegionCell _ -> ()
  RegionCell _ -> case middle of
    ExtentCell -> case target of
      ExtentCell -> case datum of
        RankedDominionExtentDatum _ -> ()
        RankedDominionRegionDatum _ -> ()
      RegionCell _ -> ()
    RegionCell _ -> case target of
      ExtentCell -> case datum of
        RankedDominionExtentDatum _ -> ()
        RankedDominionRegionDatum _ -> ()
      RegionCell _ -> case datum of
        RankedDominionExtentDatum _ -> ()
        RankedDominionRegionDatum _ -> ()

{-@ cellDisjoint :: owner:Dominion value -> left:Natural -> right:Natural
      -> leftDatum:{RankedDominionCellData value l | cellAccepts owner (RegionCell left) leftDatum}
      -> rightDatum:{RankedDominionCellData value r | cellAccepts owner (RegionCell right) rightDatum}
      -> {cellMap owner (RegionCell left) ExtentCell leftDatum == cellMap owner (RegionCell right) ExtentCell rightDatum
           => left == right} @-}
cellDisjoint :: Dominion value -> Natural -> Natural -> RankedDominionCellData value left
  -> RankedDominionCellData value right -> ()
cellDisjoint _ _ _ (RankedDominionExtentDatum _) _ = ()
cellDisjoint _ _ _ (RankedDominionRegionDatum _) (RankedDominionExtentDatum _) = ()
cellDisjoint _ _ _ (RankedDominionRegionDatum _) (RankedDominionRegionDatum _) = ()
