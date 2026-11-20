{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | Resolved component cells and their checked membership transport.
module AtlasMerge.Source
  ( AtlasMergeSource (..)
  , leftMergeSource
  , rightMergeSource
  , mergeSourceValid
  , mergeSourceContains
  , mergeSourceContainsRetag
  , mergeSourceTransport
  , mergeSourceContainsPreserved
  ) where

import Atlas (Atlas)
import qualified AtlasExtent as Extent
  ( cellHasOrigin, cellTraceValid, extentContainsRank, cellContainsRank
  , cellContainsRankInExtent, cellContainsRankPreserved )
import AtlasMerge.Data (AtlasMergeDatum (..), retagMergeDatum)
import PageElements.Structure
  ( PageElement, SomePageElement (..), pageElementPrecedes, pageElementTransported, pageElementArrow )

data AtlasMergeSource leftScope rightScope
  = MergeOrigin
  | MergeLeftSource (SomePageElement leftScope)
  | MergeRightSource (SomePageElement rightScope)

{-@ reflect mergeSourceValid @-}
mergeSourceValid :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> AtlasMergeSource ls rs -> Bool
mergeSourceValid _ _ MergeOrigin = True
mergeSourceValid left _ (MergeLeftSource (SomePageElement source)) =
  Extent.cellHasOrigin left source && Extent.cellTraceValid left source
mergeSourceValid _ right (MergeRightSource (SomePageElement source)) =
  Extent.cellHasOrigin right source && Extent.cellTraceValid right source

{-@ reflect leftMergeSource @-}
{-@ leftMergeSource :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> source:{PageElement ls object | Extent.cellHasOrigin left source && Extent.cellTraceValid left source}
      -> {resolved:AtlasMergeSource ls rs | mergeSourceValid left right resolved
           && resolved == MergeLeftSource (SomePageElement source)} @-}
leftMergeSource :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> PageElement ls object -> AtlasMergeSource ls rs
leftMergeSource _ _ source = MergeLeftSource (SomePageElement source)

{-@ reflect rightMergeSource @-}
{-@ rightMergeSource :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> source:{PageElement rs object | Extent.cellHasOrigin right source && Extent.cellTraceValid right source}
      -> {resolved:AtlasMergeSource ls rs | mergeSourceValid left right resolved
           && resolved == MergeRightSource (SomePageElement source)} @-}
rightMergeSource :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> PageElement rs object -> AtlasMergeSource ls rs
rightMergeSource _ _ source = MergeRightSource (SomePageElement source)

-- ALIGN: MERGE-SOURCE-CELL-MEMBERSHIP.
{-@ reflect mergeSourceContains @-}
{-@ mergeSourceContains :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> source:{AtlasMergeSource ls rs | mergeSourceValid left right source}
      -> AtlasMergeDatum object -> Bool @-}
mergeSourceContains :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> AtlasMergeSource ls rs -> AtlasMergeDatum object -> Bool
mergeSourceContains left _ MergeOrigin (AtlasMergeLeftDatum rankValue) =
  Extent.extentContainsRank left rankValue
mergeSourceContains _ right MergeOrigin (AtlasMergeRightDatum rankValue) =
  Extent.extentContainsRank right rankValue
mergeSourceContains left _ (MergeLeftSource (SomePageElement source)) (AtlasMergeLeftDatum rankValue) =
  Extent.cellContainsRank left source rankValue
mergeSourceContains _ right (MergeRightSource (SomePageElement source)) (AtlasMergeRightDatum rankValue) =
  Extent.cellContainsRank right source rankValue
mergeSourceContains _ _ _ _ = False

-- ALIGN: MERGE-SOURCE-CELL-MEMBERSHIP-RETAG.
{-@ mergeSourceContainsRetag :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> source:{AtlasMergeSource ls rs | mergeSourceValid left right source}
      -> datum:AtlasMergeDatum object
      -> {mergeSourceContains left right source (retagMergeDatum datum)
           == mergeSourceContains left right source datum} @-}
mergeSourceContainsRetag :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> AtlasMergeSource ls rs -> AtlasMergeDatum object -> ()
mergeSourceContainsRetag _ _ MergeOrigin (AtlasMergeLeftDatum _) = ()
mergeSourceContainsRetag _ _ MergeOrigin (AtlasMergeRightDatum _) = ()
mergeSourceContainsRetag _ _ (MergeLeftSource _) (AtlasMergeLeftDatum _) = ()
mergeSourceContainsRetag _ _ (MergeLeftSource _) (AtlasMergeRightDatum _) = ()
mergeSourceContainsRetag _ _ (MergeRightSource _) (AtlasMergeLeftDatum _) = ()
mergeSourceContainsRetag _ _ (MergeRightSource _) (AtlasMergeRightDatum _) = ()

-- ALIGN: MERGE-SOURCE-CELL-TRANSPORT.
{-@ reflect mergeSourceTransport @-}
mergeSourceTransport :: AtlasMergeSource ls rs -> AtlasMergeSource ls rs -> Bool
mergeSourceTransport _ MergeOrigin = True
mergeSourceTransport (MergeLeftSource (SomePageElement source)) (MergeLeftSource (SomePageElement target)) =
  pageElementPrecedes source target && pageElementTransported source target
mergeSourceTransport (MergeRightSource (SomePageElement source)) (MergeRightSource (SomePageElement target)) =
  pageElementPrecedes source target && pageElementTransported source target
mergeSourceTransport _ _ = False

-- ALIGN: MERGE-SOURCE-CELL-MEMBERSHIP-PRESERVED.
{-@ mergeSourceContainsPreserved :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> source:{AtlasMergeSource ls rs | mergeSourceValid left right source}
      -> target:{AtlasMergeSource ls rs | mergeSourceValid left right target && mergeSourceTransport source target}
      -> datum:{AtlasMergeDatum object | mergeSourceContains left right source datum}
      -> {mergeSourceContains left right target (retagMergeDatum datum)} @-}
mergeSourceContainsPreserved :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> AtlasMergeSource ls rs -> AtlasMergeSource ls rs -> AtlasMergeDatum object -> ()
mergeSourceContainsPreserved left right MergeOrigin MergeOrigin datum =
  mergeSourceContainsRetag left right MergeOrigin datum
mergeSourceContainsPreserved left _ (MergeLeftSource (SomePageElement source)) MergeOrigin (AtlasMergeLeftDatum rankValue) =
  Extent.cellContainsRankInExtent left source rankValue
mergeSourceContainsPreserved _ right (MergeRightSource (SomePageElement source)) MergeOrigin (AtlasMergeRightDatum rankValue) =
  Extent.cellContainsRankInExtent right source rankValue
mergeSourceContainsPreserved left _ (MergeLeftSource (SomePageElement source)) (MergeLeftSource (SomePageElement target)) (AtlasMergeLeftDatum rankValue) =
  Extent.cellContainsRankPreserved left (pageElementArrow source target) rankValue
mergeSourceContainsPreserved _ right (MergeRightSource (SomePageElement source)) (MergeRightSource (SomePageElement target)) (AtlasMergeRightDatum rankValue) =
  Extent.cellContainsRankPreserved right (pageElementArrow source target) rankValue
mergeSourceContainsPreserved _ _ _ _ _ = ()
