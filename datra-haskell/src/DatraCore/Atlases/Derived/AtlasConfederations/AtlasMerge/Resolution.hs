{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}

#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Resolve merge cells while retaining their component's origin evidence.
module AtlasMerge.Resolution
  ( mergeSourceCell
  , mergeCellContains
  ) where

import Atlas.Internal (Atlas, atlasFolio)
import qualified AtlasExtent.Internal as Extent hiding
  (atlasCellOriginRankInsertion, cellContainsRankImage, cellOriginRankPreimageSound)
import AtlasMerge.Data (AtlasMergeDatum (..))
import Chain (chainIndex, chainObjectAt, chainPosition, sumChains)
import Folio (withPageAt)
import Numeric.Natural (Natural)
import PageElements.Structure (PageElement (..))

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- ALIGN: MERGE-PAGE-RESOLUTION.
-- ALIGN: MERGE-PADDED-PAGE-RESOLUTION.
-- ALIGN: MERGE-COMPONENT-DECODER.
-- ALIGN: MERGE-SOURCE-RESOLUTION.
-- ALIGN: MERGE-SOURCE-RESOLUTION-EQUIV.
-- ALIGN: MERGE-NORMALIZED-RESOLUTION.
{-@ mergeSourceCell
      :: left:Atlas la ls ld lo lf
      -> right:Atlas ra rs rd ro rf
      -> PageElement ms object
      -> result
      -> (forall source. cell:{PageElement ls source | Extent.cellHasOrigin left cell && Extent.cellTraceValid left cell} -> result)
      -> (forall source. cell:{PageElement rs source | Extent.cellHasOrigin right cell && Extent.cellTraceValid right cell} -> result)
      -> Maybe result @-}
mergeSourceCell
  :: Atlas la ls ld lo lf
  -> Atlas ra rs rd ro rf
  -> PageElement ms object
  -> result
  -> (forall source. PageElement ls source -> result)
  -> (forall source. PageElement rs source -> result)
  -> Maybe result
mergeSourceCell left right occurrence atOrigin useLeft useRight
  | pageElementPage occurrence == 0 = Just atOrigin
  | otherwise =
      let componentPage :: Natural
          componentPage = pageElementPage occurrence - 1
          position = pageElementPosition occurrence
      in withPageAt (atlasFolio left) componentPage $ \leftPage ->
          withPageAt (atlasFolio right) componentPage $ \rightPage ->
            case chainIndex (sumChains leftPage rightPage) position of
              Nothing -> Nothing
              Just componentIndex -> case chainObjectAt componentIndex of
                Left value ->
                  Extent.withAtlasCellAt left componentPage (chainPosition leftPage value) useLeft
                Right value ->
                  Extent.withAtlasCellAt right componentPage (chainPosition rightPage value) useRight

-- ALIGN: MERGE-CELL-MEMBERSHIP.
-- ALIGN: MERGE-RESOLVED-CELL.
-- ALIGN: MERGE-BOUQUET-MEMBERSHIP.
mergeCellContains
  :: Atlas la ls ld lo lf
  -> Atlas ra rs rd ro rf
  -> PageElement ms object
  -> AtlasMergeDatum datumObject
  -> Bool
mergeCellContains left right occurrence datum =
  case mergeSourceCell left right occurrence
    (case datum of
      AtlasMergeLeftDatum valueRank -> Extent.extentContainsRank left valueRank
      AtlasMergeRightDatum valueRank -> Extent.extentContainsRank right valueRank)
    (\source -> case datum of
      AtlasMergeLeftDatum valueRank -> Extent.cellContainsRank left source valueRank
      AtlasMergeRightDatum _ -> False)
    (\source -> case datum of
      AtlasMergeLeftDatum _ -> False
      AtlasMergeRightDatum valueRank -> Extent.cellContainsRank right source valueRank) of
    Nothing -> False
    Just contains -> contains
