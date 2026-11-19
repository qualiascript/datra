{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}

#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Resolve merge cells while retaining their component's origin evidence.
module AtlasMerge.Resolution
  ( withMergeNativeCell
  , mergeSourceCell
  , resolveMergeCell
  , mergeResolvedAt
  , mergeCellContains
  ) where

import Atlas.Internal (Atlas, atlasFolio)
import qualified AtlasExtent.Internal as Extent hiding
  (atlasCellOriginRankInsertion, cellContainsRankImage, cellOriginRankPreimageSound)
import AtlasMerge.Source (AtlasMergeSource (..), leftMergeSource, rightMergeSource, mergeSourceValid, mergeSourceContains)
import AtlasMerge.Data (AtlasMergeDatum (..))
import AtlasMerge.Page (AtlasMergePageCell (..), atlasMergePageChain, mergePageContains, mergePagePosition)
import Chain (chainIndex, chainObjectAt)
import PageElements.Internal (traceLookupPresent, folioPageOrderType)
import Numeric.Natural (Natural)
import PageElements.Structure (PageElement (..), SomePageElement (..))

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- | Consume the exact component trace carried by an accepted native merge cell.
-- ALIGN: MERGE-NATIVE-CELL-RESOLUTION.
-- ALIGN: MERGE-NATIVE-CELL-RESOLUTION-INTERPRETATION.
{-@ withMergeNativeCell :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:Natural -> cell:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) page cell}
      -> (forall source. occurrence:{PageElement ls source | Extent.cellHasOrigin left occurrence
             && Extent.cellTraceValid left occurrence && pageElementPage occurrence == page
             && cell == AtlasMergeLeftCell (pageElementTrace occurrence)} -> result)
      -> (forall source. occurrence:{PageElement rs source | Extent.cellHasOrigin right occurrence
             && Extent.cellTraceValid right occurrence && pageElementPage occurrence == page
             && cell == AtlasMergeRightCell (pageElementTrace occurrence)} -> result)
      -> {resolved:Maybe result | traceLookupPresent resolved} @-}
withMergeNativeCell :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> AtlasMergePageCell
  -> (forall source. PageElement ls source -> result)
  -> (forall source. PageElement rs source -> result) -> Maybe result
withMergeNativeCell left _ page (AtlasMergeLeftCell positions) useLeft _ =
  Extent.withAtlasCellTrace left page positions useLeft
withMergeNativeCell _ right page (AtlasMergeRightCell positions) _ useRight =
  Extent.withAtlasCellTrace right page positions useRight

-- ALIGN: MERGE-PAGE-RESOLUTION.
-- ALIGN: MERGE-PADDED-PAGE-RESOLUTION.
-- ALIGN: MERGE-COMPONENT-DECODER.
-- ALIGN: MERGE-SOURCE-RESOLUTION.
-- ALIGN: MERGE-SOURCE-RESOLUTION-EQUIV.
-- ALIGN: MERGE-NORMALIZED-RESOLUTION.
{-@ mergeSourceCell
      :: left:Atlas la ls ld lo lf
      -> right:Atlas ra rs rd ro rf
      -> merged:PageElement ms object
      -> result
      -> (forall source. cell:{PageElement ls source | Extent.cellHasOrigin left cell && Extent.cellTraceValid left cell
             && pageElementPage cell + 1 == pageElementPage merged
             && mergePagePosition (folioPageOrderType (atlasFolio left) (pageElementPage cell))
                  (AtlasMergeLeftCell (pageElementTrace cell)) == pageElementPosition merged} -> result)
      -> (forall source. cell:{PageElement rs source | Extent.cellHasOrigin right cell && Extent.cellTraceValid right cell
             && pageElementPage cell + 1 == pageElementPage merged
             && mergePagePosition (folioPageOrderType (atlasFolio left) (pageElementPage cell))
                  (AtlasMergeRightCell (pageElementTrace cell)) == pageElementPosition merged} -> result)
      -> Maybe result @-}
mergeSourceCell
  :: Atlas la ls ld lo lf
  -> Atlas ra rs rd ro rf
  -> PageElement ms object
  -> result
  -> (forall source. PageElement ls source -> result)
  -> (forall source. PageElement rs source -> result)
  -> Maybe result
mergeSourceCell left right occurrence atOrigin useLeft useRight =
  case resolveMergeCell left right occurrence of
    Nothing -> Nothing
    Just MergeOrigin -> Just atOrigin
    Just (MergeLeftSource (SomePageElement source)) -> Just (useLeft source)
    Just (MergeRightSource (SomePageElement source)) -> Just (useRight source)

-- | The resolved cell has the same page and encoded position as the request.
{-@ reflect mergeResolvedAt @-}
mergeResolvedAt :: Atlas la ls ld lo lf -> PageElement ms object -> AtlasMergeSource ls rs -> Bool
mergeResolvedAt _ occurrence MergeOrigin = pageElementPage occurrence == 0
mergeResolvedAt left occurrence (MergeLeftSource (SomePageElement source)) =
  pageElementPage source + 1 == pageElementPage occurrence
    && mergePagePosition (folioPageOrderType (atlasFolio left) (pageElementPage source))
         (AtlasMergeLeftCell (pageElementTrace source)) == pageElementPosition occurrence
mergeResolvedAt left occurrence (MergeRightSource (SomePageElement source)) =
  pageElementPage source + 1 == pageElementPage occurrence
    && mergePagePosition (folioPageOrderType (atlasFolio left) (pageElementPage source))
         (AtlasMergeRightCell (pageElementTrace source)) == pageElementPosition occurrence

-- | Keep the successful callback as an explicit value for the data action.
-- ALIGN: MERGE-RESOLVED-LOOKUP-VALUE.
{-@ opaque-reflect resolveMergeCell @-}
{-@ resolveMergeCell :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> occurrence:PageElement ms object
      -> Maybe ({source:AtlasMergeSource ls rs | mergeSourceValid left right source
           && mergeResolvedAt left occurrence source}) @-}
resolveMergeCell :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> PageElement ms object
  -> Maybe (AtlasMergeSource ls rs)
resolveMergeCell left right occurrence
  | pageElementPage occurrence == 0 = Just MergeOrigin
  | otherwise =
      let componentPage = pageElementPage occurrence - 1
          position = pageElementPosition occurrence
      in case chainIndex (atlasMergePageChain left right componentPage) position of
          Nothing -> Nothing
          Just componentIndex ->
            withMergeNativeCell left right componentPage (chainObjectAt componentIndex)
              (leftMergeSource left right) (rightMergeSource left right)

-- ALIGN: MERGE-CELL-MEMBERSHIP.
-- ALIGN: MERGE-RESOLVED-CELL.
-- ALIGN: MERGE-BOUQUET-MEMBERSHIP.
{-@ reflect mergeCellContains @-}
mergeCellContains
  :: Atlas la ls ld lo lf
  -> Atlas ra rs rd ro rf
  -> PageElement ms object
  -> AtlasMergeDatum datumObject
  -> Bool
mergeCellContains left right occurrence datum =
  case resolveMergeCell left right occurrence of
    Nothing -> False
    Just source -> mergeSourceContains left right source datum
