{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

-- | Recover component transport from the constructed merge's native traces.
module AtlasMerge.Transport
  ( mergeNativeTransport, mergePrefixNativeTransport
  , mergeOccurrenceTraceValid, mergeGenuineArrowNativeTransport, mergeResolvedFiniteTransport ) where

import Atlas.Internal (Atlas, atlasFolio)
import AtlasMerge.Assembly (atlasMergeLength, atlasMergeFolio, atlasMergePrefix, atlasMergePrefixTrace, atlasMergeCellLookup)
import AtlasMerge.Page
  ( AtlasMergePageCell (..), atlasMergePageChain, mergePageContains, mergePagePosition, previousMergeCell )
import AtlasMerge.Resolution (mergeResolvedAt)
import AtlasMerge.Source (AtlasMergeSource (..), mergeSourceValid, mergeSourceTransport)
import qualified AtlasExtent.Internal as Extent (cellNativeTrace)
import Chain.Internal (chainPositionInjective)
import Numeric.Natural (Natural)
import PageElements.Internal (genuinePageElementTrace, folioTraceLookup, folioPageOrderType)
import PageElements.Structure
  ( PageElement (..), PageElementArrow (..), SomePageElement (..)
  , traceSuffix, traceSuffixTransitive, traceSuffixSameLength, traceSuffixDropHead )
import PageElements.TraceChain (genuineTraceHead, previousTraceSuffix)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- ALIGN: MERGE-NATIVE-TRANSPORT.
{-@ reflect mergeNativeTransport @-}
mergeNativeTransport :: AtlasMergePageCell -> AtlasMergePageCell -> Bool
mergeNativeTransport (AtlasMergeLeftCell source) (AtlasMergeLeftCell target) = traceSuffix source target
mergeNativeTransport (AtlasMergeRightCell source) (AtlasMergeRightCell target) = traceSuffix source target
mergeNativeTransport _ _ = False

{-@ mergeNativeTransportReflexive :: cell:AtlasMergePageCell -> {mergeNativeTransport cell cell} @-}
{-@ ple mergeNativeTransportReflexive @-}
mergeNativeTransportReflexive :: AtlasMergePageCell -> ()
mergeNativeTransportReflexive (AtlasMergeLeftCell _) = ()
mergeNativeTransportReflexive (AtlasMergeRightCell _) = ()

{-@ mergeNativeTransportTransitive :: source:AtlasMergePageCell
      -> middle:{AtlasMergePageCell | mergeNativeTransport source middle}
      -> target:{AtlasMergePageCell | mergeNativeTransport middle target}
      -> {mergeNativeTransport source target} @-}
{-@ ple mergeNativeTransportTransitive @-}
mergeNativeTransportTransitive :: AtlasMergePageCell -> AtlasMergePageCell -> AtlasMergePageCell -> ()
mergeNativeTransportTransitive (AtlasMergeLeftCell source) (AtlasMergeLeftCell middle) (AtlasMergeLeftCell target) =
  traceSuffixTransitive source middle target
mergeNativeTransportTransitive (AtlasMergeRightCell source) (AtlasMergeRightCell middle) (AtlasMergeRightCell target) =
  traceSuffixTransitive source middle target
mergeNativeTransportTransitive _ _ _ = ()

{-@ mergePreviousTransport :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> page:{Natural | page > 0}
      -> source:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) page source}
      -> {mergeNativeTransport source (previousMergeCell left right page source)} @-}
{-@ ple mergePreviousTransport @-}
mergePreviousTransport :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> AtlasMergePageCell -> ()
mergePreviousTransport _ _ _ (AtlasMergeLeftCell positions) = previousTraceSuffix positions
mergePreviousTransport _ _ _ (AtlasMergeRightCell positions) = previousTraceSuffix positions

{-@ mergePrefixSamePage :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf -> page:Natural
      -> source:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) page source}
      -> target:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) page target
           && traceSuffix (genuinePageElementTrace (atlasMergePrefix left right (page + 1)) source)
                (genuinePageElementTrace (atlasMergePrefix left right (page + 1)) target)}
      -> {source == target} @-}
{-@ ple mergePrefixSamePage @-}
mergePrefixSamePage :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural
  -> AtlasMergePageCell -> AtlasMergePageCell -> ()
mergePrefixSamePage left right page source target =
  let prefix = atlasMergePrefix left right (page + 1)
  in traceSuffixSameLength (genuinePageElementTrace prefix source) (genuinePageElementTrace prefix target) `seq`
    genuineTraceHead prefix source `seq` genuineTraceHead prefix target `seq`
    chainPositionInjective (atlasMergePageChain left right page) source target

-- ALIGN: MERGE-PREFIX-NATIVE-TRANSPORT.
{-@ mergePrefixNativeTransport :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> sourcePage:Natural -> targetPage:{Natural | targetPage <= sourcePage}
      -> source:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) sourcePage source}
      -> target:{AtlasMergePageCell | mergePageContains (atlasFolio left) (atlasFolio right) targetPage target
           && traceSuffix (genuinePageElementTrace (atlasMergePrefix left right (sourcePage + 1)) source)
                (genuinePageElementTrace (atlasMergePrefix left right (targetPage + 1)) target)}
      -> {mergeNativeTransport source target} / [sourcePage - targetPage] @-}
{-@ ple mergePrefixNativeTransport @-}
mergePrefixNativeTransport :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> Natural -> Natural
  -> AtlasMergePageCell -> AtlasMergePageCell -> ()
mergePrefixNativeTransport left right sourcePage targetPage source target
  | sourcePage == targetPage = mergePrefixSamePage left right sourcePage source target `seq`
      mergeNativeTransportReflexive source
  | otherwise =
      let previous = previousMergeCell left right sourcePage source
          sourceTrace = genuinePageElementTrace (atlasMergePrefix left right (sourcePage + 1)) source
          targetTrace = genuinePageElementTrace (atlasMergePrefix left right (targetPage + 1)) target
      in atlasMergePrefixTrace left right sourcePage source `seq`
        traceSuffixDropHead sourceTrace targetTrace `seq`
        mergePrefixNativeTransport left right (sourcePage - 1) targetPage previous target `seq`
        mergePreviousTransport left right sourcePage source `seq`
        mergeNativeTransportTransitive source previous target

-- ALIGN: MERGE-RAW-TRACE-VALIDITY.
{-@ reflect mergeOccurrenceTraceValid @-}
mergeOccurrenceTraceValid :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf -> PageElement ms object -> Bool
mergeOccurrenceTraceValid left right occurrence =
  folioTraceLookup (atlasMergeFolio left right) (pageElementPage occurrence) (pageElementPosition occurrence)
    == Just (pageElementTrace occurrence)

{-@ mergeGenuineOccurrenceTrace :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> occurrence:{PageElement ms object | mergeOccurrenceTraceValid left right occurrence
           && pageElementPage occurrence > 0 && pageElementPage occurrence < atlasMergeLength left right}
      -> cell:{AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) (pageElementPage occurrence - 1) cell
           && mergePagePosition (folioPageOrderType (atlasFolio left) (pageElementPage occurrence - 1)) cell
                == pageElementPosition occurrence}
      -> {pageElementTrace occurrence
           == genuinePageElementTrace (atlasMergePrefix left right (pageElementPage occurrence)) cell} @-}
{-@ ple mergeGenuineOccurrenceTrace @-}
mergeGenuineOccurrenceTrace :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElement ms object -> AtlasMergePageCell -> ()
mergeGenuineOccurrenceTrace left right occurrence cell =
  atlasMergeCellLookup left right (pageElementPage occurrence) cell

-- ALIGN: MERGE-GENUINE-ARROW-NATIVE-TRANSPORT.
{-@ mergeGenuineArrowNativeTransport :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> arrow:{PageElementArrow ms sourceObject targetObject |
           mergeOccurrenceTraceValid left right (arrowSource arrow)
           && mergeOccurrenceTraceValid left right (arrowTarget arrow)
           && pageElementPage (arrowTarget arrow) > 0
           && pageElementPage (arrowSource arrow) < atlasMergeLength left right}
      -> source:{AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) (pageElementPage (arrowSource arrow) - 1) source
           && mergePagePosition (folioPageOrderType (atlasFolio left) (pageElementPage (arrowSource arrow) - 1)) source
                == pageElementPosition (arrowSource arrow)}
      -> target:{AtlasMergePageCell |
           mergePageContains (atlasFolio left) (atlasFolio right) (pageElementPage (arrowTarget arrow) - 1) target
           && mergePagePosition (folioPageOrderType (atlasFolio left) (pageElementPage (arrowTarget arrow) - 1)) target
                == pageElementPosition (arrowTarget arrow)}
      -> {mergeNativeTransport source target} @-}
{-@ ple mergeGenuineArrowNativeTransport @-}
mergeGenuineArrowNativeTransport :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElementArrow ms sourceObject targetObject -> AtlasMergePageCell -> AtlasMergePageCell -> ()
mergeGenuineArrowNativeTransport left right arrow@(PageElementArrow _ _) source target =
  mergeGenuineOccurrenceTrace left right (arrowSource arrow) source `seq`
    mergeGenuineOccurrenceTrace left right (arrowTarget arrow) target `seq`
    mergePrefixNativeTransport left right (pageElementPage (arrowSource arrow) - 1)
      (pageElementPage (arrowTarget arrow) - 1) source target

-- ALIGN: MERGE-RESOLVED-FINITE-TRANSPORT.
{-@ mergeResolvedFiniteTransport :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> arrow:{PageElementArrow ms sourceObject targetObject |
           mergeOccurrenceTraceValid left right (arrowSource arrow)
           && mergeOccurrenceTraceValid left right (arrowTarget arrow)
           && pageElementPage (arrowSource arrow) < atlasMergeLength left right}
      -> source:{AtlasMergeSource ls rs | mergeSourceValid left right source
           && mergeResolvedAt left (arrowSource arrow) source}
      -> target:{AtlasMergeSource ls rs | mergeSourceValid left right target
           && mergeResolvedAt left (arrowTarget arrow) target}
      -> {mergeSourceTransport source target} @-}
{-@ ple mergeResolvedFiniteTransport @-}
mergeResolvedFiniteTransport :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElementArrow ms sourceObject targetObject -> AtlasMergeSource ls rs -> AtlasMergeSource ls rs -> ()
mergeResolvedFiniteTransport left right arrow@(PageElementArrow _ _)
    (MergeLeftSource (SomePageElement source)) (MergeLeftSource (SomePageElement target)) =
  Extent.cellNativeTrace left source `seq` Extent.cellNativeTrace left target `seq`
    mergeGenuineArrowNativeTransport left right arrow
      (AtlasMergeLeftCell (pageElementTrace source)) (AtlasMergeLeftCell (pageElementTrace target))
mergeResolvedFiniteTransport left right arrow@(PageElementArrow _ _)
    (MergeLeftSource (SomePageElement source)) (MergeRightSource (SomePageElement target)) =
  Extent.cellNativeTrace left source `seq` Extent.cellNativeTrace right target `seq`
    mergeGenuineArrowNativeTransport left right arrow
      (AtlasMergeLeftCell (pageElementTrace source)) (AtlasMergeRightCell (pageElementTrace target))
mergeResolvedFiniteTransport left right arrow@(PageElementArrow _ _)
    (MergeRightSource (SomePageElement source)) (MergeLeftSource (SomePageElement target)) =
  Extent.cellNativeTrace right source `seq` Extent.cellNativeTrace left target `seq`
    mergeGenuineArrowNativeTransport left right arrow
      (AtlasMergeRightCell (pageElementTrace source)) (AtlasMergeLeftCell (pageElementTrace target))
mergeResolvedFiniteTransport left right arrow@(PageElementArrow _ _)
    (MergeRightSource (SomePageElement source)) (MergeRightSource (SomePageElement target)) =
  Extent.cellNativeTrace right source `seq` Extent.cellNativeTrace right target `seq`
    mergeGenuineArrowNativeTransport left right arrow
      (AtlasMergeRightCell (pageElementTrace source)) (AtlasMergeRightCell (pageElementTrace target))
mergeResolvedFiniteTransport _ _ _ _ MergeOrigin = ()
mergeResolvedFiniteTransport _ _ (PageElementArrow _ _) MergeOrigin (MergeLeftSource (SomePageElement _)) = ()
mergeResolvedFiniteTransport _ _ (PageElementArrow _ _) MergeOrigin (MergeRightSource (SomePageElement _)) = ()
