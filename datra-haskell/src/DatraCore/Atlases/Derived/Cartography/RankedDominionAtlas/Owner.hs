{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--etabeta" @-}
{-@ LIQUID "--fast" @-}

-- | Retain the original Dominion and the exact allocated ranked presentation.
module RankedDominionAtlas.Owner
  ( RankedDominionAtlas, RankedDominionAtlasObject
  , rankedDominionAtlas, rankedDominionValueDominion
  , rankedDominionMembership, rankedDominionTransport, rankedDominionInverseTransport
  , rankedDominionDataAt
  , retainRankedDominionAtlas, withRankedDominionAtlas
  ) where

import Atlas
  ( Atlas, AtlasObject, AtlasPresentation, atlasPagination, atlasPresentationPagination
  , atlasFolio, atlasPageElements, atlasDescription
  , atlasPresentationAction, atlasActionMembership, atlasActionDataAt, atlasActionMap, atlasMembership
  , atlasAcceptsDatum, atlasDescriptionMembership, atlasNormalizationAgrees, normalizeAtlasElement
  , mapAtlasData, normalizeAtlasArrow, normalizeAtlasArrowTraceValid, atlasArrowNormalizationAgrees
  , atlasDataAt, normalizeAtlasElementTraceValid
  , withAtlasPresentation )
import Chain (spine)
import Dominion (Dominion, rank, unrank)
import DomanialInsertion.Core (applyInsertion, preimage)
import Folio (folioLength, lastChain)
import Numeric.Natural (Natural)
import Pagination (paginationPageElements)
import PageElements (pageElementsFolio, PageElement, pageElementTraceValid)
import PageElements.Structure (PageElementArrow, arrowSource, arrowTarget)
import RankedDominionAtlas.Action (cellAt, cellMap, cellPreimage, cellRank, cellUnrank)
import RankedDominionAtlas.Data (RankedDominionCellData)
import RankedDominionAtlas.Pagination (RankedDominionPaginationScope, rankedPresentation)
import RankedDominionAtlas.Presentation
  ( rankedDominionAction, rankedDominionAccepts, rankedDominionAt, rankedDominionDataMap
  , ownedCellNormalization )

{-@ opaque-reflect spine @-}
{-@ opaque-reflect atlasDataAt @-}

type RankedDominionAtlasObject owner value =
  AtlasObject owner (RankedDominionPaginationScope value) (RankedDominionCellData value)

-- Preserve the indexed Atlas payload and its exact relation to the stored Dominion.
-- Selector measures expose constructor identities without unfolding allocation.
type role RankedDominionAtlasData nominal nominal
{-@ data variance RankedDominionAtlasData invariant invariant invariant @-}
{-@ data RankedDominionAtlasData dominion atlas
      <ownsAtlas :: dominion -> atlas -> Bool> = RankedDominionAtlas
      { storedDominion :: dominion
      , storedAtlas :: atlas<ownsAtlas storedDominion>
      } @-}
data RankedDominionAtlasData dominion atlas = RankedDominionAtlas
  { storedDominion :: dominion
  , storedAtlas :: atlas
  }

type RankedDominionAtlas owner value = RankedDominionAtlasData (Dominion value)
  (Atlas owner (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural)

{-@ type RankedDominionAtlas owner value = RankedDominionAtlasData
      <{\dominion valueAtlas ->
           atlasDescription valueAtlas == rankedPresentation dominion
           && folioLength (atlasFolio valueAtlas) == 2 && lastChain (atlasFolio valueAtlas) == spine
           && atlasPresentationAction (atlasDescription valueAtlas)
                == rankedDominionAction (atlasPageElements valueAtlas) dominion
           && atlasActionMembership (atlasPresentationAction (atlasDescription valueAtlas))
                == atlasMembership (rankedDominionAccepts dominion)
           && atlasActionDataAt (atlasPresentationAction (atlasDescription valueAtlas))
                == rankedDominionAt dominion
           && atlasActionMap (atlasPresentationAction (atlasDescription valueAtlas))
                == rankedDominionDataMap (atlasPageElements valueAtlas) dominion}>
      (Dominion value) (Atlas owner (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural) @-}

{-@ measure rankedDominionValueDominion @-}
{-@ ple rankedDominionValueDominion @-}
-- ALIGN: RANKED-OWNER-DOMINION.
{-@ rankedDominionValueDominion :: RankedDominionAtlas owner value -> Dominion value @-}
rankedDominionValueDominion :: RankedDominionAtlas owner value -> Dominion value
rankedDominionValueDominion (RankedDominionAtlas dominion _) = dominion

{-@ measure rankedDominionAtlas @-}
{-@ ple rankedDominionAtlas @-}
-- ALIGN: RANKED-OWNER-ATLAS.
-- ALIGN: RANKED-OWNER-CONTRACT.
{-@ rankedDominionAtlas :: owner:RankedDominionAtlas ownerScope value
      -> {valueAtlas:Atlas ownerScope (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural |
           atlasDescription valueAtlas == rankedPresentation (rankedDominionValueDominion owner)
           && folioLength (atlasFolio valueAtlas) == 2 && lastChain (atlasFolio valueAtlas) == spine
           && atlasPresentationAction (atlasDescription valueAtlas)
                == rankedDominionAction (atlasPageElements valueAtlas) (rankedDominionValueDominion owner)
           && atlasActionMembership (atlasPresentationAction (atlasDescription valueAtlas))
                == atlasMembership (rankedDominionAccepts (rankedDominionValueDominion owner))
           && atlasActionDataAt (atlasPresentationAction (atlasDescription valueAtlas))
                == rankedDominionAt (rankedDominionValueDominion owner)
           && atlasActionMap (atlasPresentationAction (atlasDescription valueAtlas))
                == rankedDominionDataMap (atlasPageElements valueAtlas) (rankedDominionValueDominion owner)} @-}
rankedDominionAtlas :: RankedDominionAtlas owner value
  -> Atlas owner (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural
rankedDominionAtlas (RankedDominionAtlas _ valueAtlas) = valueAtlas

{-@ ple rankedDominionMembership @-}
-- ALIGN: RANKED-OWNER-MEMBERSHIP.
{-@ rankedDominionMembership :: owner:RankedDominionAtlas ownerScope value
      -> occurrence:PageElement (RankedDominionPaginationScope value) object -> datum:RankedDominionCellData value object
      -> {atlasAcceptsDatum (rankedDominionAtlas owner) occurrence datum
           == rankedDominionAccepts (rankedDominionValueDominion owner) occurrence datum} @-}
rankedDominionMembership :: RankedDominionAtlas owner value
  -> PageElement (RankedDominionPaginationScope value) object -> RankedDominionCellData value object -> ()
rankedDominionMembership owner occurrence datum =
  let valueAtlas = rankedDominionAtlas owner
      dominion = rankedDominionValueDominion owner
  in atlasFolio valueAtlas `seq`
     atlasDescriptionMembership valueAtlas occurrence datum `seq`
     atlasNormalizationAgrees valueAtlas occurrence `seq`
     ownedCellNormalization (atlasPageElements valueAtlas) occurrence `seq`
     atlasMembership (rankedDominionAccepts dominion) `seq`
     rankedDominionAccepts dominion (normalizeAtlasElement valueAtlas occurrence) datum `seq`
     rankedDominionAccepts dominion occurrence datum `seq` ()

-- ALIGN: RANKED-OWNER-LOOKUP-RANK.
-- ALIGN: RANKED-OWNER-LOOKUP-DECODE.
{-@ ple rankedDominionDataAt @-}
{-@ rankedDominionDataAt :: owner:RankedDominionAtlas ownerScope value
      -> occurrence:{PageElement (RankedDominionPaginationScope value) object |
           pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) occurrence}
      -> {rank (atlasDataAt (rankedDominionAtlas owner) occurrence)
             == cellRank (rankedDominionValueDominion owner) (cellAt occurrence)
           && unrank (atlasDataAt (rankedDominionAtlas owner) occurrence)
             == cellUnrank (rankedDominionValueDominion owner) (cellAt occurrence)} @-}
rankedDominionDataAt :: RankedDominionAtlas ownerScope value
  -> PageElement (RankedDominionPaginationScope value) object -> ()
rankedDominionDataAt owner occurrence =
  let valueAtlas = rankedDominionAtlas owner
      dominion = rankedDominionValueDominion owner
  in atlasFolio valueAtlas `seq`
     atlasNormalizationAgrees valueAtlas occurrence `seq`
     normalizeAtlasElementTraceValid valueAtlas occurrence `seq`
     ownedCellNormalization (atlasPageElements valueAtlas) occurrence `seq`
     rankedDominionAt dominion (normalizeAtlasElement valueAtlas occurrence) `seq`
     atlasDataAt valueAtlas occurrence `seq` ()

-- Both observations use the same normalization and exact stored callbacks.
{-@ ple rankedActionAt @-}
{-@ rankedActionAt :: owner:RankedDominionAtlas ownerScope value
      -> arrow:{PageElementArrow (RankedDominionPaginationScope value) source target |
           pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) (arrowTarget arrow)}
      -> {mapAtlasData (rankedDominionAtlas owner) arrow
             == rankedDominionDataMap (atlasPageElements (rankedDominionAtlas owner))
                  (rankedDominionValueDominion owner) (normalizeAtlasArrow (rankedDominionAtlas owner) arrow)
           && cellAt (arrowSource (normalizeAtlasArrow (rankedDominionAtlas owner) arrow)) == cellAt (arrowSource arrow)
           && cellAt (arrowTarget (normalizeAtlasArrow (rankedDominionAtlas owner) arrow)) == cellAt (arrowTarget arrow)
           && pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner))
                (arrowSource (normalizeAtlasArrow (rankedDominionAtlas owner) arrow))
           && pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner))
                (arrowTarget (normalizeAtlasArrow (rankedDominionAtlas owner) arrow))} @-}
rankedActionAt :: RankedDominionAtlas owner value
  -> PageElementArrow (RankedDominionPaginationScope value) source target -> ()
rankedActionAt owner arrow =
  let valueAtlas = rankedDominionAtlas owner
      dominion = rankedDominionValueDominion owner
      category = atlasPageElements valueAtlas
  in atlasFolio valueAtlas `seq`
     atlasArrowNormalizationAgrees valueAtlas arrow `seq`
     normalizeAtlasArrowTraceValid valueAtlas arrow `seq`
     ownedCellNormalization category (arrowSource arrow) `seq`
     ownedCellNormalization category (arrowTarget arrow) `seq`
     rankedDominionDataMap category dominion (normalizeAtlasArrow valueAtlas arrow) `seq`
     mapAtlasData valueAtlas arrow `seq` ()

{-@ ple rankedDominionTransport @-}
-- ALIGN: RANKED-OWNER-TRANSPORT.
{-@ rankedDominionTransport :: owner:RankedDominionAtlas ownerScope value
      -> arrow:{PageElementArrow (RankedDominionPaginationScope value) source target |
           pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) (arrowTarget arrow)}
      -> datum:{RankedDominionCellData value source |
           atlasAcceptsDatum (rankedDominionAtlas owner) (arrowSource arrow) datum}
      -> {applyInsertion (mapAtlasData (rankedDominionAtlas owner) arrow) datum
           == cellMap (rankedDominionValueDominion owner) (cellAt (arrowSource arrow)) (cellAt (arrowTarget arrow)) datum} @-}
rankedDominionTransport :: RankedDominionAtlas owner value
  -> PageElementArrow (RankedDominionPaginationScope value) source target
  -> RankedDominionCellData value source -> ()
rankedDominionTransport owner arrow _ =
  rankedActionAt owner arrow `seq`
  let valueAtlas = rankedDominionAtlas owner
  in rankedDominionDataMap (atlasPageElements valueAtlas) (rankedDominionValueDominion owner)
       (normalizeAtlasArrow valueAtlas arrow) `seq` mapAtlasData valueAtlas arrow `seq` ()

{-@ ple rankedDominionInverseTransport @-}
-- ALIGN: RANKED-OWNER-INVERSE-TRANSPORT.
{-@ rankedDominionInverseTransport :: owner:RankedDominionAtlas ownerScope value
      -> arrow:{PageElementArrow (RankedDominionPaginationScope value) source target |
           pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements (rankedDominionAtlas owner)) (arrowTarget arrow)}
      -> datum:{RankedDominionCellData value target |
           atlasAcceptsDatum (rankedDominionAtlas owner) (arrowTarget arrow) datum}
      -> {preimage (mapAtlasData (rankedDominionAtlas owner) arrow) datum
           == cellPreimage (rankedDominionValueDominion owner) (cellAt (arrowSource arrow)) (cellAt (arrowTarget arrow)) datum} @-}
rankedDominionInverseTransport :: RankedDominionAtlas owner value
  -> PageElementArrow (RankedDominionPaginationScope value) source target
  -> RankedDominionCellData value target -> ()
rankedDominionInverseTransport owner arrow _ =
  rankedActionAt owner arrow `seq`
  let valueAtlas = rankedDominionAtlas owner
  in rankedDominionDataMap (atlasPageElements valueAtlas) (rankedDominionValueDominion owner)
       (normalizeAtlasArrow valueAtlas arrow) `seq` mapAtlasData valueAtlas arrow `seq` ()

-- ALIGN: RANKED-OWNER-RETAIN.
{-@ retainRankedDominionAtlas :: dominion:Dominion value
      -> valueAtlas:{Atlas owner (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural |
           atlasDescription valueAtlas == rankedPresentation dominion
           && folioLength (atlasFolio valueAtlas) == 2 && lastChain (atlasFolio valueAtlas) == spine
           && atlasPresentationAction (atlasDescription valueAtlas)
                == rankedDominionAction (atlasPageElements valueAtlas) dominion
           && atlasActionMembership (atlasPresentationAction (atlasDescription valueAtlas))
                == atlasMembership (rankedDominionAccepts dominion)
           && atlasActionDataAt (atlasPresentationAction (atlasDescription valueAtlas))
                == rankedDominionAt dominion
           && atlasActionMap (atlasPresentationAction (atlasDescription valueAtlas))
                == rankedDominionDataMap (atlasPageElements valueAtlas) dominion}
      -> {result:RankedDominionAtlas owner value |
           rankedDominionValueDominion result == dominion && rankedDominionAtlas result == valueAtlas} @-}
retainRankedDominionAtlas :: Dominion value
  -> Atlas owner (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural
  -> RankedDominionAtlas owner value
retainRankedDominionAtlas dominion valueAtlas = RankedDominionAtlas dominion valueAtlas

-- Establish the presentation observations on a concrete allocation before
-- passing the owner to the rank-polymorphic callback.
{-@ ple retainRankedPresentation @-}
-- ALIGN: RANKED-OWNER-RETAIN-PRESENTATION.
{-@ retainRankedPresentation :: dominion:Dominion value
      -> presentation:{AtlasPresentation (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural |
           presentation == rankedPresentation dominion
           && folioLength (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == 2
           && lastChain (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == spine
           && atlasPresentationAction presentation
                == rankedDominionAction (paginationPageElements (atlasPresentationPagination presentation)) dominion
           && atlasActionMembership (atlasPresentationAction presentation)
                == atlasMembership (rankedDominionAccepts dominion)
           && atlasActionDataAt (atlasPresentationAction presentation)
                == rankedDominionAt dominion
           && atlasActionMap (atlasPresentationAction presentation)
                == rankedDominionDataMap (paginationPageElements (atlasPresentationPagination presentation)) dominion}
      -> valueAtlas:{Atlas owner (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural |
           atlasDescription valueAtlas == presentation
           && atlasPagination valueAtlas == atlasPresentationPagination presentation}
      -> {result:RankedDominionAtlas owner value |
           rankedDominionValueDominion result == dominion && rankedDominionAtlas result == valueAtlas} @-}
retainRankedPresentation :: Dominion value
  -> AtlasPresentation (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural
  -> Atlas owner (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural
  -> RankedDominionAtlas owner value
retainRankedPresentation dominion _ valueAtlas =
  atlasFolio valueAtlas `seq` retainRankedDominionAtlas dominion valueAtlas

-- ALIGN: RANKED-OWNER-ALLOCATION.
{-@ withRankedDominionAtlas :: dominion:Dominion value
      -> (forall owner. result:{RankedDominionAtlas owner value |
           rankedDominionValueDominion result == dominion} -> resultValue) -> resultValue @-}
withRankedDominionAtlas :: Dominion value
  -> (forall owner. RankedDominionAtlas owner value -> result) -> result
withRankedDominionAtlas dominion useOwner =
  let presentation = rankedPresentation dominion
  in withAtlasPresentation presentation
    (\valueAtlas -> useOwner (retainRankedPresentation dominion presentation valueAtlas))
