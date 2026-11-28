{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
-- Keep the indexed Atlas payload intact when storing rank-polymorphic callbacks.
{-@ LIQUID "--fast" @-}

-- | Retain the exact construction data and checked action across allocation.
module ChainedDominionAtlas.Owner
  ( ChainedDominionAtlas, ChainedDominionAtlasObject
  , chainedDominionAtlas, chainedDominionFirst, chainedDominionChain, chainedDominionValueDominion
  , chainedDominionMembership, chainedDominionTransport
  , retainChainedDominionAtlas, retainChainedPresentation, withChainedDominionAtlas
  ) where

import Atlas
  ( Atlas, AtlasObject, AtlasPresentation, atlasFolio, atlasPageElements, atlasPagination, atlasDescription
  , atlasPresentationPagination
  , atlasPresentationAction, atlasActionMembership, atlasActionDataAt, atlasActionMap, atlasMembership
  , atlasAcceptsDatum, atlasDescriptionMembership, atlasNormalizationAgrees, normalizeAtlasElement
  , mapAtlasData, normalizeAtlasArrow, normalizeAtlasArrowTraceValid, atlasArrowNormalizationAgrees
  , withAtlasPresentation )
import Chain (Chain)
import ChainedDominionAtlas.Action (chainedDominionCell, cellMap)
import ChainedDominionAtlas.Data (ChainedDominionCellData)
import ChainedDominionAtlas.Presentation
  ( chainedDominionFolio, chainedDominionPresentation, chainedDominionAction
  , chainedDominionAccepts, chainedDominionAt, chainedDominionDataMap, ownedCellNormalization )
import Dominion (Dominion)
import DomanialInsertion.Core (applyInsertion)
import Folio (folioLength, lastChain)
import PageElements (PageElement, pageElementsFolio, pageElementTraceValid)
import PageElements.Structure (PageElementArrow, arrowSource, arrowTarget)
import Pagination (Pagination, pagination, paginationPageElements)

type ChainedDominionAtlasObject owner scope value =
  AtlasObject owner scope (ChainedDominionCellData value)

-- Parameterize the stored Atlas so the SMT record does not erase its indexed
-- datum family. The predicate relates that payload to all three stored inputs.
type role ChainedDominionAtlasData nominal nominal
{-@ data variance ChainedDominionAtlasData invariant invariant invariant @-}
{-@ data ChainedDominionAtlasData value atlas
      <ownsAtlas :: value -> Chain value -> Dominion value -> atlas -> Bool> = ChainedDominionAtlas
      { storedFirst :: value
      , storedChain :: Chain value
      , storedDominion :: Dominion value
      , storedAtlas :: atlas<ownsAtlas storedFirst storedChain storedDominion>
      } @-}
data ChainedDominionAtlasData value atlas = ChainedDominionAtlas
  { storedFirst :: value
  , storedChain :: Chain value
  , storedDominion :: Dominion value
  , storedAtlas :: atlas
  }

type ChainedDominionAtlas owner scope value =
  ChainedDominionAtlasData value (Atlas owner scope (ChainedDominionCellData value) () value)

{-@ type ChainedDominionAtlas owner scope value = ChainedDominionAtlasData
      <{\first chain dominion valueAtlas ->
           folioLength (atlasFolio valueAtlas) == 2 && lastChain (atlasFolio valueAtlas) == chain
           && atlasPresentationAction (atlasDescription valueAtlas)
                == chainedDominionAction (atlasPageElements valueAtlas) first chain dominion
           && atlasActionMembership (atlasPresentationAction (atlasDescription valueAtlas))
                == atlasMembership (chainedDominionAccepts first chain)
           && atlasActionDataAt (atlasPresentationAction (atlasDescription valueAtlas))
                == chainedDominionAt first chain dominion
           && atlasActionMap (atlasPresentationAction (atlasDescription valueAtlas))
                == chainedDominionDataMap (atlasPageElements valueAtlas) first chain}>
      value (Atlas owner scope (ChainedDominionCellData value) () value) @-}

-- ALIGN: CHAINED-OWNER-FIRST.
{-@ reflect chainedDominionFirst @-}
{-@ chainedDominionFirst :: ChainedDominionAtlas owner scope value -> value @-}
chainedDominionFirst :: ChainedDominionAtlas owner scope value -> value
chainedDominionFirst (ChainedDominionAtlas first _ _ _) = first

-- ALIGN: CHAINED-OWNER-CHAIN.
{-@ reflect chainedDominionChain @-}
{-@ chainedDominionChain :: ChainedDominionAtlas owner scope value -> Chain value @-}
chainedDominionChain :: ChainedDominionAtlas owner scope value -> Chain value
chainedDominionChain (ChainedDominionAtlas _ chain _ _) = chain

-- ALIGN: CHAINED-OWNER-DOMINION.
{-@ reflect chainedDominionValueDominion @-}
{-@ chainedDominionValueDominion :: ChainedDominionAtlas owner scope value -> Dominion value @-}
chainedDominionValueDominion :: ChainedDominionAtlas owner scope value -> Dominion value
chainedDominionValueDominion (ChainedDominionAtlas _ _ dominion _) = dominion

{-@ reflect chainedDominionAtlas @-}
-- ALIGN: CHAINED-OWNER-ATLAS.
-- ALIGN: CHAINED-OWNER-CONTRACT.
{-@ chainedDominionAtlas :: owner:ChainedDominionAtlas ownerScope scope value
      -> {valueAtlas:Atlas ownerScope scope (ChainedDominionCellData value) () value |
           folioLength (atlasFolio valueAtlas) == 2
           && lastChain (atlasFolio valueAtlas) == chainedDominionChain owner
           && atlasPresentationAction (atlasDescription valueAtlas)
                == chainedDominionAction (atlasPageElements valueAtlas) (chainedDominionFirst owner) (chainedDominionChain owner) (chainedDominionValueDominion owner)
           && atlasActionMembership (atlasPresentationAction (atlasDescription valueAtlas))
                == atlasMembership (chainedDominionAccepts (chainedDominionFirst owner) (chainedDominionChain owner))
           && atlasActionDataAt (atlasPresentationAction (atlasDescription valueAtlas))
                == chainedDominionAt (chainedDominionFirst owner) (chainedDominionChain owner) (chainedDominionValueDominion owner)
           && atlasActionMap (atlasPresentationAction (atlasDescription valueAtlas))
                == chainedDominionDataMap (atlasPageElements valueAtlas) (chainedDominionFirst owner) (chainedDominionChain owner)} @-}
chainedDominionAtlas :: ChainedDominionAtlas owner scope value
  -> Atlas owner scope (ChainedDominionCellData value) () value
chainedDominionAtlas (ChainedDominionAtlas _ _ _ valueAtlas) = valueAtlas

-- | The allocated Atlas tests the same restricted carrier as its presentation,
-- including on padded occurrences.
-- ALIGN: CHAINED-OWNER-MEMBERSHIP.
{-@ chainedDominionMembership :: owner:ChainedDominionAtlas ownerScope scope value
      -> occurrence:PageElement scope object -> datum:ChainedDominionCellData value object
      -> {atlasAcceptsDatum (chainedDominionAtlas owner) occurrence datum
           == chainedDominionAccepts (chainedDominionFirst owner) (chainedDominionChain owner) occurrence datum} @-}
chainedDominionMembership :: ChainedDominionAtlas ownerScope scope value
  -> PageElement scope object -> ChainedDominionCellData value object -> ()
chainedDominionMembership owner occurrence datum =
  let valueAtlas = chainedDominionAtlas owner
      first = chainedDominionFirst owner
      chain = chainedDominionChain owner
  in atlasFolio valueAtlas `seq`
     atlasDescriptionMembership valueAtlas occurrence datum `seq`
     atlasNormalizationAgrees valueAtlas occurrence `seq`
     ownedCellNormalization (atlasPageElements valueAtlas) first chain occurrence `seq`
     atlasMembership (chainedDominionAccepts first chain) `seq`
     chainedDominionAccepts first chain (normalizeAtlasElement valueAtlas occurrence) datum `seq`
     chainedDominionAccepts first chain occurrence datum `seq` ()

-- | Observe the checked cell action through the allocated Atlas, retaining
-- both endpoints even when their raw occurrences lie in the padded tail.
-- ALIGN: CHAINED-OWNER-TRANSPORT.
{-@ chainedDominionTransport :: owner:ChainedDominionAtlas ownerScope scope value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid (atlasPageElements (chainedDominionAtlas owner)) (arrowSource arrow)
           && pageElementTraceValid (atlasPageElements (chainedDominionAtlas owner)) (arrowTarget arrow)}
      -> datum:{ChainedDominionCellData value source |
           atlasAcceptsDatum (chainedDominionAtlas owner) (arrowSource arrow) datum}
      -> {applyInsertion (mapAtlasData (chainedDominionAtlas owner) arrow) datum
           == cellMap (chainedDominionChain owner)
                (chainedDominionCell (chainedDominionFirst owner) (chainedDominionChain owner) (arrowSource arrow))
                (chainedDominionCell (chainedDominionFirst owner) (chainedDominionChain owner) (arrowTarget arrow)) datum} @-}
chainedDominionTransport :: ChainedDominionAtlas ownerScope scope value
  -> PageElementArrow scope source target -> ChainedDominionCellData value source -> ()
chainedDominionTransport owner arrow datum =
  let valueAtlas = chainedDominionAtlas owner
      first = chainedDominionFirst owner
      chain = chainedDominionChain owner
      category = atlasPageElements valueAtlas
  in atlasFolio valueAtlas `seq`
     chainedDominionMembership owner (arrowSource arrow) datum `seq`
     atlasArrowNormalizationAgrees valueAtlas arrow `seq`
     normalizeAtlasArrowTraceValid valueAtlas arrow `seq`
     ownedCellNormalization category first chain (arrowSource arrow) `seq`
     ownedCellNormalization category first chain (arrowTarget arrow) `seq`
     chainedDominionDataMap category first chain (normalizeAtlasArrow valueAtlas arrow) `seq`
     mapAtlasData valueAtlas arrow `seq` ()

-- ALIGN: CHAINED-OWNER-RETAIN.
{-@ retainChainedDominionAtlas :: first:value -> chain:Chain value -> dominion:Dominion value
      -> valueAtlas:{Atlas owner scope (ChainedDominionCellData value) () value |
           folioLength (atlasFolio valueAtlas) == 2 && lastChain (atlasFolio valueAtlas) == chain
           && atlasPresentationAction (atlasDescription valueAtlas)
                == chainedDominionAction (atlasPageElements valueAtlas) first chain dominion
           && atlasActionMembership (atlasPresentationAction (atlasDescription valueAtlas))
                == atlasMembership (chainedDominionAccepts first chain)
           && atlasActionDataAt (atlasPresentationAction (atlasDescription valueAtlas))
                == chainedDominionAt first chain dominion
           && atlasActionMap (atlasPresentationAction (atlasDescription valueAtlas))
                == chainedDominionDataMap (atlasPageElements valueAtlas) first chain}
      -> {result:ChainedDominionAtlas owner scope value |
           chainedDominionFirst result == first && chainedDominionChain result == chain
           && chainedDominionValueDominion result == dominion && chainedDominionAtlas result == valueAtlas} @-}
retainChainedDominionAtlas :: value -> Chain value -> Dominion value
  -> Atlas owner scope (ChainedDominionCellData value) () value -> ChainedDominionAtlas owner scope value
retainChainedDominionAtlas = ChainedDominionAtlas

-- ALIGN: CHAINED-OWNER-ALLOCATION.
{-@ withChainedDominionAtlas :: first:value -> chain:Chain value -> dominion:Dominion value
      -> (forall owner scope. result:{ChainedDominionAtlas owner scope value |
           chainedDominionFirst result == first && chainedDominionChain result == chain
           && chainedDominionValueDominion result == dominion} -> resultValue) -> resultValue @-}
withChainedDominionAtlas :: value -> Chain value -> Dominion value
  -> (forall owner scope. ChainedDominionAtlas owner scope value -> result) -> result
withChainedDominionAtlas first chain dominion useOwner =
  pagination (chainedDominionFolio first chain) $ \pages ->
    withChainedPagination first chain dominion pages useOwner

-- ALIGN: CHAINED-OWNER-PAGINATION-ALLOCATION.
{-@ withChainedPagination :: first:value -> chain:Chain value -> dominion:Dominion value
      -> pages:{Pagination scope () value |
           folioLength (pageElementsFolio (paginationPageElements pages)) == 2
           && lastChain (pageElementsFolio (paginationPageElements pages)) == chain}
      -> (forall owner. result:{ChainedDominionAtlas owner scope value |
           chainedDominionFirst result == first && chainedDominionChain result == chain
           && chainedDominionValueDominion result == dominion} -> resultValue) -> resultValue @-}
withChainedPagination :: value -> Chain value -> Dominion value -> Pagination scope () value
  -> (forall owner. ChainedDominionAtlas owner scope value -> result) -> result
withChainedPagination first chain dominion pages useOwner =
  let presentation = chainedDominionPresentation pages first chain dominion
  in withAtlasPresentation presentation (\valueAtlas ->
       useOwner (retainChainedPresentation first chain dominion presentation valueAtlas))

-- ALIGN: CHAINED-OWNER-RETAIN-PRESENTATION.
{-@ retainChainedPresentation :: first:value -> chain:Chain value -> dominion:Dominion value
      -> presentation:{AtlasPresentation scope (ChainedDominionCellData value) () value |
           folioLength (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == 2
           && lastChain (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == chain
           && atlasPresentationAction presentation
                == chainedDominionAction (paginationPageElements (atlasPresentationPagination presentation)) first chain dominion
           && atlasActionMembership (atlasPresentationAction presentation) == atlasMembership (chainedDominionAccepts first chain)
           && atlasActionDataAt (atlasPresentationAction presentation) == chainedDominionAt first chain dominion
           && atlasActionMap (atlasPresentationAction presentation)
                == chainedDominionDataMap (paginationPageElements (atlasPresentationPagination presentation)) first chain}
      -> valueAtlas:{Atlas owner scope (ChainedDominionCellData value) () value |
           atlasDescription valueAtlas == presentation && atlasPagination valueAtlas == atlasPresentationPagination presentation}
      -> {result:ChainedDominionAtlas owner scope value |
           chainedDominionFirst result == first && chainedDominionChain result == chain
           && chainedDominionValueDominion result == dominion && chainedDominionAtlas result == valueAtlas} @-}
retainChainedPresentation :: value -> Chain value -> Dominion value
  -> AtlasPresentation scope (ChainedDominionCellData value) () value
  -> Atlas owner scope (ChainedDominionCellData value) () value -> ChainedDominionAtlas owner scope value
retainChainedPresentation first chain dominion _ valueAtlas =
  atlasFolio valueAtlas `seq` retainChainedDominionAtlas first chain dominion valueAtlas
