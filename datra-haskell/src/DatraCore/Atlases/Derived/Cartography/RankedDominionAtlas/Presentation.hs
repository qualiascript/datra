{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--etabeta" @-}

-- | Ranked cell actions assembled over their owning two-page folio.
module RankedDominionAtlas.Presentation
  ( rankedArrowCompatible, rankedRegionPosition, ownedCellNormalization
  , rankedDominionAt, rankedDominionAccepts, rankedDominionDataMap
  , rankedDominionAction, rankedDominionPresentation, rankedDominionFolio
  ) where

import Atlas
  ( AtlasPresentation, AtlasDataAction, atlasPresentationForPredicate, atlasPredicateDataAction
  , atlasActionDomain, atlasActionMembership, atlasActionDataAt, atlasActionMap, atlasMembership
  , atlasPresentationPagination, atlasPresentationAction )
import Chain (spine, spinePosition)
import ChainedDominionAtlas.Action (chainValueAt)
import ChainedDominionAtlas.Presentation (chainedRegionPosition, chainedDominionFolio)
import RankedDominionAtlas.Action
  ( ChainedDominionCell (..), cellAt, spineRank, cellRank, cellUnrank, cellDominion
  , cellAccepts, cellPrecedes, cellInsertion, cellMap, cellPreimage
  , cellIdentity, cellComposition, cellDisjoint )
import RankedDominionAtlas.Data (RankedDominionCellData)
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import DatraOrdinal.Laws (finiteOrdinalLookup)
import Dominion (Dominion, rank, unrank)
import DomanialInsertion.Core (DomanialInsertion (..))
import Folio (Folio, folioLength, lastChain)
import PageElements
  ( PageElements, pageElementsFolio, normalizePageElement, normalizePageElementArrow
  , pageElementTraceValid, pageElementSamePagePosition, pageElementDomain )
import PageElements.Structure
  ( PageElement, PageElementArrow (..), pageElementPage, pageElementPosition
  , identityPageElementArrow, composePageElementArrows )
import Pagination (Pagination, paginationPageElements)
import Numeric.Natural (Natural)
import TwoPagePresentation (twoPageRegionPosition, twoPageArrowPosition, normalizedArrow)

{-@ opaque-reflect spine @-}

{-@ rankedDominionFolio :: {pages:Folio () Natural |
      folioLength pages == 2 && lastChain pages == spine} @-}
-- ALIGN: RANKED-TWO-PAGE-FOLIO.
rankedDominionFolio :: Folio () Natural
rankedDominionFolio = chainedDominionFolio 0 spine

{-@ rankedArrowCompatible :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> {cellPrecedes (cellAt (arrowSource arrow)) (cellAt (arrowTarget arrow))} @-}
-- ALIGN: RANKED-ARROW-COMPATIBLE.
rankedArrowCompatible :: PageElements scope origin final -> PageElementArrow scope source target -> ()
rankedArrowCompatible category arrow@(PageElementArrow _ _)
  | pageElementPage (arrowSource arrow) == 0 =
      if pageElementPage (arrowTarget arrow) == 0 then () else ()
  | pageElementPage (arrowTarget arrow) == 0 = ()
  | otherwise = twoPageArrowPosition category arrow

{-@ rankedRegionPosition :: category:{PageElements scope origin Natural |
           folioLength (pageElementsFolio category) == 2 && lastChain (pageElementsFolio category) == spine}
      -> occurrence:{PageElement scope object | pageElementTraceValid category occurrence
           && pageElementPage occurrence > 0}
      -> {finiteOrdinal (spineRank (pageElementPosition occurrence)) == pageElementPosition occurrence} @-}
-- ALIGN: RANKED-REGION-POSITION.
rankedRegionPosition :: PageElements scope origin Natural -> PageElement scope object -> ()
rankedRegionPosition category occurrence =
  chainedRegionPosition category 0 spine occurrence `seq`
  spinePosition (chainValueAt 0 spine occurrence) `seq`
  finiteOrdinalLookup (chainValueAt 0 spine occurrence) `seq`
  case naturalAtOrdinal (pageElementPosition occurrence) of
    Nothing -> ()
    Just _ -> ()

{-@ ownedCellNormalization :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> occurrence:PageElement scope object
      -> {cellAt (normalizePageElement category occurrence) == cellAt occurrence} @-}
-- ALIGN: RANKED-OWNED-NORMALIZATION.
ownedCellNormalization :: PageElements scope origin final -> PageElement scope object -> ()
ownedCellNormalization category occurrence
  | pageElementPage occurrence == 0 = normalizePageElement category occurrence `seq` ()
  | otherwise = twoPageRegionPosition category occurrence

{-@ reflect rankedDominionAccepts @-}
-- ALIGN: RANKED-PRESENTATION-MEMBERSHIP.
rankedDominionAccepts :: Dominion value -> PageElement scope object -> RankedDominionCellData value object -> Bool
rankedDominionAccepts owner occurrence = cellAccepts owner (cellAt occurrence)

{-@ rankedDominionAt :: owner:Dominion value -> occurrence:PageElement scope object
      -> {result:Dominion ({datum:RankedDominionCellData value object | rankedDominionAccepts owner occurrence datum}) |
           rank result == cellRank owner (cellAt occurrence)
           && unrank result == cellUnrank owner (cellAt occurrence)} @-}
-- ALIGN: RANKED-PRESENTATION-DOMINION.
rankedDominionAt :: Dominion value -> PageElement scope object -> Dominion (RankedDominionCellData value object)
rankedDominionAt owner occurrence = cellDominion owner (cellAt occurrence)

{-@ rankedDominionDataMap :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> owner:Dominion value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> {result:DomanialInsertion
           ({datum:RankedDominionCellData value source | rankedDominionAccepts owner (arrowSource arrow) datum})
           ({datum:RankedDominionCellData value target | rankedDominionAccepts owner (arrowTarget arrow) datum}) |
           applyInsertion result == cellMap owner (cellAt (arrowSource arrow)) (cellAt (arrowTarget arrow))
           && preimage result == cellPreimage owner (cellAt (arrowSource arrow)) (cellAt (arrowTarget arrow))} @-}
-- ALIGN: RANKED-PRESENTATION-INSERTION.
-- ALIGN: RANKED-PRESENTATION-FORWARD.
-- ALIGN: RANKED-PRESENTATION-INVERSE.
rankedDominionDataMap :: PageElements scope origin final -> Dominion value
  -> PageElementArrow scope source target
  -> DomanialInsertion (RankedDominionCellData value source) (RankedDominionCellData value target)
rankedDominionDataMap category owner arrow =
  rankedArrowCompatible category arrow `seq` cellInsertion owner (cellAt (arrowSource arrow)) (cellAt (arrowTarget arrow))

{-@ opaque-reflect rankedDominionAt @-}
{-@ opaque-reflect rankedDominionDataMap @-}
{-@ opaque-reflect atlasActionDataAt @-}
{-@ opaque-reflect rankedDominionAction @-}
{-@ rankedDominionAction :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> owner:Dominion value
      -> {action:AtlasDataAction scope (RankedDominionCellData value) |
           atlasActionDomain action == pageElementDomain category
           && atlasActionMembership action == atlasMembership (rankedDominionAccepts owner)
           && atlasActionDataAt action == rankedDominionAt owner
           && atlasActionMap action == rankedDominionDataMap category owner} @-}
-- ALIGN: RANKED-PRESENTATION-ACTION.
rankedDominionAction :: PageElements scope origin final -> Dominion value
  -> AtlasDataAction scope (RankedDominionCellData value)
rankedDominionAction category owner =
  atlasPredicateDataAction category (rankedDominionAccepts owner)
    (rankedDominionAt owner) (rankedDominionDataMap category owner)

{-@ opaque-reflect atlasPresentationAction @-}
{-@ rankedDominionPresentation :: pages:{Pagination scope origin Natural |
           folioLength (pageElementsFolio (paginationPageElements pages)) == 2
           && lastChain (pageElementsFolio (paginationPageElements pages)) == spine}
      -> owner:Dominion value
      -> {presentation:AtlasPresentation scope (RankedDominionCellData value) origin Natural |
           atlasPresentationPagination presentation == pages
           && atlasPresentationAction presentation == rankedDominionAction (paginationPageElements pages) owner
           && atlasActionMembership (atlasPresentationAction presentation) == atlasMembership (rankedDominionAccepts owner)
           && atlasActionDataAt (atlasPresentationAction presentation) == rankedDominionAt owner
           && atlasActionMap (atlasPresentationAction presentation) == rankedDominionDataMap (paginationPageElements pages) owner} @-}
-- ALIGN: RANKED-OWNED-PRESENTATION.
rankedDominionPresentation :: Pagination scope origin Natural -> Dominion value
  -> AtlasPresentation scope (RankedDominionCellData value) origin Natural
rankedDominionPresentation pages owner =
  let category = paginationPageElements pages
      action = rankedDominionAction category owner
  in atlasPresentationForPredicate pages (rankedDominionAccepts owner) action
       (rankedIdentity category owner)
       (rankedComposition category owner)
       (rankedCoherence category owner)
       (rankedDisjoint category owner)

{-@ rankedIdentity :: category:{PageElements scope origin Natural | folioLength (pageElementsFolio category) == 2}
      -> owner:Dominion value
      -> occurrence:{PageElement scope object | pageElementTraceValid category occurrence}
       -> datum:{RankedDominionCellData value object | rankedDominionAccepts owner
            (normalizePageElement category occurrence) datum}
       -> { proof:() |
            applyInsertion
              (rankedDominionDataMap category owner
                (normalizePageElementArrow category
                  (identityPageElementArrow occurrence)))
              datum
            == datum } @-}
-- ALIGN: RANKED-PRESENTATION-IDENTITY.
rankedIdentity :: PageElements scope origin Natural -> Dominion value
  -> PageElement scope object -> RankedDominionCellData value object -> ()
rankedIdentity category owner occurrence datum =
  let arrow = normalizedArrow category (identityPageElementArrow occurrence)
  in rankedDominionDataMap category owner arrow `seq`
     cellIdentity owner (cellAt (arrowSource arrow)) datum

{-@ rankedComposition :: category:{PageElements scope origin Natural | folioLength (pageElementsFolio category) == 2}
      -> owner:Dominion value
      -> second:{PageElementArrow scope middle target | pageElementTraceValid category (arrowSource second) && pageElementTraceValid category (arrowTarget second)}
       -> first:{PageElementArrow scope source middle | pageElementTraceValid category (arrowSource first) && pageElementTraceValid category (arrowTarget first)}
       -> alignment:{() | arrowTarget first == arrowSource second}
       -> datum:{RankedDominionCellData value source | rankedDominionAccepts owner
            (normalizePageElement category (arrowSource first)) datum}
       -> { proof:() |
            applyInsertion
              (rankedDominionDataMap category owner
                (normalizePageElementArrow category
                  (composePageElementArrows second first)))
              datum
            == applyInsertion
                 (rankedDominionDataMap category owner
                   (normalizePageElementArrow category second))
                 (applyInsertion
                   (rankedDominionDataMap category owner
                     (normalizePageElementArrow category first))
                   datum) } @-}
-- ALIGN: RANKED-PRESENTATION-COMPOSITION.
rankedComposition :: PageElements scope origin Natural -> Dominion value
  -> PageElementArrow scope middle target -> PageElementArrow scope source middle
  -> () -> RankedDominionCellData value source -> ()
rankedComposition category owner second before alignment datum =
  alignment `seq`
  let a = normalizedArrow category before
      b = normalizedArrow category second
      c = normalizedArrow category (composePageElementArrows second before)
  in rankedDominionDataMap category owner a `seq`
     rankedDominionDataMap category owner b `seq`
     rankedDominionDataMap category owner c `seq`
     rankedArrowCompatible category a `seq`
     rankedArrowCompatible category b `seq`
     cellComposition owner (cellAt (arrowSource a))
       (cellAt (arrowTarget a))
       (cellAt (arrowTarget b)) datum

{-@ rankedCoherence :: category:{PageElements scope origin Natural | folioLength (pageElementsFolio category) == 2}
      -> owner:Dominion value
      -> occurrence:{PageElement scope object | pageElementTraceValid category occurrence}
       -> coherenceArrow:{PageElementArrow scope object object | pageElementTraceValid category (arrowSource coherenceArrow) && pageElementTraceValid category (arrowTarget coherenceArrow)}
       -> conditions:{() |
            arrowSource coherenceArrow == occurrence
            && arrowTarget coherenceArrow == normalizePageElement category occurrence}
       -> datum:{RankedDominionCellData value object | rankedDominionAccepts owner
            (normalizePageElement category occurrence) datum}
       -> { proof:() |
            applyInsertion
              (rankedDominionDataMap category owner
                (normalizePageElementArrow category coherenceArrow))
              datum
            == datum } @-}
-- ALIGN: RANKED-PRESENTATION-COHERENCE.
rankedCoherence :: PageElements scope origin Natural -> Dominion value
  -> PageElement scope object -> PageElementArrow scope object object
  -> () -> RankedDominionCellData value object -> ()
rankedCoherence category owner occurrence coherence conditions datum =
  conditions `seq`
  ownedCellNormalization category (normalizePageElement category occurrence) `seq`
  let arrow = normalizedArrow category coherence
  in rankedDominionDataMap category owner arrow `seq`
     cellIdentity owner (cellAt (arrowSource arrow)) datum

{-@ rankedDisjoint :: category:{PageElements scope origin Natural | folioLength (pageElementsFolio category) == 2 && lastChain (pageElementsFolio category) == spine}
      -> owner:Dominion value
      -> left:{PageElement scope leftObject | pageElementTraceValid category left}
       -> right:{PageElement scope rightObject | pageElementTraceValid category right}
       -> leftToOrigin:{PageElementArrow scope leftObject originObject | pageElementTraceValid category (arrowSource leftToOrigin) && pageElementTraceValid category (arrowTarget leftToOrigin)}
       -> rightToOrigin:{PageElementArrow scope rightObject originObject | pageElementTraceValid category (arrowSource rightToOrigin) && pageElementTraceValid category (arrowTarget rightToOrigin)}
       -> conditions:{() |
            pageElementPage right == pageElementPage left
            && pageElementPosition right /= pageElementPosition left
            && pageElementPage left <= folioLength (pageElementsFolio category) - 1
            && arrowSource leftToOrigin == left
            && pageElementPage (arrowTarget leftToOrigin) == 0
            && arrowSource rightToOrigin == right
            && arrowTarget rightToOrigin == arrowTarget leftToOrigin}
       -> leftDatum:{RankedDominionCellData value leftObject | rankedDominionAccepts owner
            (normalizePageElement category left) leftDatum}
       -> rightDatum:{RankedDominionCellData value rightObject | rankedDominionAccepts owner
            (normalizePageElement category right) rightDatum}
       -> { proof:() |
            applyInsertion
              (rankedDominionDataMap category owner
                (normalizePageElementArrow category leftToOrigin))
              leftDatum
            /= applyInsertion
                 (rankedDominionDataMap category owner
                   (normalizePageElementArrow category rightToOrigin))
                 rightDatum } @-}
-- ALIGN: RANKED-PRESENTATION-DISJOINT.
rankedDisjoint :: PageElements scope origin Natural -> Dominion value
  -> PageElement scope leftObject -> PageElement scope rightObject
  -> PageElementArrow scope leftObject originObject -> PageElementArrow scope rightObject originObject
  -> () -> RankedDominionCellData value leftObject -> RankedDominionCellData value rightObject -> ()
rankedDisjoint category owner left right leftArrow rightArrow conditions leftDatum rightDatum =
  conditions `seq`
  if pageElementPage left == 0
  then pageElementSamePagePosition category leftArrow `seq`
       pageElementSamePagePosition category rightArrow
  else
    let a = normalizedArrow category leftArrow
        b = normalizedArrow category rightArrow
    in ownedCellNormalization category left `seq`
       ownedCellNormalization category right `seq`
       ownedCellNormalization category (arrowTarget leftArrow) `seq`
       rankedRegionPosition category left `seq`
       rankedRegionPosition category right `seq`
       rankedDominionDataMap category owner a `seq`
       rankedDominionDataMap category owner b `seq`
       cellDisjoint owner (spineRank (pageElementPosition left)) (spineRank (pageElementPosition right))
         leftDatum rightDatum
