{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
-- Unfold the partially applied carrier predicate passed to shared folio assembly.
{-@ LIQUID "--etabeta" @-}

-- | Connect the checked cell action to arrows in its owning two-page folio.
module ChainedDominionAtlas.Presentation
  ( twoPageRegionPosition, chainedArrowCompatible, chainedRegionPosition, ownedCellNormalization
  , chainedDominionAt, chainedDominionAccepts, chainedDominionDataMap
  , chainedDominionAction, chainedDominionPresentation, chainedDominionFolio
  ) where

import Atlas
  ( AtlasPresentation, AtlasDataAction, atlasPresentationForPredicate, atlasPredicateDataAction
  , atlasActionDomain, atlasActionMembership, atlasActionDataAt, atlasActionMap, atlasMembership
  , atlasPresentationPagination, atlasPresentationAction )
import Chain (Chain, chainPosition, chainObjectAt, chainIndex)
import ChainedDominionAtlas.Action
  ( ChainedDominionCell (..), chainedDominionCell, chainValueAt
  , cellAccepts, cellPrecedes, cellInsertion, cellMap, cellPreimage
  , cellIdentity, cellComposition, cellDisjoint )
import ChainedDominionAtlas.Data
  ( ChainedDominionCellData, extentDominion, regionDominion )
import Dominion (Dominion)
import DomanialInsertion.Core (DomanialInsertion (..))
import Folio (Folio, folioLength, lastChain)
import Folio.Assembly (extendOrigin, originExtensionPages)
import Folio.Presentation (folioLengthData, lastPageData)
import PageElements
  ( PageElements, pageElementsFolio, normalizePageElement, normalizePageElementArrow
  , pageElementTraceValid, pageElementTraceValidNormalize, pageElementSamePagePosition
  , finalPageElementIndex, traceLookupPresent, pageElementDomain )
import PageElements.Structure
  ( PageElement, PageElementArrow (..), pageElementPage, pageElementPosition, clampPage
  , pageElementPrecedes, identityPageElementArrow, composePageElementArrows )
import Pagination (Pagination, paginationPageElements)
import Numeric.Natural (Natural)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- ALIGN: CHAINED-TWO-PAGE-FOLIO.
{-@ chainedDominionFolio :: first:value -> owner:Chain value
      -> {pages:Folio () value | folioLength pages == 2 && lastChain pages == owner} @-}
chainedDominionFolio :: value -> Chain value -> Folio () value
chainedDominionFolio first owner = originExtensionPages (extendOrigin (acceptsValue owner) owner first)

{-@ reflect acceptsValue @-}
-- ALIGN: CHAINED-FOLIO-MEMBERSHIP.
{-@ acceptsValue :: Chain value -> value -> {accepted:Bool | accepted} @-}
acceptsValue :: Chain value -> value -> Bool
acceptsValue _ _ = True

-- ALIGN: CHAINED-TWO-PAGE-REGION.
{-@ twoPageRegionPosition :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> occurrence:{PageElement scope object | pageElementPage occurrence > 0}
      -> {pageElementPage (normalizePageElement category occurrence) == 1} @-}
twoPageRegionPosition :: PageElements scope origin final -> PageElement scope object -> ()
twoPageRegionPosition category occurrence =
  normalizePageElement category occurrence `seq`
    if pageElementPage occurrence <= 1 then () else ()

-- ALIGN: CHAINED-ARROW-COMPATIBLE.
{-@ chainedArrowCompatible :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> first:value -> owner:Chain value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> {cellPrecedes owner
           (chainedDominionCell first owner (arrowSource arrow))
           (chainedDominionCell first owner (arrowTarget arrow))} @-}
chainedArrowCompatible :: PageElements scope origin final -> value -> Chain value
  -> PageElementArrow scope source target -> ()
chainedArrowCompatible category _ _ arrow@(PageElementArrow _ _)
  | pageElementPage (arrowSource arrow) == 0 =
      if pageElementPage (arrowTarget arrow) == 0 then () else ()
  | pageElementPage (arrowTarget arrow) == 0 = ()
  | otherwise =
      twoPageRegionPosition category (arrowSource arrow) `seq`
      twoPageRegionPosition category (arrowTarget arrow) `seq`
      pageElementTraceValidNormalize category (arrowSource arrow) `seq`
      pageElementTraceValidNormalize category (arrowTarget arrow) `seq`
      pageElementSamePagePosition category (normalizePageElementArrow category arrow)

-- | A valid region selects the value at its own position in the actual final
-- chain. The fallback used by the raw classifier cannot occur on this domain.
-- ALIGN: CHAINED-REGION-POSITION.
{-@ chainedRegionPosition :: category:{PageElements scope origin value |
           folioLength (pageElementsFolio category) == 2}
      -> first:value -> owner:{Chain value | owner == lastChain (pageElementsFolio category)}
      -> occurrence:{PageElement scope object | pageElementTraceValid category occurrence
           && pageElementPage occurrence > 0}
      -> {chainPosition owner (chainValueAt first owner occurrence) == pageElementPosition occurrence} @-}
chainedRegionPosition :: PageElements scope origin value -> value -> Chain value
  -> PageElement scope object -> ()
chainedRegionPosition category _ _ occurrence =
  twoPageRegionPosition category occurrence `seq`
  pageElementTraceValidNormalize category occurrence `seq`
  case finalPageElementIndex category (normalizePageElement category occurrence) of
    Nothing -> ()
    Just _ -> ()

-- ALIGN: CHAINED-PRESENTATION-MEMBERSHIP.
{-@ reflect chainedDominionAccepts @-}
chainedDominionAccepts :: value -> Chain value -> PageElement scope object
  -> ChainedDominionCellData value object -> Bool
chainedDominionAccepts first owner occurrence =
  cellAccepts owner (chainedDominionCell first owner occurrence)

-- ALIGN: CHAINED-PRESENTATION-DOMINION.
{-@ chainedDominionAt :: first:value -> owner:Chain value -> Dominion value
      -> occurrence:PageElement scope object
      -> Dominion ({datum:ChainedDominionCellData value object |
           chainedDominionAccepts first owner occurrence datum}) @-}
chainedDominionAt :: value -> Chain value -> Dominion value -> PageElement scope object
  -> Dominion (ChainedDominionCellData value object)
chainedDominionAt first owner valueDominion occurrence =
  case chainedDominionCell first owner occurrence of
    ExtentCell -> extentDominion valueDominion
    RegionCell selected -> regionDominion owner selected

-- ALIGN: CHAINED-PRESENTATION-INSERTION.
-- ALIGN: CHAINED-PRESENTATION-FORWARD.
-- ALIGN: CHAINED-PRESENTATION-INVERSE.
{-@ chainedDominionDataMap :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> first:value -> owner:Chain value
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> {result:DomanialInsertion
           ({datum:ChainedDominionCellData value source |
                chainedDominionAccepts first owner (arrowSource arrow) datum})
           ({datum:ChainedDominionCellData value target |
                chainedDominionAccepts first owner (arrowTarget arrow) datum}) |
           applyInsertion result == cellMap owner
             (chainedDominionCell first owner (arrowSource arrow))
             (chainedDominionCell first owner (arrowTarget arrow))
           && preimage result == cellPreimage owner
             (chainedDominionCell first owner (arrowSource arrow))
             (chainedDominionCell first owner (arrowTarget arrow))} @-}
chainedDominionDataMap :: PageElements scope origin final -> value -> Chain value
  -> PageElementArrow scope source target
  -> DomanialInsertion (ChainedDominionCellData value source) (ChainedDominionCellData value target)
chainedDominionDataMap category first owner arrow =
  chainedArrowCompatible category first owner arrow `seq`
    cellInsertion owner
      (chainedDominionCell first owner (arrowSource arrow))
      (chainedDominionCell first owner (arrowTarget arrow))

-- ALIGN: CHAINED-ARROW-NORMALIZATION.
{-@ normalizedArrow :: category:PageElements scope origin final
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)}
      -> {result:PageElementArrow scope source target |
           result == normalizePageElementArrow category arrow
           && pageElementTraceValid category (arrowSource result)
           && pageElementTraceValid category (arrowTarget result)
           && arrowSource result == normalizePageElement category (arrowSource arrow)
           && arrowTarget result == normalizePageElement category (arrowTarget arrow)} @-}
normalizedArrow :: PageElements scope origin final -> PageElementArrow scope source target
  -> PageElementArrow scope source target
normalizedArrow category arrow =
  pageElementTraceValidNormalize category (arrowSource arrow) `seq`
  pageElementTraceValidNormalize category (arrowTarget arrow) `seq`
  normalizePageElementArrow category arrow

-- ALIGN: CHAINED-OWNED-NORMALIZATION.
{-@ ownedCellNormalization :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> first:value -> owner:Chain value -> occurrence:PageElement scope object
      -> {chainedDominionCell first owner (normalizePageElement category occurrence)
           == chainedDominionCell first owner occurrence} @-}
ownedCellNormalization :: PageElements scope origin final -> value -> Chain value
  -> PageElement scope object -> ()
ownedCellNormalization category _ _ occurrence
  | pageElementPage occurrence == 0 = normalizePageElement category occurrence `seq` ()
  | otherwise = twoPageRegionPosition category occurrence

{-@ opaque-reflect chainedDominionAt @-}
{-@ opaque-reflect chainedDominionDataMap @-}
{-@ opaque-reflect atlasActionDataAt @-}
{-@ opaque-reflect chainedDominionAction @-}
-- ALIGN: CHAINED-PRESENTATION-ACTION.
{-@ chainedDominionAction :: category:{PageElements scope origin final |
           folioLength (pageElementsFolio category) == 2}
      -> first:value -> owner:Chain value -> valueDominion:Dominion value
      -> {action:AtlasDataAction scope (ChainedDominionCellData value) |
           atlasActionDomain action == pageElementDomain category
           && atlasActionMembership action == atlasMembership (chainedDominionAccepts first owner)
           && atlasActionDataAt action == chainedDominionAt first owner valueDominion
           && atlasActionMap action == chainedDominionDataMap category first owner} @-}
chainedDominionAction :: PageElements scope origin final -> value -> Chain value -> Dominion value
  -> AtlasDataAction scope (ChainedDominionCellData value)
chainedDominionAction category first owner valueDominion =
  atlasPredicateDataAction category (chainedDominionAccepts first owner)
    (chainedDominionAt first owner valueDominion) (chainedDominionDataMap category first owner)

{-@ opaque-reflect atlasPresentationAction @-}
-- ALIGN: CHAINED-OWNED-PRESENTATION.
{-@ chainedDominionPresentation :: pages:{Pagination scope origin value |
           folioLength (pageElementsFolio (paginationPageElements pages)) == 2}
      -> first:value -> owner:{Chain value | owner == lastChain (pageElementsFolio (paginationPageElements pages))}
      -> valueDominion:Dominion value
      -> {presentation:AtlasPresentation scope (ChainedDominionCellData value) origin value |
           atlasPresentationPagination presentation == pages
           && atlasPresentationAction presentation == chainedDominionAction (paginationPageElements pages) first owner valueDominion
           && atlasActionMembership (atlasPresentationAction presentation) == atlasMembership (chainedDominionAccepts first owner)
           && atlasActionDataAt (atlasPresentationAction presentation) == chainedDominionAt first owner valueDominion
           && atlasActionMap (atlasPresentationAction presentation) == chainedDominionDataMap (paginationPageElements pages) first owner} @-}
chainedDominionPresentation :: Pagination scope origin value -> value -> Chain value -> Dominion value
  -> AtlasPresentation scope (ChainedDominionCellData value) origin value
chainedDominionPresentation pages first owner valueDominion =
  let category = paginationPageElements pages
      action = chainedDominionAction category first owner valueDominion
  in atlasPresentationForPredicate pages (chainedDominionAccepts first owner) action
       (chainedIdentity category first owner)
       (chainedComposition category first owner)
       (chainedCoherence category first owner)
       (chainedDisjoint category first owner)

-- ALIGN: CHAINED-PRESENTATION-IDENTITY.
{-@ chainedIdentity :: category:{PageElements scope origin value | folioLength (pageElementsFolio category) == 2}
      -> firstValue:value -> owner:Chain value
      -> occurrence:{PageElement scope object | pageElementTraceValid category occurrence}
       -> datum:{ChainedDominionCellData value object | chainedDominionAccepts firstValue owner
            (normalizePageElement category occurrence) datum}
       -> { proof:() |
            applyInsertion
              (chainedDominionDataMap category firstValue owner
                (normalizePageElementArrow category
                  (identityPageElementArrow occurrence)))
              datum
            == datum } @-}
chainedIdentity :: PageElements scope origin value -> value -> Chain value
  -> PageElement scope object -> ChainedDominionCellData value object -> ()
chainedIdentity category first owner occurrence datum =
  let arrow = normalizedArrow category (identityPageElementArrow occurrence)
  in chainedDominionDataMap category first owner arrow `seq`
     cellIdentity owner (chainedDominionCell first owner (arrowSource arrow)) datum

-- ALIGN: CHAINED-PRESENTATION-COMPOSITION.
{-@ chainedComposition :: category:{PageElements scope origin value | folioLength (pageElementsFolio category) == 2}
      -> firstValue:value -> owner:Chain value
      -> second:{PageElementArrow scope middle target | pageElementTraceValid category (arrowSource second) && pageElementTraceValid category (arrowTarget second)}
       -> first:{PageElementArrow scope source middle | pageElementTraceValid category (arrowSource first) && pageElementTraceValid category (arrowTarget first)}
       -> alignment:{() | arrowTarget first == arrowSource second}
       -> datum:{ChainedDominionCellData value source | chainedDominionAccepts firstValue owner
            (normalizePageElement category (arrowSource first)) datum}
       -> { proof:() |
            applyInsertion
              (chainedDominionDataMap category firstValue owner
                (normalizePageElementArrow category
                  (composePageElementArrows second first)))
              datum
            == applyInsertion
                 (chainedDominionDataMap category firstValue owner
                   (normalizePageElementArrow category second))
                 (applyInsertion
                   (chainedDominionDataMap category firstValue owner
                     (normalizePageElementArrow category first))
                   datum) } @-}
chainedComposition :: PageElements scope origin value -> value -> Chain value
  -> PageElementArrow scope middle target -> PageElementArrow scope source middle
  -> () -> ChainedDominionCellData value source -> ()
chainedComposition category firstValue owner second before alignment datum =
  alignment `seq`
  let a = normalizedArrow category before
      b = normalizedArrow category second
      c = normalizedArrow category (composePageElementArrows second before)
  in chainedDominionDataMap category firstValue owner a `seq`
     chainedDominionDataMap category firstValue owner b `seq`
     chainedDominionDataMap category firstValue owner c `seq`
     chainedArrowCompatible category firstValue owner a `seq`
     chainedArrowCompatible category firstValue owner b `seq`
     cellComposition owner (chainedDominionCell firstValue owner (arrowSource a))
       (chainedDominionCell firstValue owner (arrowTarget a))
       (chainedDominionCell firstValue owner (arrowTarget b)) datum

-- ALIGN: CHAINED-PRESENTATION-COHERENCE.
{-@ chainedCoherence :: category:{PageElements scope origin value | folioLength (pageElementsFolio category) == 2}
      -> firstValue:value -> owner:Chain value
      -> occurrence:{PageElement scope object | pageElementTraceValid category occurrence}
       -> coherenceArrow:{PageElementArrow scope object object | pageElementTraceValid category (arrowSource coherenceArrow) && pageElementTraceValid category (arrowTarget coherenceArrow)}
       -> conditions:{() |
            arrowSource coherenceArrow == occurrence
            && arrowTarget coherenceArrow == normalizePageElement category occurrence}
       -> datum:{ChainedDominionCellData value object | chainedDominionAccepts firstValue owner
            (normalizePageElement category occurrence) datum}
       -> { proof:() |
            applyInsertion
              (chainedDominionDataMap category firstValue owner
                (normalizePageElementArrow category coherenceArrow))
              datum
            == datum } @-}
chainedCoherence :: PageElements scope origin value -> value -> Chain value
  -> PageElement scope object -> PageElementArrow scope object object
  -> () -> ChainedDominionCellData value object -> ()
chainedCoherence category first owner occurrence coherence conditions datum =
  conditions `seq`
  ownedCellNormalization category first owner (normalizePageElement category occurrence) `seq`
  let arrow = normalizedArrow category coherence
  in chainedDominionDataMap category first owner arrow `seq`
     cellIdentity owner (chainedDominionCell first owner (arrowSource arrow)) datum

-- ALIGN: CHAINED-PRESENTATION-DISJOINT.
{-@ chainedDisjoint :: category:{PageElements scope origin value | folioLength (pageElementsFolio category) == 2}
      -> firstValue:value -> owner:{Chain value | owner == lastChain (pageElementsFolio category)}
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
       -> leftDatum:{ChainedDominionCellData value leftObject | chainedDominionAccepts firstValue owner
            (normalizePageElement category left) leftDatum}
       -> rightDatum:{ChainedDominionCellData value rightObject | chainedDominionAccepts firstValue owner
            (normalizePageElement category right) rightDatum}
       -> { proof:() |
            applyInsertion
              (chainedDominionDataMap category firstValue owner
                (normalizePageElementArrow category leftToOrigin))
              leftDatum
            /= applyInsertion
                 (chainedDominionDataMap category firstValue owner
                   (normalizePageElementArrow category rightToOrigin))
                 rightDatum } @-}
chainedDisjoint :: PageElements scope origin value -> value -> Chain value
  -> PageElement scope leftObject -> PageElement scope rightObject
  -> PageElementArrow scope leftObject originObject -> PageElementArrow scope rightObject originObject
  -> () -> ChainedDominionCellData value leftObject -> ChainedDominionCellData value rightObject -> ()
chainedDisjoint category first owner left right leftArrow rightArrow conditions leftDatum rightDatum =
  conditions `seq`
  if pageElementPage left == 0
  then pageElementSamePagePosition category leftArrow `seq`
       pageElementSamePagePosition category rightArrow
  else
    let a = normalizedArrow category leftArrow
        b = normalizedArrow category rightArrow
    in ownedCellNormalization category first owner left `seq`
       ownedCellNormalization category first owner right `seq`
       ownedCellNormalization category first owner (arrowTarget leftArrow) `seq`
       chainedRegionPosition category first owner left `seq`
       chainedRegionPosition category first owner right `seq`
       chainedDominionDataMap category first owner a `seq`
       chainedDominionDataMap category first owner b `seq`
       cellDisjoint owner (chainValueAt first owner left) (chainValueAt first owner right)
         leftDatum rightDatum
