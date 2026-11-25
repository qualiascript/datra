{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
-- Keep the rank-polymorphic carrier family intact; all assembly contracts
-- below are explicit and checked.
{-@ LIQUID "--fast" @-}

-- | The constant data action and its normalized one-page Atlas laws.
module DomanialInclusion.Presentation
  ( constantPresentation, DominionPaginationScope
  , onePageFolio, onePagePagination, dominionPresentation
  , DominionAtlas, DominionAtlasObject, dominionAtlas, withDominionAtlas
  , dominionAcceptsDatum
  , CanonicalDominion (..), CanonicalDominionAtlasScope, canonicalDominionAtlas ) where

import Atlas
  ( Atlas, AtlasObject, atlasPagination, atlasFolio, atlasDescription, withAtlasPresentation, atlasAcceptsDatum
  , AtlasPresentation, atlasPresentationForPredicate, atlasPresentationPagination, atlasPresentationAction
  , AtlasDataAction, atlasActionDomain, atlasActionMembership, atlasActionDataAt
  , atlasDescriptionMembership, normalizeAtlasElement
  , atlasActionMap, atlasMembership, atlasPredicateDataAction )
import Atlas.Construction (AtlasConstruction (..), FixedAtlasScope, constructAtlas)
import DomanialInclusion.Data
  ( DominionCellData, constantDominion, identityDominionCellInsertion
  , identityCellMap, identityCellPreimage, identityCellMapIdentity, identityCellMapComposition )
import DomanialInsertion.Core (DomanialInsertion (..))
import Chain.Singleton (singletonChain)
import Data.Proxy (Proxy (..))
import Data.Kind (Type)
import Dominion (Dominion)
import Folio (Folio, folioLength)
import Folio.Presentation (folioData, folioLengthData)
import PageElements
  ( PageElements, pageElementsFolio, pageElementTraceValidShape
  , pageElementDomain, normalizePageElementArrow
  , pageElementTraceValid, pageElementValidArrowPosition )
import PageElements.Structure
  ( PageElement, PageElementArrow (..), pageElementPage, pageElementPosition
  , identityPageElementArrow, composePageElementArrows
  , pageElementTrace, positionAtPage, tracePosition, traceStartsWith )
import Pagination (Pagination, paginationPageElements)
import qualified Pagination
import PageElements.Construction
  ( PageElementsConstruction (..), ConstructedPageElementsScope, constructPageElements )
import Numeric.Natural (Natural)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- The recipe has no runtime configuration; the datum carrier only indexes
-- its nominal occurrence owner.
data DominionPaginationRecipe (a :: Type)
type DominionPaginationScope a = ConstructedPageElementsScope (DominionPaginationRecipe a) () ()

-- ALIGN: DOMINC-ONE-PAGE-FOLIO.
{-@ onePageFolio :: {pages:Folio () () | folioLength pages == 1} @-}
onePageFolio :: Folio () ()
onePageFolio = folioData singletonChain () (\() -> ())

-- The logical instance signature includes Proxy's implicit kind parameter.
{-@ instance PageElementsConstruction (DominionPaginationRecipe a) (()) (()) where
      pageElementsRecipe :: Proxy Type (DominionPaginationRecipe a)
        -> {pages:Folio () () | folioLength pages == 1}
  @-}
instance PageElementsConstruction (DominionPaginationRecipe a) () () where
  pageElementsRecipe _ = onePageFolio

-- ALIGN: DOMINC-ONE-PAGE-PAGINATION.
{-@ onePagePagination :: {pages:Pagination (DominionPaginationScope a) () () |
      folioLength (pageElementsFolio (paginationPageElements pages)) == 1} @-}
onePagePagination :: forall a. Pagination (DominionPaginationScope a) () ()
onePagePagination =
  let recipe = Proxy :: Proxy (DominionPaginationRecipe a)
  in (pageElementsRecipe recipe :: Folio () ()) `seq`
       Pagination.paginationFromPageElements (constructPageElements recipe)

-- ALIGN: DOMINC-OWNED-PRESENTATION.
-- ALIGN: DOMINC-PRESENTATION-INTERPRETATION.
{-@ dominionPresentation :: Dominion a
      -> {presentation:AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () () |
           folioLength (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == 1
           && atlasActionMembership (atlasPresentationAction presentation) == atlasMembership acceptsConstantDatum
           && atlasActionMap (atlasPresentationAction presentation) == constantDataMap} @-}
dominionPresentation :: forall a. Dominion a
  -> AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () ()
dominionPresentation owner = constantPresentation (onePagePagination @a) owner

type DominionAtlasObject owner a =
  AtlasObject owner (DominionPaginationScope a) (DominionCellData a)

-- | Retain the whole Atlas type and its checked construction predicate. Making
-- the payload a parameter keeps dependent families out of SMT datatype fields.
type role DominionAtlasData nominal
{-@ data variance DominionAtlasData invariant invariant @-}
{-@ data DominionAtlasData atlas <ownsAction :: atlas -> Bool> = DominionAtlas
      { storedDominionAtlas :: atlas<ownsAction> } @-}
data DominionAtlasData atlas = DominionAtlas
  { storedDominionAtlas :: atlas }

type DominionAtlas owner a =
  DominionAtlasData (Atlas owner (DominionPaginationScope a) (DominionCellData a) () ())

{-@ type DominionAtlas owner a = DominionAtlasData
      <{\value -> folioLength (atlasFolio value) == 1
        && atlasActionMembership (atlasPresentationAction (atlasDescription value)) == atlasMembership acceptsConstantDatum
        && atlasActionMap (atlasPresentationAction (atlasDescription value)) == constantDataMap}>
      (Atlas owner (DominionPaginationScope a) (DominionCellData a) () ()) @-}

{-@ retainDominionAtlas :: presentation:{AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () () |
           folioLength (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == 1
           && atlasActionMembership (atlasPresentationAction presentation) == atlasMembership acceptsConstantDatum
           && atlasActionMap (atlasPresentationAction presentation) == constantDataMap}
      -> value:{Atlas owner (DominionPaginationScope a) (DominionCellData a) () () |
           atlasDescription value == presentation && atlasPagination value == atlasPresentationPagination presentation}
      -> DominionAtlas owner a @-}
retainDominionAtlas :: AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () ()
  -> Atlas owner (DominionPaginationScope a) (DominionCellData a) () () -> DominionAtlas owner a
retainDominionAtlas _ value = atlasFolio value `seq` DominionAtlas value

-- ALIGN: DOMINC-OWNER-CARDINALITY.
{-@ reflect dominionAtlas @-}
{-@ dominionAtlas :: DominionAtlas owner a
      -> {value:Atlas owner (DominionPaginationScope a) (DominionCellData a) () () |
           folioLength (atlasFolio value) == 1
           && atlasActionMembership (atlasPresentationAction (atlasDescription value)) == atlasMembership acceptsConstantDatum
           && atlasActionMap (atlasPresentationAction (atlasDescription value)) == constantDataMap} @-}
dominionAtlas :: DominionAtlas owner a
  -> Atlas owner (DominionPaginationScope a) (DominionCellData a) () ()
dominionAtlas (DominionAtlas value) = value

-- | Every value of the retained constant carrier is accepted at every cell.
-- ALIGN: DOMINC-OWNER-MEMBERSHIP.
{-@ dominionAcceptsDatum :: owner:DominionAtlas ownerScope a
      -> occurrence:PageElement (DominionPaginationScope a) object
      -> datum:DominionCellData a object
      -> {atlasAcceptsDatum (dominionAtlas owner) occurrence datum} @-}
dominionAcceptsDatum :: DominionAtlas owner a
  -> PageElement (DominionPaginationScope a) object -> DominionCellData a object -> ()
dominionAcceptsDatum owner occurrence datum =
  let value = dominionAtlas owner
  in atlasDescriptionMembership value occurrence datum `seq`
     atlasMembership acceptsConstantDatum `seq`
     acceptsConstantDatum (normalizeAtlasElement value occurrence) datum `seq` ()

-- ALIGN: DOMINC-ATLAS-INTERPRETATION.
-- ALIGN: DOMINC-STABLE-ISOMORPHISM.
-- ALIGN: DOMINC-OWNER-ALLOCATION.
{-@ withDominionAtlas :: Dominion a
      -> (forall owner. DominionAtlas owner a -> result) -> result @-}
withDominionAtlas :: Dominion a -> (forall owner. DominionAtlas owner a -> result) -> result
withDominionAtlas owner useOwner =
  let presentation = dominionPresentation owner
  in withAtlasPresentation presentation (\value -> useOwner (retainDominionAtlas presentation value))

-- | A canonical Dominion is a fixed instance recipe, with no runtime input.
class CanonicalDominion a where
  canonicalDominion :: Proxy a -> Dominion a

data CanonicalDominionRecipe (a :: Type)
type CanonicalDominionAtlasScope a =
  FixedAtlasScope (CanonicalDominionRecipe a) (DominionPaginationScope a) (DominionCellData a) () ()

{-@ instance CanonicalDominion a => AtlasConstruction (CanonicalDominionRecipe a)
      (DominionPaginationScope a) (DominionCellData a) (()) (()) where
      atlasConstructionPresentation :: Proxy Type (CanonicalDominionRecipe a)
        -> {presentation:AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () () |
             folioLength (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == 1
             && atlasActionMembership (atlasPresentationAction presentation) == atlasMembership acceptsConstantDatum
             && atlasActionMap (atlasPresentationAction presentation) == constantDataMap}
  @-}
instance CanonicalDominion a => AtlasConstruction (CanonicalDominionRecipe a)
    (DominionPaginationScope a) (DominionCellData a) () () where
  atlasConstructionPresentation _ = dominionPresentation (canonicalDominion (Proxy :: Proxy a))

-- ALIGN: DOMINC-CANONICAL-ALLOCATION.
{-@ canonicalDominionAtlas :: CanonicalDominion a => DominionAtlas (CanonicalDominionAtlasScope a) a @-}
canonicalDominionAtlas :: forall a. CanonicalDominion a => DominionAtlas (CanonicalDominionAtlasScope a) a
canonicalDominionAtlas =
  let recipe = Proxy :: Proxy (CanonicalDominionRecipe a)
      presentation = atlasConstructionPresentation recipe
        :: AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () ()
      valueAtlas = constructAtlas recipe
  in retainDominionAtlas presentation valueAtlas

{-@ reflect acceptsConstantDatum @-}
{-@ acceptsConstantDatum :: PageElement scope object -> DominionCellData a object -> {value:Bool | value} @-}
acceptsConstantDatum :: forall a scope object. PageElement scope object -> DominionCellData a object -> Bool
acceptsConstantDatum _ _ = True

{-@ opaque-reflect constantDataAt @-}
{-@ opaque-reflect constantDominion @-}
-- ALIGN: DOMINC-CONSTANT-RANK.
-- ALIGN: DOMINC-CONSTANT-UNRANK.
{-@ constantDataAt :: owner:Dominion a -> occurrence:PageElement scope object
      -> {value:Dominion ({datum:DominionCellData a object | acceptsConstantDatum occurrence datum}) |
           value == constantDominion owner} @-}
constantDataAt :: Dominion a -> PageElement scope object -> Dominion (DominionCellData a object)
constantDataAt owner _ = constantDominion owner

{-@ opaque-reflect constantDataMap @-}
-- ALIGN: DOMINC-CONSTANT-MAP.
-- ALIGN: DOMINC-CONSTANT-PREIMAGE.
{-@ constantDataMap :: arrow:PageElementArrow scope source target
      -> {insertion:DomanialInsertion
           ({datum:DominionCellData a source | acceptsConstantDatum (arrowSource arrow) datum})
           ({datum:DominionCellData a target | acceptsConstantDatum (arrowTarget arrow) datum}) |
           applyInsertion insertion == identityCellMap && preimage insertion == identityCellPreimage} @-}
constantDataMap :: forall a scope source target. PageElementArrow scope source target
  -> DomanialInsertion (DominionCellData a source) (DominionCellData a target)
constantDataMap _ = identityDominionCellInsertion

{-@ opaque-reflect atlasActionDataAt @-}
{-@ opaque-reflect constantAction @-}
{-@ constantAction :: category:PageElements scope origin final -> owner:Dominion a
      -> {action:AtlasDataAction scope (DominionCellData a) |
           atlasActionDomain action == pageElementDomain category
           && atlasActionMembership action == atlasMembership acceptsConstantDatum
           && atlasActionDataAt action == constantDataAt owner
           && atlasActionMap action == constantDataMap} @-}
constantAction :: PageElements scope origin final -> Dominion a -> AtlasDataAction scope (DominionCellData a)
constantAction category owner =
  atlasPredicateDataAction category acceptsConstantDatum (constantDataAt owner) constantDataMap

-- | A shaped transport within one page retains its position. The lookup
-- theorem supplies the target position; offset zero reads the source head.
-- ALIGN: DOMINC-SAME-PAGE-POSITION.
{-@ samePagePosition :: category:PageElements scope origin final
      -> arrow:{PageElementArrow scope source target |
           pageElementTraceValid category (arrowSource arrow)
           && pageElementTraceValid category (arrowTarget arrow)
           && pageElementPage (arrowSource arrow) == pageElementPage (arrowTarget arrow)}
      -> {pageElementPosition (arrowSource arrow) == pageElementPosition (arrowTarget arrow)} @-}
samePagePosition :: PageElements scope origin final -> PageElementArrow scope source target -> ()
samePagePosition category arrow =
  pageElementValidArrowPosition category arrow `seq`
  pageElementTraceValidShape category (arrowSource arrow) `seq`
  case pageElementTrace (arrowSource arrow) of
    [] -> ()
    _ : _ -> ()

-- | The cardinality premise is required: constant data on distinct cells of
-- a larger finite page would violate disjointness.
-- ALIGN: DOMINC-CONSTANT-LAWS.
{-@ opaque-reflect atlasPresentationAction @-}
{-@ constantPresentation :: pages:{Pagination scope origin final |
           folioLength (pageElementsFolio (paginationPageElements pages)) == 1}
      -> owner:Dominion a
      -> {presentation:AtlasPresentation scope (DominionCellData a) origin final |
           atlasPresentationPagination presentation == pages
           && atlasPresentationAction presentation == constantAction (paginationPageElements pages) owner
           && atlasActionMembership (atlasPresentationAction presentation) == atlasMembership acceptsConstantDatum
           && atlasActionMap (atlasPresentationAction presentation) == constantDataMap} @-}
constantPresentation :: Pagination scope origin final -> Dominion a
  -> AtlasPresentation scope (DominionCellData a) origin final
constantPresentation pages owner =
  let category = paginationPageElements pages
      action = constantAction category owner
  in atlasPresentationForPredicate pages acceptsConstantDatum action
       (\occurrence datum ->
          constantDataMap (normalizePageElementArrow category (identityPageElementArrow occurrence)) `seq`
          identityCellMapIdentity datum)
       (\second first _ datum ->
          constantDataMap (normalizePageElementArrow category (composePageElementArrows second first)) `seq`
          constantDataMap (normalizePageElementArrow category second) `seq`
          constantDataMap (normalizePageElementArrow category first) `seq`
          identityCellMapComposition datum)
       (\_ arrow _ datum ->
          constantDataMap (normalizePageElementArrow category arrow) `seq`
          identityCellMapIdentity datum)
       (\_ _ leftArrow rightArrow conditions _ _ ->
          conditions `seq`
          pageElementPage (arrowSource leftArrow) `seq`
          samePagePosition category leftArrow `seq` samePagePosition category rightArrow)
