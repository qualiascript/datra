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
  , CanonicalDominion (..), CanonicalDominionAtlasScope, canonicalDominionAtlas ) where

import Atlas
  ( Atlas, AtlasObject, atlasPagination, atlasFolio, withAtlasPresentation
  , AtlasPresentation, atlasPresentationForPredicate, atlasPresentationPagination, atlasPresentationAction
  , AtlasDataAction, atlasActionDomain, atlasActionMembership, atlasActionDataAt
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
           folioLength (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == 1} @-}
dominionPresentation :: forall a. Dominion a
  -> AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () ()
dominionPresentation owner = constantPresentation (onePagePagination @a) owner

type DominionAtlasObject owner a =
  AtlasObject owner (DominionPaginationScope a) (DominionCellData a)

-- | Keep the dependent family as a parameter of the checked record. The public
-- alias fixes the Dominion family and pagination without partially applying a
-- datatype constructor inside the solver's datatype declaration.
type role DominionAtlasData nominal nominal nominal nominal nominal
{-@ data DominionAtlasData owner scope cellData origin final = DominionAtlas
      { storedDominionAtlas :: {value:Atlas owner scope cellData origin final |
           folioLength (atlasFolio value) == 1} } @-}
data DominionAtlasData owner scope cellData origin final = DominionAtlas
  { storedDominionAtlas :: Atlas owner scope cellData origin final }

type DominionAtlas owner a =
  DominionAtlasData owner (DominionPaginationScope a) (DominionCellData a) () ()

{-@ retainOnePageAtlas :: presentation:{AtlasPresentation scope cellData origin final |
           folioLength (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == 1}
      -> value:{Atlas owner scope cellData origin final |
           atlasPagination value == atlasPresentationPagination presentation}
      -> DominionAtlasData owner scope cellData origin final @-}
retainOnePageAtlas :: AtlasPresentation scope cellData origin final
  -> Atlas owner scope cellData origin final -> DominionAtlasData owner scope cellData origin final
retainOnePageAtlas _ value = atlasFolio value `seq` DominionAtlas value

-- ALIGN: DOMINC-OWNER-CARDINALITY.
{-@ dominionAtlas :: DominionAtlas owner a
      -> {value:Atlas owner (DominionPaginationScope a) (DominionCellData a) () () |
           folioLength (atlasFolio value) == 1} @-}
dominionAtlas :: DominionAtlas owner a
  -> Atlas owner (DominionPaginationScope a) (DominionCellData a) () ()
dominionAtlas (DominionAtlas value) = value

-- ALIGN: DOMINC-ATLAS-INTERPRETATION.
-- ALIGN: DOMINC-STABLE-ISOMORPHISM.
-- ALIGN: DOMINC-OWNER-ALLOCATION.
{-@ withDominionAtlas :: Dominion a
      -> (forall owner. DominionAtlas owner a -> result) -> result @-}
withDominionAtlas :: Dominion a -> (forall owner. DominionAtlas owner a -> result) -> result
withDominionAtlas owner useOwner =
  let presentation = dominionPresentation owner
  in withAtlasPresentation presentation (\value -> useOwner (retainOnePageAtlas presentation value))

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
             folioLength (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == 1}
  @-}
instance CanonicalDominion a => AtlasConstruction (CanonicalDominionRecipe a)
    (DominionPaginationScope a) (DominionCellData a) () () where
  atlasConstructionPresentation _ = dominionPresentation (canonicalDominion (Proxy :: Proxy a))

-- ALIGN: DOMINC-CANONICAL-ALLOCATION.
canonicalDominionAtlas :: forall a. CanonicalDominion a => DominionAtlas (CanonicalDominionAtlasScope a) a
canonicalDominionAtlas =
  let recipe = Proxy :: Proxy (CanonicalDominionRecipe a)
      presentation = atlasConstructionPresentation recipe
        :: AtlasPresentation (DominionPaginationScope a) (DominionCellData a) () ()
      valueAtlas = constructAtlas recipe
  in retainOnePageAtlas presentation valueAtlas

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
           && atlasPresentationAction presentation == constantAction (paginationPageElements pages) owner} @-}
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
