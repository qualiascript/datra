{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
-- Preserve indexed presentation types when applying fixed class dictionaries.
{-@ LIQUID "--fast" @-}

-- | Allocate the checked chained presentation from a fixed instance recipe.
module ChainedDominionAtlas.Canonical
  ( CanonicalChainedDominion (..), CanonicalChainedAtlasScope, CanonicalChainedPaginationScope
  , canonicalChainedFirst, canonicalChainedChain, canonicalChainedValueDominion
  , canonicalPagination, canonicalPresentation
  , canonicalChainedDominionAtlas
  ) where

import Atlas
  ( AtlasPresentation, atlasDescription, atlasPagination
  , atlasPresentationPagination, atlasPresentationAction
  , atlasActionMembership, atlasActionDataAt, atlasActionMap, atlasMembership )
import Atlas.Construction (AtlasConstruction (..), FixedAtlasScope, constructAtlas)
import Chain (Chain)
import ChainedDominionAtlas.Data (ChainedDominionCellData)
import ChainedDominionAtlas.Owner
  ( ChainedDominionAtlas, retainChainedPresentation, chainedDominionAtlas
  , chainedDominionFirst, chainedDominionChain, chainedDominionValueDominion )
import ChainedDominionAtlas.Presentation
  ( chainedDominionFolio, chainedDominionPresentation, chainedDominionAction
  , chainedDominionAccepts, chainedDominionAt, chainedDominionDataMap )
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Dominion (Dominion)
import Folio (Folio, folioLength, lastChain)
import PageElements (pageElementsFolio)
import PageElements.Construction
  ( PageElementsConstruction (..), ConstructedPageElementsScope, constructPageElements )
import Pagination (Pagination, paginationPageElements, paginationFromPageElements)

-- | An instance fixes the first value, complete chain, and Dominion together.
class CanonicalChainedDominion value where
  canonicalChainedDominion :: Proxy value -> (value, Chain value, Dominion value)

data CanonicalChainedRecipe (value :: Type)
type CanonicalChainedPaginationScope value =
  ConstructedPageElementsScope (CanonicalChainedRecipe value) () value
type CanonicalChainedAtlasScope value =
  FixedAtlasScope (CanonicalChainedRecipe value) (CanonicalChainedPaginationScope value)
    (ChainedDominionCellData value) () value

{-@ opaque-reflect canonicalChainedDominion @-}
-- ALIGN: CHAINED-CANONICAL-FIRST.
{-@ reflect canonicalChainedFirst @-}
canonicalChainedFirst :: CanonicalChainedDominion value => Proxy value -> value
canonicalChainedFirst proxy = case canonicalChainedDominion proxy of (first, _, _) -> first

-- ALIGN: CHAINED-CANONICAL-CHAIN.
{-@ reflect canonicalChainedChain @-}
canonicalChainedChain :: CanonicalChainedDominion value => Proxy value -> Chain value
canonicalChainedChain proxy = case canonicalChainedDominion proxy of (_, chain, _) -> chain

-- ALIGN: CHAINED-CANONICAL-DOMINION.
{-@ reflect canonicalChainedValueDominion @-}
canonicalChainedValueDominion :: CanonicalChainedDominion value => Proxy value -> Dominion value
canonicalChainedValueDominion proxy = case canonicalChainedDominion proxy of (_, _, dominion) -> dominion

{-@ reflect recipeProxy @-}
recipeProxy :: Proxy value -> Proxy (CanonicalChainedRecipe value)
recipeProxy _ = Proxy

{-@ reflect valueProxy @-}
valueProxy :: Proxy (CanonicalChainedRecipe value) -> Proxy value
valueProxy _ = Proxy

{-@ instance CanonicalChainedDominion value => PageElementsConstruction (CanonicalChainedRecipe value) (()) value where
      pageElementsRecipe :: recipe:Proxy Type (CanonicalChainedRecipe value)
        -> {pages:Folio () value | folioLength pages == 2
             && lastChain pages == canonicalChainedChain (valueProxy recipe)}
  @-}
instance CanonicalChainedDominion value => PageElementsConstruction (CanonicalChainedRecipe value) () value where
  pageElementsRecipe recipe =
    let proxy = valueProxy recipe
    in chainedDominionFolio (canonicalChainedFirst proxy) (canonicalChainedChain proxy)

-- ALIGN: CHAINED-CANONICAL-PAGINATION.
{-@ opaque-reflect canonicalPagination @-}
{-@ canonicalPagination :: CanonicalChainedDominion value => proxy:Proxy value
      -> {pages:Pagination (CanonicalChainedPaginationScope value) () value |
           folioLength (pageElementsFolio (paginationPageElements pages)) == 2
           && lastChain (pageElementsFolio (paginationPageElements pages)) == canonicalChainedChain proxy} @-}
canonicalPagination :: forall value. CanonicalChainedDominion value
  => Proxy value -> Pagination (CanonicalChainedPaginationScope value) () value
canonicalPagination proxy@Proxy =
  let recipe = recipeProxy proxy
  in (pageElementsRecipe recipe :: Folio () value) `seq`
       paginationFromPageElements (constructPageElements recipe)

-- ALIGN: CHAINED-CANONICAL-PRESENTATION.
{-@ canonicalPresentation :: CanonicalChainedDominion value => proxy:Proxy value
      -> {presentation:AtlasPresentation (CanonicalChainedPaginationScope value) (ChainedDominionCellData value) () value |
           atlasPresentationPagination presentation == canonicalPagination proxy
           && folioLength (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == 2
           && lastChain (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == canonicalChainedChain proxy
           && atlasPresentationAction presentation
                == chainedDominionAction (paginationPageElements (atlasPresentationPagination presentation))
                     (canonicalChainedFirst proxy) (canonicalChainedChain proxy) (canonicalChainedValueDominion proxy)
           && atlasActionMembership (atlasPresentationAction presentation)
                == atlasMembership (chainedDominionAccepts (canonicalChainedFirst proxy) (canonicalChainedChain proxy))
           && atlasActionDataAt (atlasPresentationAction presentation)
                == chainedDominionAt (canonicalChainedFirst proxy) (canonicalChainedChain proxy) (canonicalChainedValueDominion proxy)
           && atlasActionMap (atlasPresentationAction presentation)
                == chainedDominionDataMap (paginationPageElements (atlasPresentationPagination presentation))
                     (canonicalChainedFirst proxy) (canonicalChainedChain proxy)} @-}
canonicalPresentation :: CanonicalChainedDominion value
  => Proxy value -> AtlasPresentation (CanonicalChainedPaginationScope value) (ChainedDominionCellData value) () value
canonicalPresentation proxy = chainedDominionPresentation (canonicalPagination proxy)
  (canonicalChainedFirst proxy) (canonicalChainedChain proxy) (canonicalChainedValueDominion proxy)

{-@ opaque-reflect canonicalPresentation @-}
{-@ instance CanonicalChainedDominion value => AtlasConstruction (CanonicalChainedRecipe value)
      (CanonicalChainedPaginationScope value) (ChainedDominionCellData value) (()) value where
      atlasConstructionPresentation :: recipe:Proxy Type (CanonicalChainedRecipe value)
        -> {presentation:AtlasPresentation (CanonicalChainedPaginationScope value) (ChainedDominionCellData value) () value |
             presentation == canonicalPresentation (valueProxy recipe)
             && atlasPresentationPagination presentation == canonicalPagination (valueProxy recipe)
             && folioLength (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == 2
             && lastChain (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == canonicalChainedChain (valueProxy recipe)
             && atlasPresentationAction presentation
                  == chainedDominionAction (paginationPageElements (atlasPresentationPagination presentation))
                       (canonicalChainedFirst (valueProxy recipe)) (canonicalChainedChain (valueProxy recipe)) (canonicalChainedValueDominion (valueProxy recipe))
             && atlasActionMembership (atlasPresentationAction presentation)
                  == atlasMembership (chainedDominionAccepts (canonicalChainedFirst (valueProxy recipe)) (canonicalChainedChain (valueProxy recipe)))
             && atlasActionDataAt (atlasPresentationAction presentation)
                  == chainedDominionAt (canonicalChainedFirst (valueProxy recipe)) (canonicalChainedChain (valueProxy recipe)) (canonicalChainedValueDominion (valueProxy recipe))
             && atlasActionMap (atlasPresentationAction presentation)
                  == chainedDominionDataMap (paginationPageElements (atlasPresentationPagination presentation))
                       (canonicalChainedFirst (valueProxy recipe)) (canonicalChainedChain (valueProxy recipe))}
  @-}
instance CanonicalChainedDominion value => AtlasConstruction (CanonicalChainedRecipe value)
    (CanonicalChainedPaginationScope value) (ChainedDominionCellData value) () value where
  atlasConstructionPresentation recipe = canonicalPresentation (valueProxy recipe)

-- ALIGN: CHAINED-CANONICAL-OWNER.
{-@ canonicalOwner :: CanonicalChainedDominion value => proxy:Proxy value
      -> {owner:ChainedDominionAtlas (CanonicalChainedAtlasScope value) (CanonicalChainedPaginationScope value) value |
           chainedDominionFirst owner == canonicalChainedFirst proxy
           && chainedDominionChain owner == canonicalChainedChain proxy
           && chainedDominionValueDominion owner == canonicalChainedValueDominion proxy
           && atlasDescription (chainedDominionAtlas owner) == canonicalPresentation proxy
           && atlasPagination (chainedDominionAtlas owner) == canonicalPagination proxy} @-}
canonicalOwner :: forall value. CanonicalChainedDominion value => Proxy value
  -> ChainedDominionAtlas (CanonicalChainedAtlasScope value) (CanonicalChainedPaginationScope value) value
canonicalOwner proxy@Proxy =
  let recipe = recipeProxy proxy
      presentation = atlasConstructionPresentation recipe
        :: AtlasPresentation (CanonicalChainedPaginationScope value) (ChainedDominionCellData value) () value
      valueAtlas = constructAtlas recipe
  in retainChainedPresentation (canonicalChainedFirst proxy) (canonicalChainedChain proxy)
       (canonicalChainedValueDominion proxy) presentation valueAtlas

-- ALIGN: CHAINED-CANONICAL-ALLOCATION.
-- ALIGN: CHAINED-CANONICAL-INPUTS.
-- ALIGN: CHAINED-CANONICAL-DESCRIPTION.
-- ALIGN: CHAINED-CANONICAL-PAGINATION-OBSERVATION.
{-@ canonicalChainedDominionAtlas :: CanonicalChainedDominion value
      => {owner:ChainedDominionAtlas (CanonicalChainedAtlasScope value) (CanonicalChainedPaginationScope value) value |
           chainedDominionFirst owner == canonicalChainedFirst Proxy
           && chainedDominionChain owner == canonicalChainedChain Proxy
           && chainedDominionValueDominion owner == canonicalChainedValueDominion Proxy
           && atlasDescription (chainedDominionAtlas owner) == canonicalPresentation Proxy
           && atlasPagination (chainedDominionAtlas owner) == canonicalPagination Proxy} @-}
canonicalChainedDominionAtlas :: forall value. CanonicalChainedDominion value
  => ChainedDominionAtlas (CanonicalChainedAtlasScope value) (CanonicalChainedPaginationScope value) value
canonicalChainedDominionAtlas = canonicalOwner (Proxy :: Proxy value)
