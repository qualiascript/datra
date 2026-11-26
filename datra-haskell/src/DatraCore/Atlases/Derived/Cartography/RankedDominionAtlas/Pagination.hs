{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--fast" @-}

-- | The fixed two-page recipe and its checked ranked presentation.
module RankedDominionAtlas.Pagination
  ( RankedDominionPaginationScope, rankedDominionPagination, rankedPresentation ) where

import Atlas
  ( AtlasPresentation, atlasPresentationPagination, atlasPresentationAction
  , atlasActionMembership, atlasActionDataAt, atlasActionMap, atlasMembership )
import Chain (spine)
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Dominion (Dominion)
import Folio (Folio, folioLength, lastChain)
import Numeric.Natural (Natural)
import PageElements (pageElementsFolio)
import PageElements.Construction
  ( PageElementsConstruction (..), ConstructedPageElementsScope, constructPageElements )
import Pagination (Pagination, paginationPageElements, paginationFromPageElements)
import RankedDominionAtlas.Data (RankedDominionCellData)
import RankedDominionAtlas.Presentation
  ( rankedDominionFolio, rankedDominionPresentation, rankedDominionAction
  , rankedDominionAccepts, rankedDominionAt, rankedDominionDataMap )

{-@ opaque-reflect spine @-}
{-@ opaque-reflect rankedDominionFolio @-}

data RankedDominionPaginationRecipe (value :: Type)
type RankedDominionPaginationScope value =
  ConstructedPageElementsScope (RankedDominionPaginationRecipe value) () Natural

{-@ instance PageElementsConstruction (RankedDominionPaginationRecipe value) (()) (Natural) where
      pageElementsRecipe :: Proxy Type (RankedDominionPaginationRecipe value)
        -> {pages:Folio () Natural | pages == rankedDominionFolio
             && folioLength pages == 2 && lastChain pages == spine}
  @-}
instance PageElementsConstruction (RankedDominionPaginationRecipe value) () Natural where
  pageElementsRecipe _ = rankedDominionFolio

{-@ rankedDominionPagination :: Proxy value
      -> {pages:Pagination (RankedDominionPaginationScope value) () Natural |
           pageElementsFolio (paginationPageElements pages) == rankedDominionFolio
           && folioLength (pageElementsFolio (paginationPageElements pages)) == 2
           && lastChain (pageElementsFolio (paginationPageElements pages)) == spine} @-}
-- ALIGN: RANKED-PAGINATION.
rankedDominionPagination :: forall value. Proxy value -> Pagination (RankedDominionPaginationScope value) () Natural
rankedDominionPagination _ =
  let recipe = Proxy :: Proxy (RankedDominionPaginationRecipe value)
  in (pageElementsRecipe recipe :: Folio () Natural) `seq`
       paginationFromPageElements (constructPageElements recipe)

-- ALIGN: RANKED-FIXED-PRESENTATION.
{-@ opaque-reflect rankedPresentation @-}
{-@ rankedPresentation :: owner:Dominion value
      -> {presentation:AtlasPresentation (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural |
           folioLength (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == 2
           && lastChain (pageElementsFolio (paginationPageElements (atlasPresentationPagination presentation))) == spine
           && atlasPresentationAction presentation
                == rankedDominionAction (paginationPageElements (atlasPresentationPagination presentation)) owner
           && atlasActionMembership (atlasPresentationAction presentation) == atlasMembership (rankedDominionAccepts owner)
           && atlasActionDataAt (atlasPresentationAction presentation) == rankedDominionAt owner
           && atlasActionMap (atlasPresentationAction presentation)
                == rankedDominionDataMap (paginationPageElements (atlasPresentationPagination presentation)) owner} @-}
rankedPresentation :: forall value. Dominion value
  -> AtlasPresentation (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural
rankedPresentation owner = rankedDominionPresentation (rankedDominionPagination (Proxy :: Proxy value)) owner
