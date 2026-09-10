{-# LANGUAGE CPP #-}
#include "../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | Paginations and their morphisms.
--
-- A pagination packages a folio with the category of page elements generated
-- by that same folio.  A pagination morphism is the Haskell presentation of a
-- functor between two such page-element categories.
module Pagination
  ( Pagination
  , PaginationMorphism
  , SomePageElementArrow
  , pagination
  , paginationFolio
  , paginationPageElements
  , paginationMorphism
  , mapPaginationElement
  , mapPaginationArrow
  , withPageElementArrow
  , identityPaginationMorphism
  , composePaginationMorphisms
  ) where

import Pagination.Internal
  ( Pagination
  , PaginationMorphism
  , SomePageElementArrow
  , composePaginationMorphisms
  , identityPaginationMorphism
  , mapPaginationArrow
  , mapPaginationElement
  , pagination
  , paginationFolio
  , paginationPageElements
  , wrapPaginationMorphism
  , withPageElementArrow
  )

import PageElements.LiquidInternal
  (
  SomePageElement
  )
import qualified Pagination.LiquidInternal as Liquid

-- Keep the types and reflected relation dependencies appearing inside imported
-- page-element refinements in LiquidHaskell's checking environment.

-- | Construct a pagination morphism from its action on objects and a proof
-- that the action preserves every page-element arrow.
{-@
paginationMorphism
  :: mapObject:(SomePageElement sourceScope
       -> SomePageElement targetScope)
  -> (sourceValue:SomePageElement sourceScope
       -> targetValue:{SomePageElement sourceScope |
            somePageElementPrecedes sourceValue targetValue
            && somePageElementTransported sourceValue targetValue}
       -> { proof:() |
            somePageElementPrecedes
              (mapObject sourceValue)
              (mapObject targetValue)
            && somePageElementTransported
              (mapObject sourceValue)
              (mapObject targetValue) })
  -> PaginationMorphism sourceScope targetScope
@-}
paginationMorphism
  :: (SomePageElement sourceScope -> SomePageElement targetScope)
  -> (SomePageElement sourceScope -> SomePageElement sourceScope -> ())
  -> PaginationMorphism sourceScope targetScope
paginationMorphism mapObject preservesArrow =
  wrapPaginationMorphism
    (Liquid.paginationMorphism mapObject preservesArrow)
