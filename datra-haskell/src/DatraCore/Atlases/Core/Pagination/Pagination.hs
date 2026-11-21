{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
#include "../../../LiquidPlugin.h"
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
  , paginationFromPageElements
  , paginationFolio
  , paginationPageElements
  , paginationCardinality
  , normalizePaginationElement
  , normalizePaginationArrow
  , paginationCoherence
  , paginationCoherenceIdempotent
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
  , paginationMorphism
  , paginationFolio
  , paginationPageElements
  , paginationCardinality
  , normalizePaginationElement
  , normalizePaginationArrow
  , paginationCoherence
  , paginationCoherenceIdempotent
  , withPageElementArrow
  )

import Folio (Folio)
import PageElements (PageElements, pageElements, pageElementsFolio)
import qualified Pagination.Internal as Internal (paginationFromPageElements)

-- | Build a pagination from its already owned category of occurrences.
-- ALIGN: PAGINATION-FROM-PAGE-ELEMENTS.
{-@ paginationFromPageElements :: elements:PageElements scope origin final
      -> {value:Pagination scope origin final | paginationPageElements value == elements} @-}
paginationFromPageElements :: PageElements scope origin final -> Pagination scope origin final
paginationFromPageElements = Internal.paginationFromPageElements

-- | Introduce a pagination with a fresh page-element scope.
{-@ pagination :: pages:Folio origin final
      -> (forall scope. value:{Pagination scope origin final |
           pageElementsFolio (paginationPageElements value) == pages} -> result)
      -> result @-}
pagination
  :: Folio origin final
  -> (forall scope. Pagination scope origin final -> result)
  -> result
pagination pages usePagination =
  pageElements pages (\elements -> usePagination (paginationFromPageElements elements))
