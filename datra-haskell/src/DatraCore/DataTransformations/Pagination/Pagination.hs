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
  , pagination
  , paginationFolio
  , paginationPageElements
  , paginationCardinality
  , normalizePaginationElement
  , normalizePaginationArrow
  , paginationCoherence
  , paginationCoherenceIdempotent
  , withPageElementArrow
  )
