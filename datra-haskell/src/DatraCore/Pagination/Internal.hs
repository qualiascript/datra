{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden representation of paginations and pagination morphisms.
module Pagination.Internal
  ( Pagination
  , PaginationMorphism
  , SomePageElementArrow
  , pagination
  , paginationFolio
  , paginationPageElements
  , mapPaginationElement
  , mapPaginationArrow
  , withPageElementArrow
  , identityPaginationMorphism
  , composePaginationMorphisms
  , wrapPaginationMorphism
  ) where

import Control.Category (Category (..))
import Data.Kind (Type)
import Folio (Folio)
import PageElements
  ( PageElement
  , PageElementArrow
  , PageElements
  , SomePageElement
  , pageElements
  )
import Pagination.LiquidInternal
  ( SomePageElementArrow
  , composePaginationMorphismsData
  , identityPaginationMorphismData
  , mapPaginationArrowData
  , mapPaginationElementData
  , withPageElementArrowData
  )
import qualified Pagination.LiquidInternal as Liquid
import Prelude hiding ((.), id)

-- | A folio paired with the category of page elements generated from it.
-- The nominal @scope@ makes the association generative: page elements from a
-- different pagination cannot be substituted, even when both folios have the
-- same Haskell carrier types.
type role Pagination nominal nominal nominal
data Pagination (scope :: Type) origin final = Pagination
  (Folio origin final)
  (PageElements scope origin final)

-- | Public pagination morphisms wrap the LiquidHaskell-verified
-- representation. Defining the wrapper here keeps its 'Category' instance
-- non-orphan while leaving the proof implementation in the verified module.
type role PaginationMorphism nominal nominal
newtype PaginationMorphism sourceScope targetScope = PaginationMorphism
  (Liquid.PaginationMorphism sourceScope targetScope)

-- | Lift a verified pagination morphism into the public representation.
wrapPaginationMorphism
  :: Liquid.PaginationMorphism sourceScope targetScope
  -> PaginationMorphism sourceScope targetScope
wrapPaginationMorphism = PaginationMorphism

-- | Introduce a pagination with a fresh page-element scope.
pagination
  :: Folio origin final
  -> (forall scope. Pagination scope origin final -> result)
  -> result
pagination pages usePagination =
  pageElements pages $ \elements ->
    usePagination (Pagination pages elements)

-- | Recover the folio from a pagination.
paginationFolio :: Pagination scope origin final -> Folio origin final
paginationFolio (Pagination pages _) = pages

-- | Recover the folio's corresponding category of page elements.
paginationPageElements
  :: Pagination scope origin final
  -> PageElements scope origin final
paginationPageElements (Pagination _ elements) = elements

-- | Apply a pagination morphism to a page element.
mapPaginationElement
  :: PaginationMorphism sourceScope targetScope
  -> PageElement sourceScope object
  -> SomePageElement targetScope
mapPaginationElement (PaginationMorphism morphism) =
  mapPaginationElementData morphism

-- | Apply a pagination morphism to a page-element arrow.
mapPaginationArrow
  :: PaginationMorphism sourceScope targetScope
  -> PageElementArrow sourceScope source target
  -> SomePageElementArrow targetScope
mapPaginationArrow (PaginationMorphism morphism) =
  mapPaginationArrowData morphism

-- | Eliminate the hidden endpoint identities of a mapped arrow.
withPageElementArrow
  :: SomePageElementArrow scope
  -> (forall source target.
        PageElementArrow scope source target -> result)
  -> result
withPageElementArrow = withPageElementArrowData

-- | The identity pagination morphism.
identityPaginationMorphism :: PaginationMorphism scope scope
identityPaginationMorphism =
  PaginationMorphism identityPaginationMorphismData

-- | Compose pagination morphisms in categorical order: the first argument is
-- applied after the second.
composePaginationMorphisms
  :: PaginationMorphism middleScope targetScope
  -> PaginationMorphism sourceScope middleScope
  -> PaginationMorphism sourceScope targetScope
composePaginationMorphisms
  (PaginationMorphism second)
  (PaginationMorphism first) =
    PaginationMorphism (composePaginationMorphismsData second first)

-- | Paginations form a category under their functor morphisms.
instance Category PaginationMorphism where
  id = identityPaginationMorphism
  (.) = composePaginationMorphisms
