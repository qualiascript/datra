{-# LANGUAGE GADTs #-}
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
  , paginationMorphism
  , mapPaginationElement
  , mapPaginationArrow
  , withPageElementArrow
  , identityPaginationMorphism
  , composePaginationMorphisms
  ) where

import Control.Category (Category (..))
import Data.Kind (Type)
import Folio (Folio)
import PageElements
  ( PageElement
  , PageElementArrow
  , PageElements
  , arrowSource
  , arrowTarget
  , pageElementArrow
  , pageElements
  , withPageElement
  )
import PageElements.Internal (SomePageElement (..))
import Prelude hiding ((.), id)

-- | A folio paired with the category of page elements generated from it.
-- The nominal @scope@ makes the association generative: page elements from a
-- different pagination cannot be substituted, even when both folios have the
-- same Haskell carrier types.
type role Pagination nominal nominal nominal
data Pagination (scope :: Type) origin final = Pagination
  (Folio origin final)
  (PageElements scope origin final)

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

-- | A functor between the page-element categories of two paginations.
-- Because page-element categories are thin, its action on objects determines
-- the unique possible action on every arrow.
type role PaginationMorphism nominal nominal
newtype PaginationMorphism (sourceScope :: Type) (targetScope :: Type) =
  PaginationMorphism
    (forall object.
      PageElement sourceScope object -> SomePageElement targetScope)

-- | Construct a pagination morphism from its action on page elements.
--
-- LiquidHaskell coherence required for Lean parity: for every source arrow
-- @x -> y@, the mapped occurrences must admit a target arrow
-- @F(x) -> F(y)@. Concretely, the target pages must remain ordered in the
-- opposite spine and transport of @F(x)@ along the target folio must land
-- exactly on @F(y)@. A refinement on @mapObject@ must enforce this condition
-- so that non-functorial object maps are rejected at construction time.
paginationMorphism
  :: Pagination sourceScope sourceOrigin sourceFinal
  -> Pagination targetScope targetOrigin targetFinal
  -> (forall object.
        PageElement sourceScope object -> SomePageElement targetScope)
  -> PaginationMorphism sourceScope targetScope
paginationMorphism _ _ = PaginationMorphism

-- | Apply a pagination morphism to a page element.
mapPaginationElement
  :: PaginationMorphism sourceScope targetScope
  -> PageElement sourceScope object
  -> SomePageElement targetScope
mapPaginationElement (PaginationMorphism mapObject) = mapObject

-- | An arrow whose source and target object indices are existentially hidden.
-- This is the result type needed when a functor changes object identities.
type role SomePageElementArrow nominal
data SomePageElementArrow (scope :: Type) where
  SomePageElementArrow
    :: PageElementArrow scope source target
    -> SomePageElementArrow scope

-- | Apply a pagination morphism to a page-element arrow.
--
-- LiquidHaskell coherence required for Lean parity: the refinement carried by
-- 'paginationMorphism' must prove that its two mapped endpoints admit a target
-- arrow. That fact must justify the call to 'pageElementArrow'.
mapPaginationArrow
  :: PaginationMorphism sourceScope targetScope
  -> PageElementArrow sourceScope source target
  -> SomePageElementArrow targetScope
mapPaginationArrow morphism sourceArrow =
  withPageElement
    (mapPaginationElement morphism (arrowSource sourceArrow)) $ \mappedSource ->
      withPageElement
        (mapPaginationElement morphism (arrowTarget sourceArrow)) $
          \mappedTarget ->
            SomePageElementArrow
              (pageElementArrow mappedSource mappedTarget)

-- | Eliminate the hidden endpoint identities of a mapped arrow.
withPageElementArrow
  :: SomePageElementArrow scope
  -> (forall source target.
        PageElementArrow scope source target -> result)
  -> result
withPageElementArrow (SomePageElementArrow pageArrow) useArrow =
  useArrow pageArrow

-- | The identity pagination morphism.
identityPaginationMorphism :: PaginationMorphism scope scope
identityPaginationMorphism =
  PaginationMorphism SomePageElement

-- | Compose pagination morphisms in categorical order: the first argument is
-- applied after the second.
--
-- LiquidHaskell coherence required for Lean parity: assuming both operands
-- satisfy the arrow-preservation refinement of 'paginationMorphism', prove
-- that their composite also preserves every page-element arrow.
composePaginationMorphisms
  :: PaginationMorphism middleScope targetScope
  -> PaginationMorphism sourceScope middleScope
  -> PaginationMorphism sourceScope targetScope
composePaginationMorphisms
  (PaginationMorphism second)
  (PaginationMorphism first) =
    PaginationMorphism $ \source ->
      withPageElement (first source) second

-- | Paginations form a category under their functor morphisms.
instance Category PaginationMorphism where
  id = identityPaginationMorphism
  (.) = composePaginationMorphisms
