{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | Hidden representation of paginations and pagination morphisms.
module Pagination.Internal
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

import Control.Category (Category (..))
import Data.Kind (Type)
import Folio (Folio)
import Folio.LiquidInternal
  ( folioLengthData
  )
import Numeric.Natural (Natural)
import PageElements
  ( PageElements
  , normalizePageElement
  , normalizePageElementArrow
  , pageElements
  )
import PageElements.LiquidInternal hiding (withPageElementArrow)
import Pagination.LiquidInternal
  ( composePaginationMorphismsData
  , identityPaginationMorphismData
  , mapPaginationArrowData
  , mapPaginationElementData
  , normalizationPaginationMorphismData
  , normalizationPaginationMorphismIdempotent
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

-- | The number of genuine pages in the pagination's finite presentation.
-- Every greater page number denotes a repeated occurrence of its final page.
paginationCardinality
  :: Pagination scope origin final
  -> Natural
{-@ reflect paginationCardinality @-}
paginationCardinality (Pagination pages _) = folioLengthData pages

-- | Collapse a tall occurrence to its representative at or before the final
-- genuine page.
normalizePaginationElement
  :: Pagination scope origin final
  -> PageElement scope object
  -> PageElement scope object
normalizePaginationElement paginationValue =
  normalizePageElement (paginationPageElements paginationValue)

-- | Normalize both endpoints of a tall page-element arrow.
normalizePaginationArrow
  :: Pagination scope origin final
  -> PageElementArrow scope source target
  -> PageElementArrow scope source target
normalizePaginationArrow paginationValue =
  normalizePageElementArrow (paginationPageElements paginationValue)

-- | The idempotent endomorphism selecting the coherent finite representative
-- of every occurrence on the tall padded spine.
paginationCoherence
  :: Pagination scope origin final
  -> PaginationMorphism scope scope
paginationCoherence paginationValue =
  PaginationMorphism
    (normalizationPaginationMorphismData
      (paginationCardinality paginationValue - 1)
      (fromIntegral (paginationCardinality paginationValue)))

-- | Pointwise witness that pagination coherence is idempotent.
paginationCoherenceIdempotent
  :: Pagination scope origin final
  -> PageElement scope object
  -> ()
paginationCoherenceIdempotent paginationValue =
  normalizationPaginationMorphismIdempotent
    (paginationCardinality paginationValue - 1)
    (fromIntegral (paginationCardinality paginationValue))

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
  PaginationMorphism
    (Liquid.paginationMorphism mapObject
      (\source target -> preservesArrow source target))

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
