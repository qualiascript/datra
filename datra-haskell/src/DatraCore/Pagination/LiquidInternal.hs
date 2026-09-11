{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | LiquidHaskell-verified pagination morphisms.
module Pagination.LiquidInternal
  ( PaginationMorphism (..)
  , SomePageElementArrow
  , paginationMorphism
  , mapPaginationElementData
  , mapPaginationArrowData
  , withPageElementArrowData
  , identityPaginationMorphismData
  , composePaginationMorphismsData
  , normalizationPaginationMorphismData
  , normalizationPaginationMorphismIdempotent
  ) where

import Data.Kind (Type)
import Numeric.Natural (Natural)
import PageElements.LiquidInternal

-- | A functor between two thin page-element categories. The second field is
-- the remaining functoriality obligation: the object map must carry every
-- source arrow to an arrow between the mapped target objects.
{-@
data PaginationMorphism sourceScope targetScope = PaginationMorphism
  { mapPaginationObject :: SomePageElement sourceScope
      -> SomePageElement targetScope
  , paginationMorphismPreservesArrow ::
      sourceValue:SomePageElement sourceScope
      -> targetValue:{SomePageElement sourceScope |
           somePageElementPrecedes sourceValue targetValue
           && somePageElementTransported sourceValue targetValue}
      -> { proof:() |
           somePageElementPrecedes
             (mapPaginationObject sourceValue)
             (mapPaginationObject targetValue)
           && somePageElementTransported
             (mapPaginationObject sourceValue)
             (mapPaginationObject targetValue) }
  }
@-}
type role PaginationMorphism nominal nominal
data PaginationMorphism
  (sourceScope :: Type)
  (targetScope :: Type) = PaginationMorphism
  { mapPaginationObject
      :: SomePageElement sourceScope -> SomePageElement targetScope
  , paginationMorphismPreservesArrow
      :: SomePageElement sourceScope
      -> SomePageElement sourceScope
      -> ()
  }

-- | Construct a pagination morphism from an object map and its proof that
-- both defining conditions of page-element arrows are preserved.
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
paginationMorphism = PaginationMorphism

-- | Normalization is a functor on the tall page-element category.  It clamps
-- page coordinates to the final genuine page and trims repeated final-page
-- entries from transport traces.
normalizationPaginationMorphismData
  :: Natural
  -> Int
  -> PaginationMorphism scope scope
normalizationPaginationMorphismData finalPage traceLimit =
  PaginationMorphism
    (normalizeSomePageElementAt finalPage traceLimit)
    (normalizationPaginationPreservesArrow finalPage traceLimit)

{-@
normalizationPaginationPreservesArrow
  :: finalPage:Natural
  -> traceLimit:Int
  -> sourceValue:SomePageElement scope
  -> targetValue:{SomePageElement scope |
       somePageElementPrecedes sourceValue targetValue
       && somePageElementTransported sourceValue targetValue}
  -> { proof:() |
       somePageElementPrecedes
         (normalizeSomePageElementAt finalPage traceLimit sourceValue)
         (normalizeSomePageElementAt finalPage traceLimit targetValue)
       && somePageElementTransported
         (normalizeSomePageElementAt finalPage traceLimit sourceValue)
         (normalizeSomePageElementAt finalPage traceLimit targetValue) }
@-}
normalizationPaginationPreservesArrow
  :: Natural
  -> Int
  -> SomePageElement scope
  -> SomePageElement scope
  -> ()
normalizationPaginationPreservesArrow
  finalPage traceLimit source target =
    normalizeSomePageElementPreservesArrowAt
      finalPage traceLimit source target

-- | Pointwise idempotence of the normalization pagination morphism.
normalizationPaginationMorphismIdempotent
  :: Natural
  -> Int
  -> PageElement scope object
  -> ()
normalizationPaginationMorphismIdempotent =
  normalizePageElementIdempotentAt

-- | Apply the total object map to a typed source page element.
{-@ reflect mapPaginationElementData @-}
mapPaginationElementData
  :: PaginationMorphism sourceScope targetScope
  -> PageElement sourceScope object
  -> SomePageElement targetScope
mapPaginationElementData morphism source =
  mapPaginationObject morphism (somePageElement source)

-- | Apply a pagination functor to a page-element arrow. LiquidHaskell uses the
-- stored preservation field to establish that the mapped endpoints form a
-- genuine target arrow.
mapPaginationArrowData
  :: PaginationMorphism sourceScope targetScope
  -> PageElementArrow sourceScope source target
  -> SomePageElementArrow targetScope
mapPaginationArrowData morphism sourceArrow =
  let source = somePageElement (arrowSource sourceArrow)
      target = somePageElement (arrowTarget sourceArrow)
      mappedSource = mapPaginationObject morphism source
      mappedTarget = mapPaginationObject morphism target
  in case paginationMorphismPreservesArrow morphism source target of
      () -> somePageElementArrow mappedSource mappedTarget

-- | Eliminate the existential endpoint identities of a mapped arrow.
withPageElementArrowData
  :: SomePageElementArrow scope
  -> (forall source target.
        PageElementArrow scope source target -> result)
  -> result
withPageElementArrowData = withPageElementArrow

-- | The identity object map.
{-@ reflect identityPaginationObject @-}
identityPaginationObject
  :: SomePageElement scope -> SomePageElement scope
identityPaginationObject source = source

-- | Identity preserves every page-element arrow.
{-@
identityPaginationPreservesArrow
  :: sourceValue:SomePageElement scope
  -> targetValue:{SomePageElement scope |
       somePageElementPrecedes sourceValue targetValue
       && somePageElementTransported sourceValue targetValue}
  -> { proof:() |
       somePageElementPrecedes
         (identityPaginationObject sourceValue)
         (identityPaginationObject targetValue)
       && somePageElementTransported
         (identityPaginationObject sourceValue)
         (identityPaginationObject targetValue) }
@-}
identityPaginationPreservesArrow
  :: SomePageElement scope -> SomePageElement scope -> ()
identityPaginationPreservesArrow _ _ = ()

-- | The identity pagination functor.
identityPaginationMorphismData :: PaginationMorphism scope scope
identityPaginationMorphismData =
  PaginationMorphism
    identityPaginationObject
    identityPaginationPreservesArrow

-- | Compose two pagination object maps.
{-@ reflect composePaginationObjectMaps @-}
composePaginationObjectMaps
  :: (SomePageElement middleScope -> SomePageElement targetScope)
  -> (SomePageElement sourceScope -> SomePageElement middleScope)
  -> SomePageElement sourceScope
  -> SomePageElement targetScope
composePaginationObjectMaps second first source = second (first source)

-- | Arrow preservation is closed under composition.
{-@
composePaginationPreservesArrow
  :: secondMap:(SomePageElement middleScope
       -> SomePageElement targetScope)
  -> firstMap:(SomePageElement sourceScope
       -> SomePageElement middleScope)
  -> (middleSource:SomePageElement middleScope
       -> middleTarget:{SomePageElement middleScope |
            somePageElementPrecedes middleSource middleTarget
            && somePageElementTransported middleSource middleTarget}
       -> { proof:() |
            somePageElementPrecedes
              (secondMap middleSource) (secondMap middleTarget)
            && somePageElementTransported
              (secondMap middleSource) (secondMap middleTarget) })
  -> (sourceValue:SomePageElement sourceScope
       -> targetValue:{SomePageElement sourceScope |
            somePageElementPrecedes sourceValue targetValue
            && somePageElementTransported sourceValue targetValue}
       -> { proof:() |
            somePageElementPrecedes
              (firstMap sourceValue) (firstMap targetValue)
            && somePageElementTransported
              (firstMap sourceValue) (firstMap targetValue) })
  -> sourceValue:SomePageElement sourceScope
  -> targetValue:{SomePageElement sourceScope |
       somePageElementPrecedes sourceValue targetValue
       && somePageElementTransported sourceValue targetValue}
  -> { proof:() |
       somePageElementPrecedes
         (composePaginationObjectMaps secondMap firstMap sourceValue)
         (composePaginationObjectMaps secondMap firstMap targetValue)
       && somePageElementTransported
         (composePaginationObjectMaps secondMap firstMap sourceValue)
         (composePaginationObjectMaps secondMap firstMap targetValue) }
@-}
composePaginationPreservesArrow
  :: (SomePageElement middleScope -> SomePageElement targetScope)
  -> (SomePageElement sourceScope -> SomePageElement middleScope)
  -> (SomePageElement middleScope -> SomePageElement middleScope -> ())
  -> (SomePageElement sourceScope -> SomePageElement sourceScope -> ())
  -> SomePageElement sourceScope
  -> SomePageElement sourceScope
  -> ()
composePaginationPreservesArrow
  _secondMap
  firstMap
  secondPreserves
  firstPreserves
  source
  target =
    case firstPreserves source target of
      () -> secondPreserves (firstMap source) (firstMap target)

-- | Compose pagination functors in categorical order.
composePaginationMorphismsData
  :: PaginationMorphism middleScope targetScope
  -> PaginationMorphism sourceScope middleScope
  -> PaginationMorphism sourceScope targetScope
composePaginationMorphismsData
  (PaginationMorphism secondMap secondPreserves)
  (PaginationMorphism firstMap firstPreserves) =
    PaginationMorphism
      (composePaginationObjectMaps secondMap firstMap)
      (composePaginationPreservesArrow
        secondMap
        firstMap
        secondPreserves
        firstPreserves)
