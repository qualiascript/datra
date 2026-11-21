{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--fast" @-}

-- | Stable object actions whose recipe is fixed by their data-family instance.
module Atlas.Construction
  ( AtlasDataConstruction (..)
  , ConstructedAtlasScope
  , constructAtlasData
  ) where

import Data.Kind (Type)
import Atlas
  ( Atlas, AtlasPresentation, atlasPagination, atlasPresentationPagination )
import qualified Atlas.Internal as Internal (atlasFromPresentationWithScope)

-- | The recipe and original owner jointly name the derived Atlas. All indices
-- are nominal, so distinct recipes and original owners cannot be coerced together.
type role ConstructedAtlasScope nominal nominal nominal nominal
data ConstructedAtlasScope
  (construction :: Type -> Type -> (Type -> Type) -> Type -> Type)
  (atlasScope :: Type) (scope :: Type) (cellData :: Type -> Type)

-- | A construction is a pure, instance-defined recipe, not a per-call callback.
-- Its checked presentation must retain the original pagination.
{-@ class AtlasDataConstruction construction where
      atlasDataPresentation :: forall a s d o f. owner:Atlas a s d o f
        -> {presentation:AtlasPresentation s (construction a s d) o f |
             atlasPresentationPagination presentation == atlasPagination owner}
  @-}
class AtlasDataConstruction
    (construction :: Type -> Type -> (Type -> Type) -> Type -> Type) where
  atlasDataPresentation :: forall a s d o f. Atlas a s d o f -> AtlasPresentation s (construction a s d) o f

-- ALIGN: ATLAS-DATA-CONSTRUCTION.
-- ALIGN: ATLAS-DATA-CONSTRUCTION-PAGINATION.
{-@ constructAtlasData :: AtlasDataConstruction construction
      => owner:Atlas a s d o f
      -> {value:Atlas (ConstructedAtlasScope construction a s d) s (construction a s d) o f |
           atlasPagination value == atlasPagination owner} @-}
constructAtlasData :: AtlasDataConstruction construction
  => Atlas a s d o f
  -> Atlas (ConstructedAtlasScope construction a s d) s (construction a s d) o f
constructAtlasData owner = Internal.atlasFromPresentationWithScope (atlasDataPresentation owner)
