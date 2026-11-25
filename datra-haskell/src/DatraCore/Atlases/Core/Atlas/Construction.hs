{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
  , AtlasConstruction (..)
  , FixedAtlasScope
  , constructAtlas
  ) where

import Data.Kind (Type)
import Data.Proxy (Proxy)
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

-- | A complete, fixed recipe has no runtime configuration. The nominal token
-- names that recipe and every index of its checked presentation.
type role FixedAtlasScope nominal nominal nominal nominal nominal
data FixedAtlasScope recipe scope (cellData :: Type -> Type) origin final

class AtlasConstruction (recipe :: Type) scope (cellData :: Type -> Type) origin final where
  atlasConstructionPresentation :: Proxy recipe -> AtlasPresentation scope cellData origin final

-- ALIGN: ATLAS-FIXED-CONSTRUCTION.
-- ALIGN: ATLAS-FIXED-CONSTRUCTION-PAGINATION.
{-@ opaque-reflect atlasConstructionPresentation @-}
{-@ reflect constructAtlas @-}
{-@ constructAtlas :: AtlasConstruction recipe scope cellData origin final
      => recipe:Proxy recipe
      -> {value:Atlas (FixedAtlasScope recipe scope cellData origin final) scope cellData origin final |
           atlasPagination value == atlasPresentationPagination (atlasConstructionPresentation recipe)} @-}
constructAtlas :: AtlasConstruction recipe scope cellData origin final
  => Proxy recipe
  -> Atlas (FixedAtlasScope recipe scope cellData origin final) scope cellData origin final
constructAtlas recipe = Internal.atlasFromPresentationWithScope (atlasConstructionPresentation recipe)
