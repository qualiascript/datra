{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden runtime representation of the LiquidHaskell-checked Atlas category.
module Atlas.Morphism.Internal
  ( AtlasMorphism
  , AtlasMorphismAction
  , AtlasObjectMap
  , AtlasMappedObject
  , IdentityAtlasObjectMap
  , identityAtlasObjectMap
  , atlasObjectMap
  , AtlasMorphismImage
  , atlasMorphismAction
  , atlasMorphism
  , withAtlasMorphismImage
  , atlasMorphismPagination
  , mapAtlasMorphismElement
  , mapAtlasMorphismArrow
  , mapAtlasMorphismData
  , AtlasCategory
  , atlasCategory
  , atlasCategoryIdentity
  , atlasCategoryCompose
  , identityAtlasMorphism
  , composeAtlasMorphisms
  ) where

import Atlas.Internal
  ( Atlas
  , atlasCoherence
  , normalizeAtlasElement
  )
import Atlas.Morphism.LiquidInternal
  ( AtlasMorphismAction
  , AtlasObjectMap
  , AtlasMappedObject
  , IdentityAtlasObjectMap
  , identityAtlasObjectMap
  , atlasObjectMap
  , atlasMorphismAction
  , atlasMorphismActionPreservesArrow
  , atlasMorphismSource
  , atlasMorphismTarget
  , mapAtlasMorphismActionComponent
  , mapAtlasMorphismActionElement
  , mapAtlasMorphismActionObject
  )
import Data.Kind (Type)
import DomanialInsertion
  ( DomanialInsertion
  , composeInsertions
  , identityInsertion
  )
import PageElements
  ( PageElement
  , PageElementArrow
  )
import PageElements.Internal (SomePageElement (..))
import Pagination
  ( PaginationMorphism
  , SomePageElementArrow
  , composePaginationMorphisms
  , mapPaginationArrow
  , paginationMorphism
  )

-- | The observable image of one source cell. Its target identity remains
-- existential, keeping the target cell and its correctly indexed data
-- insertion together.
type role AtlasMorphismImage nominal nominal nominal nominal
data AtlasMorphismImage
  (targetScope :: Type)
  (sourceCellData :: Type -> Type)
  (targetCellData :: Type -> Type)
  (sourceObject :: Type) where
  AtlasMorphismImage
    :: PageElement targetScope targetObject
    -> DomanialInsertion
         (sourceCellData sourceObject)
         (targetCellData targetObject)
    -> AtlasMorphismImage
         targetScope sourceCellData targetCellData sourceObject

-- | Eliminate the hidden target-cell identity of a mapped Atlas cell.
withAtlasMorphismImage
  :: AtlasMorphismImage
       targetScope sourceCellData targetCellData sourceObject
  -> (forall targetObject.
        PageElement targetScope targetObject
        -> DomanialInsertion
             (sourceCellData sourceObject)
             (targetCellData targetObject)
        -> result)
  -> result
withAtlasMorphismImage (AtlasMorphismImage target insertion) useImage =
  useImage target insertion

-- | A morphism is a LiquidHaskell-checked primitive, an object's coherence
-- identity, or a categorical composite. The structural identity/composite
-- cases ensure those operations cannot bypass the primitive proof boundary.
type role AtlasMorphism nominal nominal nominal nominal nominal nominal
data AtlasMorphism
  (sourceAtlasScope :: Type)
  (targetAtlasScope :: Type)
  (sourceScope :: Type)
  (targetScope :: Type)
  (sourceCellData :: Type -> Type)
  (targetCellData :: Type -> Type) where
  PrimitiveAtlasMorphism
    :: AtlasMorphismAction
         objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
         sourceCellData targetCellData
         sourceOrigin sourceFinal targetOrigin targetFinal
    -> AtlasMorphism
         sourceAtlasScope targetAtlasScope
         sourceScope targetScope sourceCellData targetCellData
  IdentityAtlasMorphism
    :: Atlas atlasScope scope cellData origin final
    -> AtlasMorphism atlasScope atlasScope scope scope cellData cellData
  CompositeAtlasMorphism
    :: AtlasMorphism
         middleAtlasScope targetAtlasScope
         middleScope targetScope middleCellData targetCellData
    -> AtlasMorphism
         sourceAtlasScope middleAtlasScope
         sourceScope middleScope sourceCellData middleCellData
    -> AtlasMorphism
         sourceAtlasScope targetAtlasScope
         sourceScope targetScope sourceCellData targetCellData

-- | Promote a checked primitive action to an Atlas morphism.
atlasMorphism
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> AtlasMorphism
       sourceAtlasScope targetAtlasScope
       sourceScope targetScope sourceCellData targetCellData
atlasMorphism = PrimitiveAtlasMorphism

-- | Apply an Atlas morphism to a cell and its attached data carrier.
-- Primitive maps normalize at both boundaries. Identity is coherence;
-- composition recursively inserts the middle object's coherence.
mapAtlasMorphismData
  :: AtlasMorphism
       sourceAtlasScope targetAtlasScope
       sourceScope targetScope sourceCellData targetCellData
  -> PageElement sourceScope sourceObject
  -> AtlasMorphismImage
       targetScope sourceCellData targetCellData sourceObject
mapAtlasMorphismData (PrimitiveAtlasMorphism action) source =
  let sourceAtlas = atlasMorphismSource action
      targetAtlas = atlasMorphismTarget action
      normalizedSource = normalizeAtlasElement sourceAtlas source
  in AtlasMorphismImage
      (normalizeAtlasElement targetAtlas
        (mapAtlasMorphismActionObject action normalizedSource))
      (mapAtlasMorphismActionComponent action normalizedSource)
mapAtlasMorphismData (IdentityAtlasMorphism valueAtlas) source =
  AtlasMorphismImage
    (normalizeAtlasElement valueAtlas source)
    identityInsertion
mapAtlasMorphismData (CompositeAtlasMorphism second first) source =
  withAtlasMorphismImage
    (mapAtlasMorphismData first source) $ \middle firstInsertion ->
      withAtlasMorphismImage
        (mapAtlasMorphismData second middle) $ \target secondInsertion ->
          AtlasMorphismImage target
            (composeInsertions secondInsertion firstInsertion)

-- | Apply the page-element part of an Atlas morphism.
mapAtlasMorphismElement
  :: AtlasMorphism
       sourceAtlasScope targetAtlasScope
       sourceScope targetScope sourceCellData targetCellData
  -> PageElement sourceScope sourceObject
  -> SomePageElement targetScope
mapAtlasMorphismElement morphism source =
  withAtlasMorphismImage
    (mapAtlasMorphismData morphism source)
    (\target _ -> SomePageElement target)

-- | Recover the induced functor on the full padded page-element spines.
atlasMorphismPagination
  :: AtlasMorphism
       sourceAtlasScope targetAtlasScope
       sourceScope targetScope sourceCellData targetCellData
  -> PaginationMorphism sourceScope targetScope
atlasMorphismPagination (PrimitiveAtlasMorphism action) =
  paginationMorphism
    (mapAtlasMorphismActionElement action)
    (atlasMorphismActionPreservesArrow action)
atlasMorphismPagination (IdentityAtlasMorphism valueAtlas) =
  atlasCoherence valueAtlas
atlasMorphismPagination (CompositeAtlasMorphism second first) =
  composePaginationMorphisms
    (atlasMorphismPagination second)
    (atlasMorphismPagination first)

-- | Apply the page-element part of an Atlas morphism to an arrow.
mapAtlasMorphismArrow
  :: AtlasMorphism
       sourceAtlasScope targetAtlasScope
       sourceScope targetScope sourceCellData targetCellData
  -> PageElementArrow sourceScope sourceObject targetObject
  -> SomePageElementArrow targetScope
mapAtlasMorphismArrow morphism =
  mapPaginationArrow (atlasMorphismPagination morphism)

-- | The coherent identity of a particular Atlas. Its page action is the
-- normalization idempotent, not the raw full-spine identity.
identityAtlasMorphism
  :: Atlas atlasScope scope cellData origin final
  -> AtlasMorphism atlasScope atlasScope scope scope cellData cellData
identityAtlasMorphism = IdentityAtlasMorphism

-- | Compose in categorical order. Recursive evaluation explicitly retains
-- the middle Atlas coherence, giving Karoubi composition @g . eMiddle . f@.
composeAtlasMorphisms
  :: AtlasMorphism
       middleAtlasScope targetAtlasScope
       middleScope targetScope middleCellData targetCellData
  -> AtlasMorphism
       sourceAtlasScope middleAtlasScope
       sourceScope middleScope sourceCellData middleCellData
  -> AtlasMorphism
       sourceAtlasScope targetAtlasScope
       sourceScope targetScope sourceCellData targetCellData
composeAtlasMorphisms = CompositeAtlasMorphism

-- | A first-class witness for the Atlas category operations. This is
-- deliberately not a 'Control.Category' instance: categorical identity needs
-- the actual Atlas value in order to recover its coherence map.
--
-- The category laws are extensional on 'mapAtlasMorphismData'. Left and right
-- identity reduce to idempotence of the endpoint normalizations plus identity
-- of 'identityInsertion'; associativity reduces to ordinary function and
-- insertion composition. In particular, the full-spine identity at @X@ is
-- @X@'s coherence idempotent @eX@, so a composite has the Karoubi shape
-- @g . eY . f@ rather than silently treating padded occurrences as genuine.
data AtlasCategory = AtlasCategory

-- | The category of checked Atlases and checked Atlas morphisms.
atlasCategory :: AtlasCategory
atlasCategory = AtlasCategory

-- | Select the object-dependent identity operation.
atlasCategoryIdentity
  :: AtlasCategory
  -> Atlas atlasScope scope cellData origin final
  -> AtlasMorphism atlasScope atlasScope scope scope cellData cellData
atlasCategoryIdentity AtlasCategory = identityAtlasMorphism

-- | Select categorical composition.
atlasCategoryCompose
  :: AtlasCategory
  -> AtlasMorphism
       middleAtlasScope targetAtlasScope
       middleScope targetScope middleCellData targetCellData
  -> AtlasMorphism
       sourceAtlasScope middleAtlasScope
       sourceScope middleScope sourceCellData middleCellData
  -> AtlasMorphism
       sourceAtlasScope targetAtlasScope
       sourceScope targetScope sourceCellData targetCellData
atlasCategoryCompose AtlasCategory = composeAtlasMorphisms
