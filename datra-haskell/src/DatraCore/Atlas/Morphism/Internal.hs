{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

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
  , AtlasObject
  , AtlasObjectAtlasScope
  , AtlasObjectPaginationScope
  , AtlasObjectCellData
  , AtlasWitness
  , atlasWitness
  , AtlasHom
  , atlasHom
  , materializeAtlasHom
  , atlasHomPagination
  , mapAtlasHomElement
  , mapAtlasHomArrow
  , mapAtlasHomData
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
import Control.Category (Category (..))
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
import Prelude hiding ((.), id)

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

-- | A type-level name for one Atlas object. The generative Atlas token is the
-- decisive identity; the pagination scope and data family are retained so an
-- arrow's executable source and target types can be recovered.
type role AtlasObject nominal nominal nominal
data AtlasObject
  (atlasScope :: Type)
  (paginationScope :: Type)
  (cellData :: Type -> Type)

type family AtlasObjectAtlasScope object :: Type where
  AtlasObjectAtlasScope (AtlasObject atlasScope paginationScope cellData) =
    atlasScope

type family AtlasObjectPaginationScope object :: Type where
  AtlasObjectPaginationScope
    (AtlasObject atlasScope paginationScope cellData) = paginationScope

type family AtlasObjectCellData object :: Type -> Type where
  AtlasObjectCellData
    (AtlasObject atlasScope paginationScope cellData) = cellData

-- | Runtime evidence for a type-level 'AtlasObject'. Origin and final-page
-- carrier types remain existential because morphism operations do not expose
-- them.
type role AtlasWitness nominal
data AtlasWitness object where
  AtlasWitness
    :: Atlas atlasScope paginationScope cellData origin final
    -> AtlasWitness (AtlasObject atlasScope paginationScope cellData)

-- | Name an Atlas value as a category object witness.
atlasWitness
  :: Atlas atlasScope paginationScope cellData origin final
  -> AtlasWitness (AtlasObject atlasScope paginationScope cellData)
atlasWitness = AtlasWitness

-- | A genuine 'Control.Category' arrow over type-level Atlas objects.
--
-- Identity is symbolic because 'Category.id' has no value argument. It is
-- interpreted as the witnessed object's coherence morphism by
-- 'materializeAtlasHom'. Primitive arrows retain their checked
-- 'AtlasMorphism'; composition is an indexed syntax node.
type role AtlasHom nominal nominal
data AtlasHom source target where
  PrimitiveAtlasHom
    :: AtlasMorphism
         sourceAtlasScope targetAtlasScope
         sourceScope targetScope sourceCellData targetCellData
    -> AtlasHom
         (AtlasObject sourceAtlasScope sourceScope sourceCellData)
         (AtlasObject targetAtlasScope targetScope targetCellData)
  IdentityAtlasHom
    :: AtlasHom object object
  CompositeAtlasHom
    :: AtlasHom middle target
    -> AtlasHom source middle
    -> AtlasHom source target

-- | Lift a checked semantic morphism into the ordinary category wrapper.
atlasHom
  :: AtlasMorphism
       sourceAtlasScope targetAtlasScope
       sourceScope targetScope sourceCellData targetCellData
  -> AtlasHom
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
atlasHom = PrimitiveAtlasHom

-- | The target object carried by an already materialized morphism.
atlasMorphismTargetWitness
  :: AtlasMorphism
       sourceAtlasScope targetAtlasScope
       sourceScope targetScope sourceCellData targetCellData
  -> AtlasWitness
       (AtlasObject targetAtlasScope targetScope targetCellData)
atlasMorphismTargetWitness (PrimitiveAtlasMorphism action) =
  AtlasWitness (atlasMorphismTarget action)
atlasMorphismTargetWitness (IdentityAtlasMorphism valueAtlas) =
  AtlasWitness valueAtlas
atlasMorphismTargetWitness (CompositeAtlasMorphism second _) =
  atlasMorphismTargetWitness second

-- | Recover the target witness of a symbolic arrow from its source witness.
-- Identity returns its input witness; primitive arrows recover the target
-- Atlas stored by their checked action; composition follows the two stages.
targetAtlasWitness
  :: AtlasWitness source
  -> AtlasHom source target
  -> AtlasWitness target
targetAtlasWitness sourceWitness IdentityAtlasHom = sourceWitness
targetAtlasWitness _ (PrimitiveAtlasHom morphism) =
  atlasMorphismTargetWitness morphism
targetAtlasWitness sourceWitness (CompositeAtlasHom second first) =
  targetAtlasWitness
    (targetAtlasWitness sourceWitness first)
    second

-- | Interpret a symbolic category arrow as the checked semantic morphism for
-- a particular source object. This is where symbolic 'Category.id' becomes
-- 'identityAtlasMorphism', hence the source Atlas's coherence idempotent.
materializeAtlasHom
  :: AtlasWitness source
  -> AtlasHom source target
  -> AtlasMorphism
       (AtlasObjectAtlasScope source)
       (AtlasObjectAtlasScope target)
       (AtlasObjectPaginationScope source)
       (AtlasObjectPaginationScope target)
       (AtlasObjectCellData source)
       (AtlasObjectCellData target)
materializeAtlasHom (AtlasWitness valueAtlas) IdentityAtlasHom =
  identityAtlasMorphism valueAtlas
materializeAtlasHom _ (PrimitiveAtlasHom morphism) = morphism
materializeAtlasHom sourceWitness (CompositeAtlasHom second first) =
  composeAtlasMorphisms
    (materializeAtlasHom
      (targetAtlasWitness sourceWitness first)
      second)
    (materializeAtlasHom sourceWitness first)

-- | Symbolic Atlas arrows form an ordinary Haskell category. Simplifying the
-- two identity cases is sound because primitive actions are already
-- coherence-sandwiched; a standalone identity is still materialized as the
-- object's actual coherence morphism.
instance Category AtlasHom where
  id = IdentityAtlasHom

  IdentityAtlasHom . first = first
  second . IdentityAtlasHom = second
  second . first = CompositeAtlasHom second first

-- | Recover the full-spine pagination functor of a symbolic Atlas arrow.
atlasHomPagination
  :: AtlasWitness source
  -> AtlasHom source target
  -> PaginationMorphism
       (AtlasObjectPaginationScope source)
       (AtlasObjectPaginationScope target)
atlasHomPagination sourceWitness =
  atlasMorphismPagination . materializeAtlasHom sourceWitness

-- | Apply a symbolic Atlas arrow to one page element.
mapAtlasHomElement
  :: AtlasWitness source
  -> AtlasHom source target
  -> PageElement (AtlasObjectPaginationScope source) object
  -> SomePageElement (AtlasObjectPaginationScope target)
mapAtlasHomElement sourceWitness hom =
  mapAtlasMorphismElement (materializeAtlasHom sourceWitness hom)

-- | Apply a symbolic Atlas arrow to a page-element arrow.
mapAtlasHomArrow
  :: AtlasWitness source
  -> AtlasHom source target
  -> PageElementArrow
       (AtlasObjectPaginationScope source) sourceObject targetObject
  -> SomePageElementArrow (AtlasObjectPaginationScope target)
mapAtlasHomArrow sourceWitness hom =
  mapAtlasMorphismArrow (materializeAtlasHom sourceWitness hom)

-- | Apply a symbolic Atlas arrow to a cell and its dependent data component.
mapAtlasHomData
  :: AtlasWitness source
  -> AtlasHom source target
  -> PageElement (AtlasObjectPaginationScope source) sourceObject
  -> AtlasMorphismImage
       (AtlasObjectPaginationScope target)
       (AtlasObjectCellData source)
       (AtlasObjectCellData target)
       sourceObject
mapAtlasHomData sourceWitness hom =
  mapAtlasMorphismData (materializeAtlasHom sourceWitness hom)

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
