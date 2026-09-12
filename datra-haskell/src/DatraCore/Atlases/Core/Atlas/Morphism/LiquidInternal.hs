{-# LANGUAGE CPP #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | LiquidHaskell-verified primitive Atlas morphism actions.
module Atlas.Morphism.LiquidInternal
  ( AtlasMorphismAction
  , AtlasObjectMap
  , AtlasMappedObject
  , IdentityAtlasObjectMap
  , identityAtlasObjectMap
  , atlasObjectMap
  , atlasMorphismAction
  , atlasMorphismSource
  , atlasMorphismTarget
  , mapAtlasMorphismActionObject
  , mapAtlasMorphismActionComponent
  , mapAtlasMorphismActionElement
  , atlasMorphismActionPreservesArrow
  ) where

import Atlas.Internal
import Data.Kind (Type)
import DomanialInsertion.LiquidInternal
import PageElements.LiquidInternal

-- | A canonical page functor and the components of its data natural
-- transformation, checked relative to particular source and target Atlases.
-- Keeping all type parameters explicit avoids losing the dependent object map
-- when this value is existentially hidden by the public morphism type.
type role AtlasMorphismAction
  nominal nominal nominal nominal nominal nominal nominal nominal nominal nominal nominal
data AtlasMorphismAction
  (objectMap :: Type)
  (sourceAtlasScope :: Type)
  (targetAtlasScope :: Type)
  (sourceScope :: Type)
  (targetScope :: Type)
  (sourceCellData :: Type -> Type)
  (targetCellData :: Type -> Type)
  sourceOrigin sourceFinal targetOrigin targetFinal = AtlasMorphismAction
  (Atlas sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal)
  (Atlas targetAtlasScope targetScope targetCellData targetOrigin targetFinal)
  (forall sourceObject.
    PageElement sourceScope sourceObject
    -> PageElement targetScope (AtlasMappedObject objectMap sourceObject))
  (forall sourceObject.
    PageElement sourceScope sourceObject
    -> DomanialInsertion
         (sourceCellData sourceObject)
         (targetCellData (AtlasMappedObject objectMap sourceObject)))
  (forall sourceObject targetObject.
    PageElementArrow sourceScope sourceObject targetObject
    -> sourceCellData sourceObject
    -> ())
  (SomePageElement sourceScope -> SomePageElement sourceScope -> ())

-- | A defunctionalized object-map symbol. Haskell cannot partially apply a
-- type synonym for the identity type function, so a symbol plus an open type
-- family is used to represent both identity and user-defined object maps.
data AtlasObjectMap objectMap = AtlasObjectMap

-- | Interpret an Atlas object-map symbol.
type family AtlasMappedObject (objectMap :: Type) (sourceObject :: Type) :: Type

-- | The object-map symbol used when source and target retain the same phantom
-- object identities.
data IdentityAtlasObjectMap

type instance AtlasMappedObject IdentityAtlasObjectMap sourceObject = sourceObject

-- | Witness the built-in identity object map.
identityAtlasObjectMap :: AtlasObjectMap IdentityAtlasObjectMap
identityAtlasObjectMap = AtlasObjectMap

-- | Witness a user-defined object-map symbol after declaring its
-- 'AtlasMappedObject' equations.
atlasObjectMap :: AtlasObjectMap objectMap
atlasObjectMap = AtlasObjectMap

atlasMorphismSource
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> Atlas sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
atlasMorphismSource (AtlasMorphismAction sourceAtlas _ _ _ _ _) = sourceAtlas

atlasMorphismTarget
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> Atlas targetAtlasScope targetScope targetCellData targetOrigin targetFinal
atlasMorphismTarget (AtlasMorphismAction _ targetAtlas _ _ _ _) = targetAtlas

mapAtlasMorphismActionObject
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> PageElement sourceScope sourceObject
  -> PageElement targetScope (AtlasMappedObject objectMap sourceObject)
mapAtlasMorphismActionObject (AtlasMorphismAction _ _ mapObject _ _ _) =
  mapObject

mapAtlasMorphismActionComponent
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> PageElement sourceScope sourceObject
  -> DomanialInsertion
       (sourceCellData sourceObject)
       (targetCellData (AtlasMappedObject objectMap sourceObject))
mapAtlasMorphismActionComponent
  (AtlasMorphismAction _ _ _ component _ _) = component

mapAtlasMorphismActionElement
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> SomePageElement sourceScope
  -> SomePageElement targetScope
mapAtlasMorphismActionElement action =
  mapPrimitiveElement
    (atlasMorphismObjectMapWitness action)
    (atlasMorphismSource action)
    (atlasMorphismTarget action)
    (mapAtlasMorphismActionObject action)

atlasMorphismObjectMapWitness
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> AtlasObjectMap objectMap
atlasMorphismObjectMapWitness _ = AtlasObjectMap

atlasMorphismActionPreservesArrow
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> SomePageElement sourceScope
  -> SomePageElement sourceScope
  -> ()
atlasMorphismActionPreservesArrow
  (AtlasMorphismAction _ _ _ _ _ preservesArrow) = preservesArrow

{-@ reflect mapPrimitiveElement @-}
mapPrimitiveElement
  :: AtlasObjectMap objectMap
  -> Atlas sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> Atlas targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> (forall sourceObject.
       PageElement sourceScope sourceObject
       -> PageElement targetScope (AtlasMappedObject objectMap sourceObject))
  -> SomePageElement sourceScope
  -> SomePageElement targetScope
mapPrimitiveElement
  _ sourceAtlas targetAtlas mapObject (SomePageElement source) =
    SomePageElement
      (normalizeAtlasElement targetAtlas
        (mapObject (normalizeAtlasElement sourceAtlas source)))

-- | Check the page-functor and data-naturality laws of a primitive Atlas
-- morphism. Normalization appears directly in both laws, so the resulting
-- action is already stable on the entire infinite padded spine.
{-@
atlasMorphismAction
  :: objectMapWitness:AtlasObjectMap objectMap
  -> sourceAtlas:Atlas
       sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> targetAtlas:Atlas
       targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> mapObject:(forall sourceObject.
       PageElement sourceScope sourceObject
       -> PageElement targetScope (AtlasMappedObject objectMap sourceObject))
  -> component:(forall sourceObject.
       PageElement sourceScope sourceObject
       -> DomanialInsertion
            (sourceCellData sourceObject)
            (targetCellData (AtlasMappedObject objectMap sourceObject)))
  -> pageLaw:(sourceValue:SomePageElement sourceScope
       -> targetValue:{SomePageElement sourceScope |
            somePageElementPrecedes sourceValue targetValue
            && somePageElementTransported sourceValue targetValue}
       -> { proof:() |
            somePageElementPrecedes
              (mapPrimitiveElement objectMapWitness sourceAtlas targetAtlas mapObject sourceValue)
              (mapPrimitiveElement objectMapWitness sourceAtlas targetAtlas mapObject targetValue)
            && somePageElementTransported
              (mapPrimitiveElement objectMapWitness sourceAtlas targetAtlas mapObject sourceValue)
              (mapPrimitiveElement objectMapWitness sourceAtlas targetAtlas mapObject targetValue) })
  -> naturalityLaw:(forall sourceObject targetObject.
       sourceArrow:PageElementArrow
         sourceScope sourceObject targetObject
       -> datum:sourceCellData sourceObject
       -> { proof:() |
            applyInsertion
              (component
                (normalizeAtlasElement sourceAtlas
                  (arrowTarget sourceArrow)))
              (applyInsertion
                (mapAtlasData sourceAtlas sourceArrow) datum)
            == applyInsertion
                 (mapAtlasData targetAtlas
                   (pageElementArrow
                     (normalizeAtlasElement targetAtlas
                       (mapObject
                         (normalizeAtlasElement sourceAtlas
                           (arrowSource sourceArrow))))
                     (normalizeAtlasElement targetAtlas
                       (mapObject
                         (normalizeAtlasElement sourceAtlas
                           (arrowTarget sourceArrow))))))
                 (applyInsertion
                   (component
                     (normalizeAtlasElement sourceAtlas
                       (arrowSource sourceArrow)))
                   datum) })
  -> AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
@-}
atlasMorphismAction
  :: AtlasObjectMap objectMap
  -> Atlas sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> Atlas targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> (forall sourceObject.
       PageElement sourceScope sourceObject
       -> PageElement targetScope (AtlasMappedObject objectMap sourceObject))
  -> (forall sourceObject.
       PageElement sourceScope sourceObject
       -> DomanialInsertion
            (sourceCellData sourceObject)
            (targetCellData (AtlasMappedObject objectMap sourceObject)))
  -> (SomePageElement sourceScope -> SomePageElement sourceScope -> ())
  -> (forall sourceObject targetObject.
       PageElementArrow sourceScope sourceObject targetObject
       -> sourceCellData sourceObject
       -> ())
  -> AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
atlasMorphismAction
  _ sourceAtlas targetAtlas mapObject component pageLaw naturalityLaw =
    AtlasMorphismAction
      sourceAtlas
      targetAtlas
      mapObject
      component
      naturalityLaw
      checkedPageLaw
  where
    checkedPageLaw source target
      | somePageElementPrecedes source target
          && somePageElementTransported source target =
            pageLaw source target
      | otherwise = ()
