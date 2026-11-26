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
  , identityAtlasMorphismObject
  , identityAtlasMorphismPreservesArrow
  , atlasMorphismSource
  , atlasMorphismTarget
  , mapAtlasMorphismActionObject
  , mapAtlasMorphismActionComponent
  , mapAtlasMorphismActionElement
  , mapPrimitiveElement
  , atlasMorphismActionPreservesArrow
  , atlasMorphismActionNaturality
  , atlasMorphismObjectMapWitness
  , normalizedActionObject
  , normalizeAtlasMorphismAction
  , normalizeAtlasMorphismActionRetains
  ) where

import Atlas.Internal
import qualified PageElements as Elements (pageElementTraceValid)
import Data.Kind (Type)
import DomanialInsertion.Core
  ( DomanialInsertion (..)
  )

import PageElements.Structure
  ( PageElementCell (..)
  , PageElement (..)
  , SomePageElement (..)
  , PageElementArrow (..)
  , SomePageElementArrow (..)
  , somePageElementPrecedes
  , somePageElementTransported
  , pageElementArrow
  , normalizeSomePageElementPreservesArrowAt
  )

{-@ predicate MorphismCellValid A X = Elements.pageElementTraceValid (atlasPageElements A) X @-}

-- | A canonical page functor and the components of its data natural
-- transformation, checked relative to particular source and target Atlases.
-- Keeping all type parameters explicit avoids losing the dependent object map
-- when this value is existentially hidden by the public morphism type.
type role AtlasMorphismAction
  nominal nominal nominal nominal nominal nominal nominal nominal nominal nominal nominal
{-@ data AtlasMorphismAction objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
      sourceCellData targetCellData sourceOrigin sourceFinal targetOrigin targetFinal = AtlasMorphismAction
  { actionWitness :: AtlasObjectMap objectMap
  , actionSource :: Atlas sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  , actionTarget :: Atlas targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  , actionObject :: forall sourceObject.
      source:PageElement sourceScope sourceObject
      -> {target:PageElement targetScope (AtlasMappedObject objectMap sourceObject) |
           MorphismCellValid actionSource source => MorphismCellValid actionTarget target}
  , actionComponent :: forall sourceObject.
      PageElement sourceScope sourceObject
      -> DomanialInsertion
           (sourceCellData sourceObject)
           (targetCellData (AtlasMappedObject objectMap sourceObject))
  , actionNaturality :: forall sourceObject targetObject.
      sourceArrow:PageElementArrow sourceScope sourceObject targetObject
      -> datum:sourceCellData sourceObject
      -> {applyInsertion
          (actionComponent (normalizeAtlasElement actionSource (arrowTarget sourceArrow)))
          (applyInsertion (mapAtlasData actionSource sourceArrow) datum)
        == applyInsertion
          (mapAtlasData actionTarget
            (pageElementArrow
              (normalizeAtlasElement actionTarget
                (actionObject (normalizeAtlasElement actionSource (arrowSource sourceArrow))))
              (normalizeAtlasElement actionTarget
                (actionObject (normalizeAtlasElement actionSource (arrowTarget sourceArrow))))))
          (applyInsertion
            (actionComponent (normalizeAtlasElement actionSource (arrowSource sourceArrow))) datum)}
  , actionPageLaw :: sourceValue:SomePageElement sourceScope
      -> targetValue:SomePageElement sourceScope
      -> {(somePageElementPrecedes sourceValue targetValue
          && somePageElementTransported sourceValue targetValue)
        => (somePageElementPrecedes
              (mapPrimitiveElement actionWitness actionSource actionTarget actionObject sourceValue)
              (mapPrimitiveElement actionWitness actionSource actionTarget actionObject targetValue)
          && somePageElementTransported
              (mapPrimitiveElement actionWitness actionSource actionTarget actionObject sourceValue)
              (mapPrimitiveElement actionWitness actionSource actionTarget actionObject targetValue))}
  } @-}
data AtlasMorphismAction
  (objectMap :: Type)
  (sourceAtlasScope :: Type)
  (targetAtlasScope :: Type)
  (sourceScope :: Type)
  (targetScope :: Type)
  (sourceCellData :: Type -> Type)
  (targetCellData :: Type -> Type)
  sourceOrigin sourceFinal targetOrigin targetFinal = AtlasMorphismAction
  { actionWitness :: AtlasObjectMap objectMap
  , actionSource :: Atlas sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  , actionTarget :: Atlas targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  , actionObject :: forall sourceObject.
      PageElement sourceScope sourceObject
      -> PageElement targetScope (AtlasMappedObject objectMap sourceObject)
  , actionComponent :: forall sourceObject.
      PageElement sourceScope sourceObject
      -> DomanialInsertion
           (sourceCellData sourceObject)
           (targetCellData (AtlasMappedObject objectMap sourceObject))
  , actionNaturality :: forall sourceObject targetObject.
      PageElementArrow sourceScope sourceObject targetObject -> sourceCellData sourceObject -> ()
  , actionPageLaw :: SomePageElement sourceScope -> SomePageElement sourceScope -> ()
  }

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

{-@ reflect atlasMorphismSource @-}
atlasMorphismSource
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> Atlas sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
atlasMorphismSource (AtlasMorphismAction _ sourceAtlas _ _ _ _ _) = sourceAtlas

{-@ reflect atlasMorphismTarget @-}
atlasMorphismTarget
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> Atlas targetAtlasScope targetScope targetCellData targetOrigin targetFinal
atlasMorphismTarget (AtlasMorphismAction _ _ targetAtlas _ _ _ _) = targetAtlas

{-@ measure mapAtlasMorphismActionObject @-}
-- ALIGN: ATLAS-PRIMITIVE-OBJECT-VALIDITY.
{-@ mapAtlasMorphismActionObject :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> (forall object. source:PageElement ss object
          -> {target:PageElement ts (AtlasMappedObject m object) |
               MorphismCellValid (atlasMorphismSource action) source
                 => MorphismCellValid (atlasMorphismTarget action) target}) @-}
mapAtlasMorphismActionObject
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> (forall sourceObject. PageElement sourceScope sourceObject
      -> PageElement targetScope (AtlasMappedObject objectMap sourceObject))
mapAtlasMorphismActionObject (AtlasMorphismAction _ _ _ mapObject _ _ _) =
  mapObject

-- ALIGN: ATLAS-PRIMITIVE-DATA-INTERPRETATION.
{-@ measure mapAtlasMorphismActionComponent @-}
mapAtlasMorphismActionComponent
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> (forall sourceObject. PageElement sourceScope sourceObject
      -> DomanialInsertion
           (sourceCellData sourceObject)
           (targetCellData (AtlasMappedObject objectMap sourceObject)))
mapAtlasMorphismActionComponent
  (AtlasMorphismAction _ _ _ _ component _ _) = component

-- ALIGN: ATLAS-PRIMITIVE-PAGE-INTERPRETATION.
{-@ reflect mapAtlasMorphismActionElement @-}
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

{-@ reflect atlasMorphismObjectMapWitness @-}
atlasMorphismObjectMapWitness
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> AtlasObjectMap objectMap
atlasMorphismObjectMapWitness (AtlasMorphismAction witness _ _ _ _ _ _) = witness

-- ALIGN: ATLAS-PRIMITIVE-STORED-PAGE-LAW.
{-@ atlasMorphismActionPreservesArrow :: action:AtlasMorphismAction objectMap sa ta ss ts sd td so sf to tf
      -> sourceValue:SomePageElement ss -> targetValue:SomePageElement ss
      -> {(somePageElementPrecedes sourceValue targetValue
          && somePageElementTransported sourceValue targetValue)
        => (somePageElementPrecedes
              (mapPrimitiveElement (atlasMorphismObjectMapWitness action) (atlasMorphismSource action) (atlasMorphismTarget action) (mapAtlasMorphismActionObject action) sourceValue)
              (mapPrimitiveElement (atlasMorphismObjectMapWitness action) (atlasMorphismSource action) (atlasMorphismTarget action) (mapAtlasMorphismActionObject action) targetValue)
          && somePageElementTransported
              (mapPrimitiveElement (atlasMorphismObjectMapWitness action) (atlasMorphismSource action) (atlasMorphismTarget action) (mapAtlasMorphismActionObject action) sourceValue)
              (mapPrimitiveElement (atlasMorphismObjectMapWitness action) (atlasMorphismSource action) (atlasMorphismTarget action) (mapAtlasMorphismActionObject action) targetValue))} @-}
atlasMorphismActionPreservesArrow
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> SomePageElement sourceScope
  -> SomePageElement sourceScope
  -> ()
atlasMorphismActionPreservesArrow
  (AtlasMorphismAction _ _ _ _ _ _ preservesArrow) = preservesArrow

-- | Invoke the checked data-naturality equation retained by a primitive
-- morphism action. Derived functors use this witness after applying a
-- proof-transparent carrier wrapper.
-- ALIGN: ATLAS-PRIMITIVE-STORED-NATURALITY.
{-@ atlasMorphismActionNaturality :: action:AtlasMorphismAction objectMap sa ta ss ts sd td so sf to tf
      -> sourceArrow:PageElementArrow ss source target -> datum:sd source
      -> {applyInsertion
          ((mapAtlasMorphismActionComponent action) (normalizeAtlasElement (atlasMorphismSource action) (arrowTarget sourceArrow)))
          (applyInsertion (mapAtlasData (atlasMorphismSource action) sourceArrow) datum)
        == applyInsertion
          (mapAtlasData (atlasMorphismTarget action)
            (pageElementArrow
              (normalizeAtlasElement (atlasMorphismTarget action)
                ((mapAtlasMorphismActionObject action) (normalizeAtlasElement (atlasMorphismSource action) (arrowSource sourceArrow))))
              (normalizeAtlasElement (atlasMorphismTarget action)
                ((mapAtlasMorphismActionObject action) (normalizeAtlasElement (atlasMorphismSource action) (arrowTarget sourceArrow))))))
          (applyInsertion
            ((mapAtlasMorphismActionComponent action) (normalizeAtlasElement (atlasMorphismSource action) (arrowSource sourceArrow))) datum)} @-}
atlasMorphismActionNaturality
  :: AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
  -> PageElementArrow sourceScope sourceObject targetObject
  -> sourceCellData sourceObject
  -> ()
atlasMorphismActionNaturality
  (AtlasMorphismAction _ _ _ _ _ naturality _) = naturality

-- | Evaluate a proposed object callback at both normalized boundaries. Public
-- clients use this operation to certify its page law before assembling an action.
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
       source:PageElement sourceScope sourceObject
       -> {target:PageElement targetScope (AtlasMappedObject objectMap sourceObject) |
            MorphismCellValid sourceAtlas source => MorphismCellValid targetAtlas target})
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
  -> {action:AtlasMorphismAction
       objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
       sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal |
         atlasMorphismSource action == sourceAtlas
         && atlasMorphismTarget action == targetAtlas
         && atlasMorphismObjectMapWitness action == objectMapWitness
         && mapAtlasMorphismActionObject action == mapObject
         && mapAtlasMorphismActionComponent action == component}
@-}
-- ALIGN: ATLAS-PRIMITIVE-PAGE-FUNCTOR.
-- ALIGN: ATLAS-PRIMITIVE-NATURALITY.
-- ALIGN: ATLAS-PRIMITIVE-INTERPRETATION.
-- ALIGN: ATLAS-PRIMITIVE-ASSEMBLY-RETENTION.
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
  objectMapWitness sourceAtlas targetAtlas mapObject component pageLaw naturalityLaw =
    AtlasMorphismAction
      objectMapWitness
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

{-@ reflect normalizedActionObject @-}
-- ALIGN: ATLAS-NORMALIZED-OBJECT-VALIDITY.
{-@ normalizedActionObject :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> {target:PageElement ts (AtlasMappedObject m object) |
           MorphismCellValid (atlasMorphismSource action) source
             => MorphismCellValid (atlasMorphismTarget action) target} @-}
normalizedActionObject
  :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> PageElement ts (AtlasMappedObject m object)
normalizedActionObject action source =
  let sourceOwner = atlasMorphismSource action
      targetOwner = atlasMorphismTarget action
      normalizedSource = normalizeAtlasElement sourceOwner source
      mapped = mapAtlasMorphismActionObject action normalizedSource
      target = normalizeAtlasElement targetOwner mapped
      validity
        | Elements.pageElementTraceValid (atlasPageElements sourceOwner) source =
            normalizeAtlasElementTraceValid sourceOwner source `seq`
              normalizeAtlasElementTraceValid targetOwner mapped
        | otherwise = ()
  in retainObjectValidity sourceOwner targetOwner source target validity

-- | The certificate is checked statically and remains unevaluated at runtime.
{-@ reflect retainObjectValidity @-}
{-@ retainObjectValidity :: sourceOwner:Atlas sa ss sd so sf -> targetOwner:Atlas ta ts td to tf
      -> source:PageElement ss object -> target:PageElement ts mapped
      -> {proof:() | MorphismCellValid sourceOwner source => MorphismCellValid targetOwner target}
      -> {result:PageElement ts mapped | result == target
           && (MorphismCellValid sourceOwner source => MorphismCellValid targetOwner result)} @-}
retainObjectValidity :: Atlas sa ss sd so sf -> Atlas ta ts td to tf
  -> PageElement ss object -> PageElement ts mapped -> () -> PageElement ts mapped
retainObjectValidity _ _ _ target _ = target

{-@ reflect normalizedActionComponent @-}
normalizedActionComponent
  :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> DomanialInsertion (sd object) (td (AtlasMappedObject m object))
normalizedActionComponent action source =
  mapAtlasMorphismActionComponent action
    (normalizeAtlasElement (atlasMorphismSource action) source)

{-@ normalizedActionElementAgrees :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:SomePageElement ss
      -> {mapPrimitiveElement (atlasMorphismObjectMapWitness action)
            (atlasMorphismSource action) (atlasMorphismTarget action)
            (normalizedActionObject action) source
           == mapAtlasMorphismActionElement action source} @-}
normalizedActionElementAgrees :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> SomePageElement ss -> ()
normalizedActionElementAgrees action (SomePageElement source) =
  atlasCoherenceIdempotent (atlasMorphismSource action) source `seq`
    atlasCoherenceIdempotent (atlasMorphismTarget action)
      (mapAtlasMorphismActionObject action
        (normalizeAtlasElement (atlasMorphismSource action) source))

-- | Rebuild the action at normalized cells, retaining its owners and complete
-- dependent insertions. Both stored laws are checked for these new callbacks.
-- ALIGN: ATLAS-NORMALIZED-ACTION.
{-@ opaque-reflect normalizeAtlasMorphismAction @-}
{-@ normalizeAtlasMorphismAction :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> {result:AtlasMorphismAction m sa ta ss ts sd td so sf to tf |
           atlasMorphismSource result == atlasMorphismSource action
           && atlasMorphismTarget result == atlasMorphismTarget action
           && atlasMorphismObjectMapWitness result == atlasMorphismObjectMapWitness action
           && mapAtlasMorphismActionObject result == normalizedActionObject action
           && mapAtlasMorphismActionComponent result == normalizedActionComponent action} @-}
normalizeAtlasMorphismAction
  :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> AtlasMorphismAction m sa ta ss ts sd td so sf to tf
normalizeAtlasMorphismAction action =
  atlasMorphismAction (atlasMorphismObjectMapWitness action)
    (atlasMorphismSource action) (atlasMorphismTarget action)
    (normalizedActionObject action)
    (normalizedActionComponent action)
    (\source target ->
      normalizedActionElementAgrees action source `seq`
        normalizedActionElementAgrees action target `seq`
          atlasMorphismActionPreservesArrow action source target)
    (normalizedActionNaturality action)

-- | Observe normalization without exposing its implementation callbacks.
-- ALIGN: ATLAS-NORMALIZED-ACTION-RETENTION.
{-@ normalizeAtlasMorphismActionRetains :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> {mapAtlasMorphismActionObject (normalizeAtlasMorphismAction action) source
            == normalizeAtlasElement (atlasMorphismTarget action)
              (mapAtlasMorphismActionObject action
                (normalizeAtlasElement (atlasMorphismSource action) source))
          && mapAtlasMorphismActionComponent (normalizeAtlasMorphismAction action) source
            == mapAtlasMorphismActionComponent action
              (normalizeAtlasElement (atlasMorphismSource action) source)} @-}
normalizeAtlasMorphismActionRetains :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> ()
normalizeAtlasMorphismActionRetains action source =
  let normalized = normalizeAtlasMorphismAction action
  in mapAtlasMorphismActionObject normalized source `seq`
       normalizedActionObject action source `seq`
         mapAtlasMorphismActionComponent normalized source `seq`
           normalizedActionComponent action source `seq` ()

{-@ normalizedActionNaturality :: action:AtlasMorphismAction objectMap sa ta ss ts sd td so sf to tf
      -> sourceArrow:PageElementArrow ss source target -> datum:sd source
      -> {applyInsertion
          ((normalizedActionComponent action) (normalizeAtlasElement (atlasMorphismSource action) (arrowTarget sourceArrow)))
          (applyInsertion (mapAtlasData (atlasMorphismSource action) sourceArrow) datum)
        == applyInsertion
          (mapAtlasData (atlasMorphismTarget action)
            (pageElementArrow
              (normalizeAtlasElement (atlasMorphismTarget action)
                ((normalizedActionObject action) (normalizeAtlasElement (atlasMorphismSource action) (arrowSource sourceArrow))))
              (normalizeAtlasElement (atlasMorphismTarget action)
                ((normalizedActionObject action) (normalizeAtlasElement (atlasMorphismSource action) (arrowTarget sourceArrow))))))
          (applyInsertion
            ((normalizedActionComponent action) (normalizeAtlasElement (atlasMorphismSource action) (arrowSource sourceArrow))) datum)} @-}
normalizedActionNaturality :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElementArrow ss source target -> sd source -> ()
normalizedActionNaturality action arrow datum =
  atlasCoherenceIdempotent (atlasMorphismSource action) (arrowSource arrow) `seq`
    atlasCoherenceIdempotent (atlasMorphismSource action) (arrowTarget arrow) `seq`
      atlasCoherenceIdempotent (atlasMorphismTarget action)
        (mapAtlasMorphismActionObject action
          (normalizeAtlasElement (atlasMorphismSource action) (arrowSource arrow))) `seq`
        atlasCoherenceIdempotent (atlasMorphismTarget action)
          (mapAtlasMorphismActionObject action
            (normalizeAtlasElement (atlasMorphismSource action) (arrowTarget arrow))) `seq`
          atlasMorphismActionNaturality action arrow datum

-- | The raw identity callback preserves every field of the occurrence.
-- ALIGN: ATLAS-PRIMITIVE-IDENTITY-OBJECT.
{-@ reflect identityAtlasMorphismObject @-}
{-@ identityAtlasMorphismObject :: Atlas a s d o f -> source:PageElement s object
      -> {target:PageElement s (AtlasMappedObject IdentityAtlasObjectMap object) |
           pageElementPage target == pageElementPage source
           && pageElementPosition target == pageElementPosition source
           && pageElementTrace target == pageElementTrace source
           && pageElementCell target == pageElementCell source} @-}
identityAtlasMorphismObject :: Atlas a s d o f -> PageElement s object
  -> PageElement s (AtlasMappedObject IdentityAtlasObjectMap object)
identityAtlasMorphismObject _ source = source

-- | The normalized identity callback preserves page arrows and transport.
-- ALIGN: ATLAS-PRIMITIVE-IDENTITY-PAGE.
{-@ identityAtlasMorphismPreservesArrow :: witness:AtlasObjectMap IdentityAtlasObjectMap
      -> owner:Atlas a s d o f
      -> source:SomePageElement s
      -> target:{SomePageElement s | somePageElementPrecedes source target
           && somePageElementTransported source target}
      -> {somePageElementPrecedes
            (mapPrimitiveElement witness owner owner (identityAtlasMorphismObject owner) source)
            (mapPrimitiveElement witness owner owner (identityAtlasMorphismObject owner) target)
          && somePageElementTransported
            (mapPrimitiveElement witness owner owner (identityAtlasMorphismObject owner) source)
            (mapPrimitiveElement witness owner owner (identityAtlasMorphismObject owner) target)} @-}
identityAtlasMorphismPreservesArrow :: AtlasObjectMap IdentityAtlasObjectMap
  -> Atlas a s d o f -> SomePageElement s -> SomePageElement s -> ()
identityAtlasMorphismPreservesArrow _ owner source@(SomePageElement left) target@(SomePageElement right) =
  atlasCoherenceIdempotent owner left `seq`
    atlasCoherenceIdempotent owner right `seq`
      atlasNormalizationAgrees owner left `seq`
        atlasNormalizationAgrees owner right `seq`
          identityAtlasMorphismObject owner (normalizeAtlasElement owner left) `seq`
            identityAtlasMorphismObject owner (normalizeAtlasElement owner right) `seq`
              normalizeSomePageElementPreservesArrowAt (atlasCardinality owner - 1)
                (fromIntegral (atlasCardinality owner)) source target
