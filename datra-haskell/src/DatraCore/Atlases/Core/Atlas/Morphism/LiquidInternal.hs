{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ embed AtlasEquality * as TypeEquality @-}

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
  , identityAtlasMorphismAction
  , identityAtlasMorphismComponent
  , composeAtlasMorphismComponents
  , composeAtlasMorphismNaturality
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

import Atlas.Witness (atlasOwner, atlasWitnessData, atlasWitnessOwnerAgrees, atlasOwnersMembershipAgrees, atlasOwnersMapDataAgree)
import Atlas.Internal
import qualified PageElements as Elements (pageElementTraceValid)
import Data.Kind (Type)
import Data.Type.Equality ((:~:) (Refl))
import Atlas.Morphism.Equality.Internal (AtlasEquality (..))
import DomanialInsertion.Core
  ( DomanialInsertion (..), identityInsertionApply, composeInsertions, composeInsertionsApply
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

{-@ predicate MorphismSameCell X Y = pageElementPage X == pageElementPage Y && pageElementPosition X == pageElementPosition Y && pageElementTrace X == pageElementTrace Y && pageElementCell X == pageElementCell Y @-}

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
      source:PageElement sourceScope sourceObject
      -> DomanialInsertion
           ({datum:sourceCellData sourceObject | atlasAcceptsDatum actionSource source datum})
           ({datum:targetCellData (AtlasMappedObject objectMap sourceObject) |
                atlasAcceptsDatum actionTarget (actionObject source) datum})
  , actionNaturality :: forall sourceObject targetObject.
      sourceArrow:{PageElementArrow sourceScope sourceObject targetObject |
           MorphismCellValid actionSource (arrowSource sourceArrow)
           && MorphismCellValid actionSource (arrowTarget sourceArrow)}
      -> datum:{sourceCellData sourceObject | atlasAcceptsDatum actionSource (arrowSource sourceArrow) datum}
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
-- ALIGN: ATLAS-PRIMITIVE-COMPONENT-MEMBERSHIP.
{-@ measure mapAtlasMorphismActionComponent @-}
{-@ mapAtlasMorphismActionComponent :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> (forall object. source:PageElement ss object
          -> DomanialInsertion
               ({datum:sd object | atlasAcceptsDatum (atlasMorphismSource action) source datum})
               ({datum:td (AtlasMappedObject m object) |
                    atlasAcceptsDatum (atlasMorphismTarget action)
                      (mapAtlasMorphismActionObject action source) datum})) @-}
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
-- proof-transparent carrier wrapper, on valid owning arrows and accepted data.
-- ALIGN: ATLAS-PRIMITIVE-STORED-NATURALITY.
{-@ atlasMorphismActionNaturality :: action:AtlasMorphismAction objectMap sa ta ss ts sd td so sf to tf
      -> sourceArrow:{PageElementArrow ss source target |
           MorphismCellValid (atlasMorphismSource action) (arrowSource sourceArrow)
           && MorphismCellValid (atlasMorphismSource action) (arrowTarget sourceArrow)}
      -> datum:{sd source | atlasAcceptsDatum (atlasMorphismSource action) (arrowSource sourceArrow) datum}
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
       source:PageElement sourceScope sourceObject
       -> DomanialInsertion
            ({datum:sourceCellData sourceObject | atlasAcceptsDatum sourceAtlas source datum})
            ({datum:targetCellData (AtlasMappedObject objectMap sourceObject) |
                 atlasAcceptsDatum targetAtlas (mapObject source) datum}))
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
       sourceArrow:{PageElementArrow sourceScope sourceObject targetObject |
            MorphismCellValid sourceAtlas (arrowSource sourceArrow)
            && MorphismCellValid sourceAtlas (arrowTarget sourceArrow)}
       -> datum:{sourceCellData sourceObject | atlasAcceptsDatum sourceAtlas (arrowSource sourceArrow) datum}
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
{-@ normalizedActionComponent :: action:AtlasMorphismAction m sa ta ss ts sd td so sf to tf
      -> source:PageElement ss object
      -> DomanialInsertion
           ({datum:sd object | atlasAcceptsDatum (atlasMorphismSource action) source datum})
           ({datum:td (AtlasMappedObject m object) |
                atlasAcceptsDatum (atlasMorphismTarget action) (normalizedActionObject action source) datum}) @-}
normalizedActionComponent
  :: AtlasMorphismAction m sa ta ss ts sd td so sf to tf
  -> PageElement ss object -> DomanialInsertion (sd object) (td (AtlasMappedObject m object))
normalizedActionComponent action source =
  atlasCoherenceIdempotent (atlasMorphismSource action) source `seq`
    atlasCoherenceIdempotent (atlasMorphismTarget action)
      (mapAtlasMorphismActionObject action
        (normalizeAtlasElement (atlasMorphismSource action) source)) `seq`
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
      -> sourceArrow:{PageElementArrow ss source target |
           MorphismCellValid (atlasMorphismSource action) (arrowSource sourceArrow)
           && MorphismCellValid (atlasMorphismSource action) (arrowTarget sourceArrow)}
      -> datum:{sd source | atlasAcceptsDatum (atlasMorphismSource action) (arrowSource sourceArrow) datum}
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
           MorphismSameCell target source} @-}
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

-- | Assemble the coherent identity using the owning accepted data carrier.
-- ALIGN: ATLAS-PRIMITIVE-IDENTITY-ACTION.
{-@ opaque-reflect identityAtlasMorphismAction @-}
{-@ identityAtlasMorphismAction :: owner:Atlas a s d o f
      -> {action:AtlasMorphismAction IdentityAtlasObjectMap a a s s d d o f o f |
           atlasMorphismSource action == owner
           && atlasMorphismTarget action == owner
           && mapAtlasMorphismActionObject action == identityAtlasMorphismObject owner
           && mapAtlasMorphismActionComponent action == identityAtlasMorphismComponent owner} @-}
identityAtlasMorphismAction :: Atlas a s d o f
  -> AtlasMorphismAction IdentityAtlasObjectMap a a s s d d o f o f
identityAtlasMorphismAction owner =
  atlasMorphismAction identityAtlasObjectMap owner owner
    (identityAtlasMorphismObject owner)
    (identityAtlasMorphismComponent owner)
    (identityAtlasMorphismPreservesArrow identityAtlasObjectMap owner)
    (identityAtlasMorphismNaturality owner)

-- ALIGN: ATLAS-PRIMITIVE-IDENTITY-COMPONENT.
{-@ reflect identityAtlasMorphismComponent @-}
{-@ identityAtlasMorphismComponent :: owner:Atlas a s d o f
      -> source:PageElement s object
      -> DomanialInsertion
           ({datum:d object | atlasAcceptsDatum owner source datum})
           ({datum:d (AtlasMappedObject IdentityAtlasObjectMap object) |
              atlasAcceptsDatum owner (identityAtlasMorphismObject owner source) datum}) @-}
identityAtlasMorphismComponent :: forall a s d o f object. Atlas a s d o f -> PageElement s object
  -> DomanialInsertion (d object) (d (AtlasMappedObject IdentityAtlasObjectMap object))
identityAtlasMorphismComponent owner source =
  coherentInsertionAt @object @(AtlasMappedObject IdentityAtlasObjectMap object)
    (AtlasEquality Refl) owner source (identityAtlasMorphismObject owner source)

{-@ identityAtlasMorphismNaturality :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           MorphismCellValid owner (arrowSource arrow)
           && MorphismCellValid owner (arrowTarget arrow)}
      -> datum:{d source | atlasAcceptsDatum owner (arrowSource arrow) datum}
      -> {applyInsertion
            (identityAtlasMorphismComponent owner (normalizeAtlasElement owner (arrowTarget arrow)))
            (applyInsertion (mapAtlasData owner arrow) datum)
          == applyInsertion
            (mapAtlasData owner
              (pageElementArrow
                (normalizeAtlasElement owner (identityAtlasMorphismObject owner
                  (normalizeAtlasElement owner (arrowSource arrow))))
                (normalizeAtlasElement owner (identityAtlasMorphismObject owner
                  (normalizeAtlasElement owner (arrowTarget arrow))))))
            (applyInsertion
              (identityAtlasMorphismComponent owner (normalizeAtlasElement owner (arrowSource arrow))) datum)} @-}
identityAtlasMorphismNaturality :: forall a s d o f source target. Atlas a s d o f
  -> PageElementArrow s source target -> d source -> ()
identityAtlasMorphismNaturality owner arrow datum =
  coherentInsertionNaturalityAt @source @target
    @(AtlasMappedObject IdentityAtlasObjectMap source) @(AtlasMappedObject IdentityAtlasObjectMap target)
    (AtlasEquality Refl) (AtlasEquality Refl) owner arrow
    (identityAtlasMorphismObject owner (normalizeAtlasElement owner (arrowSource arrow)))
    (identityAtlasMorphismObject owner (normalizeAtlasElement owner (arrowTarget arrow)))
    datum

-- | Transport coherence along a genuine type equality and an unchanged cell.
-- ALIGN: ATLAS-COHERENT-INSERTION-TRANSPORT.
{-@ reflect coherentInsertionAt @-}
{-@ coherentInsertionAt :: AtlasEquality source target
      -> owner:Atlas a s d o f -> element:PageElement s source
      -> selected:{PageElement s target |
           MorphismSameCell selected element}
      -> DomanialInsertion
          ({datum:d source | atlasAcceptsDatum owner element datum})
          ({datum:d target | atlasAcceptsDatum owner selected datum}) @-}
coherentInsertionAt :: forall source target a s d o f. AtlasEquality source target
  -> Atlas a s d o f -> PageElement s source -> PageElement s target
  -> DomanialInsertion (d source) (d target)
coherentInsertionAt equality owner element _ =
  case coherencePacket @source @target equality owner element of
    CoherentInsertion _ _ _ insertion -> insertion

{-@ type CoherenceLaw a s d o f source target mappedSource mappedTarget =
      sourceEquality:AtlasEquality source mappedSource
      -> targetEquality:AtlasEquality target mappedTarget
      -> owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           MorphismCellValid owner (arrowSource arrow)
           && MorphismCellValid owner (arrowTarget arrow)}
      -> sourceMapped:{PageElement s mappedSource |
           MorphismSameCell sourceMapped (normalizeAtlasElement owner (arrowSource arrow))}
      -> targetMapped:{PageElement s mappedTarget |
           MorphismSameCell targetMapped (normalizeAtlasElement owner (arrowTarget arrow))}
      -> datum:{d source | atlasAcceptsDatum owner (arrowSource arrow) datum}
      -> {applyInsertion
            (coherentInsertionAt targetEquality owner (normalizeAtlasElement owner (arrowTarget arrow)) targetMapped)
            (applyInsertion (mapAtlasData owner arrow) datum)
          == applyInsertion
            (mapAtlasData owner
              (pageElementArrow (normalizeAtlasElement owner sourceMapped) (normalizeAtlasElement owner targetMapped)))
            (applyInsertion
              (coherentInsertionAt sourceEquality owner (normalizeAtlasElement owner (arrowSource arrow)) sourceMapped) datum)} @-}

-- ALIGN: ATLAS-COHERENT-INSERTION-NATURALITY.
{-@ coherentInsertionNaturalityAt :: CoherenceLaw a s d o f source target mappedSource mappedTarget @-}
coherentInsertionNaturalityAt
  :: forall source target mappedSource mappedTarget a s d o f.
     AtlasEquality source mappedSource -> AtlasEquality target mappedTarget
  -> Atlas a s d o f -> PageElementArrow s source target
  -> PageElement s mappedSource -> PageElement s mappedTarget -> d source -> ()
coherentInsertionNaturalityAt sourceEquality targetEquality owner arrow sourceMapped targetMapped datum =
  case coherenceNaturalityPacket @a @s @d @o @f @source @target @mappedSource @mappedTarget
      sourceEquality targetEquality of
    CoherenceNaturality law -> law sourceEquality targetEquality owner arrow sourceMapped targetMapped datum

{-@ rawCoherentNaturalityAt :: CoherenceLaw a s d o f source target source target @-}
rawCoherentNaturalityAt
  :: forall source target a s d o f.
     AtlasEquality source source -> AtlasEquality target target
  -> Atlas a s d o f -> PageElementArrow s source target
  -> PageElement s source -> PageElement s target -> d source -> ()
rawCoherentNaturalityAt sourceEquality@(AtlasEquality Refl) targetEquality@(AtlasEquality Refl) owner arrow sourceMapped targetMapped datum =
  coherencePacket @source @source (AtlasEquality Refl) owner (normalizeAtlasElement owner (arrowSource arrow)) `seq`
    coherencePacket @target @target (AtlasEquality Refl) owner (normalizeAtlasElement owner (arrowTarget arrow)) `seq`
      atlasCoherenceIdempotent owner (arrowSource arrow) `seq`
        atlasCoherenceIdempotent owner (arrowTarget arrow) `seq`
          atlasArrowNormalizationAgrees owner arrow `seq`
            mapAtlasDataNormalized owner arrow `seq`
              coherentInsertionAt @source @source sourceEquality owner (normalizeAtlasElement owner (arrowSource arrow)) sourceMapped `seq`
                coherentInsertionAt @target @target targetEquality owner (normalizeAtlasElement owner (arrowTarget arrow)) targetMapped `seq`
                  identityInsertionApply datum `seq`
                    identityInsertionApply (applyInsertion (mapAtlasData owner arrow) datum)

-- | Check the law at identical cell indices before transporting the entire
-- certificate. Its field retains the law when hidden carrier indices change.
{-@ data CoherenceNaturality a s d o f source target mappedSource mappedTarget = CoherenceNaturality
  { coherenceNaturalityLaw :: CoherenceLaw a s d o f source target mappedSource mappedTarget }
  @-}
data CoherenceNaturality a s d o f source target mappedSource mappedTarget = CoherenceNaturality
  { coherenceNaturalityLaw :: AtlasEquality source mappedSource -> AtlasEquality target mappedTarget
      -> Atlas a s d o f -> PageElementArrow s source target
      -> PageElement s mappedSource -> PageElement s mappedTarget -> d source -> () }

coherenceNaturalityPacket :: forall a s d o f source target mappedSource mappedTarget.
  AtlasEquality source mappedSource -> AtlasEquality target mappedTarget
  -> CoherenceNaturality a s d o f source target mappedSource mappedTarget
coherenceNaturalityPacket (AtlasEquality Refl) (AtlasEquality Refl) =
  (CoherenceNaturality rawCoherentNaturalityAt
    :: CoherenceNaturality a s d o f source target source target)

-- | Keep the insertion with its owner and selected cells so that a nominal
-- type-equality conversion preserves both accepted-data predicates.
{-@ data CoherentInsertion a s d o f source target = CoherentInsertion
  { coherentOwner :: Atlas a s d o f
  , coherentSource :: PageElement s source
  , coherentTarget :: PageElement s target
  , coherentMapping :: DomanialInsertion
      ({datum:d source | atlasAcceptsDatum coherentOwner coherentSource datum})
      ({datum:d target | atlasAcceptsDatum coherentOwner coherentTarget datum})
  } @-}
data CoherentInsertion a s d o f source target = CoherentInsertion
  { coherentOwner :: Atlas a s d o f
  , coherentSource :: PageElement s source
  , coherentTarget :: PageElement s target
  , coherentMapping :: DomanialInsertion (d source) (d target)
  }

{-@ reflect coherencePacket @-}
{-@ coherencePacket :: AtlasEquality source target -> owner:Atlas a s d o f
      -> element:PageElement s source
      -> {packet:CoherentInsertion a s d o f source target |
           coherentOwner packet == owner
           && coherentSource packet == element
           && MorphismSameCell (coherentTarget packet) element} @-}
coherencePacket :: forall source target a s d o f. AtlasEquality source target
  -> Atlas a s d o f -> PageElement s source -> CoherentInsertion a s d o f source target
coherencePacket (AtlasEquality Refl) owner element =
  (CoherentInsertion owner element element (atlasDataCoherence owner element)
    :: CoherentInsertion a s d o f source source)

-- | Compose accepted components at the normalized middle occurrence, retaining
-- the actual intermediate owner rather than only its nominal scope.
-- ALIGN: ATLAS-COMPOSITE-COMPONENT.
{-@ opaque-reflect composeAtlasMorphismComponents @-}
{-@ composeAtlasMorphismComponents :: second:AtlasMorphismAction n ma ta ms ts md td mo mf to tf
      -> first:{AtlasMorphismAction m sa ma ss ms sd md so sf mo2 mf2 |
           atlasOwner (atlasMorphismTarget first) == atlasOwner (atlasMorphismSource second)}
      -> source:PageElement ss object
      -> {result:DomanialInsertion
           ({datum:sd object | atlasAcceptsDatum (atlasMorphismSource first) source datum})
           ({datum:td (AtlasMappedObject n (AtlasMappedObject m object)) |
              atlasAcceptsDatum (atlasMorphismTarget second)
                (mapAtlasMorphismActionObject second
                  (normalizeAtlasElement (atlasMorphismSource second)
                    (normalizeAtlasElement (atlasMorphismTarget first)
                      (mapAtlasMorphismActionObject first source)))) datum}) |
           result == composeInsertions
             (mapAtlasMorphismActionComponent second
               (normalizeAtlasElement (atlasMorphismSource second)
                 (normalizeAtlasElement (atlasMorphismTarget first)
                   (mapAtlasMorphismActionObject first source))))
             (mapAtlasMorphismActionComponent first source)} @-}
composeAtlasMorphismComponents
  :: AtlasMorphismAction n ma ta ms ts md td mo mf to tf
  -> AtlasMorphismAction m sa ma ss ms sd md so sf mo2 mf2
  -> PageElement ss object
  -> DomanialInsertion (sd object) (td (AtlasMappedObject n (AtlasMappedObject m object)))
composeAtlasMorphismComponents second first source =
  let targetFirst = atlasMorphismTarget first
      sourceSecond = atlasMorphismSource second
      rawMiddle = mapAtlasMorphismActionObject first source
      witness = atlasWitnessData targetFirst
      middle = normalizeAtlasElement sourceSecond (normalizeAtlasElement targetFirst rawMiddle)
  in atlasWitnessOwnerAgrees witness targetFirst rawMiddle `seq`
    atlasWitnessOwnerAgrees witness sourceSecond rawMiddle `seq`
    atlasOwnersMembershipAgrees targetFirst sourceSecond rawMiddle `seq`
    atlasCoherenceIdempotent targetFirst rawMiddle `seq`
    atlasCoherenceIdempotent sourceSecond rawMiddle `seq`
      composeInsertions (mapAtlasMorphismActionComponent second middle)
        (mapAtlasMorphismActionComponent first source)

-- | The composite component commutes with owning data transport. The middle
-- insertion agrees in full across the retained owner equality.
-- ALIGN: ATLAS-COMPOSITE-NATURALITY.
{-@ composeAtlasMorphismNaturality :: second:AtlasMorphismAction n ma ta ms ts md td mo mf to tf
      -> first:{AtlasMorphismAction m sa ma ss ms sd md so sf mo2 mf2 |
           atlasOwner (atlasMorphismTarget first) == atlasOwner (atlasMorphismSource second)}
      -> arrow:{PageElementArrow ss source target |
           MorphismCellValid (atlasMorphismSource first) (arrowSource arrow)
           && MorphismCellValid (atlasMorphismSource first) (arrowTarget arrow)}
      -> datum:{sd source | atlasAcceptsDatum (atlasMorphismSource first) (arrowSource arrow) datum}
      -> {applyInsertion
            (composeAtlasMorphismComponents second first (normalizeAtlasElement (atlasMorphismSource first) (arrowTarget arrow)))
            (applyInsertion (mapAtlasData (atlasMorphismSource first) arrow) datum)
          == applyInsertion
            (mapAtlasData (atlasMorphismTarget second)
              (pageElementArrow (normalizeAtlasElement (atlasMorphismTarget second) (mapAtlasMorphismActionObject second (normalizeAtlasElement (atlasMorphismSource second) (normalizeAtlasElement (atlasMorphismTarget first) (mapAtlasMorphismActionObject first (normalizeAtlasElement (atlasMorphismSource first) (arrowSource arrow))))))) (normalizeAtlasElement (atlasMorphismTarget second) (mapAtlasMorphismActionObject second (normalizeAtlasElement (atlasMorphismSource second) (normalizeAtlasElement (atlasMorphismTarget first) (mapAtlasMorphismActionObject first (normalizeAtlasElement (atlasMorphismSource first) (arrowTarget arrow)))))))))
            (applyInsertion
              (composeAtlasMorphismComponents second first (normalizeAtlasElement (atlasMorphismSource first) (arrowSource arrow))) datum)} @-}
composeAtlasMorphismNaturality
  :: AtlasMorphismAction n ma ta ms ts md td mo mf to tf
  -> AtlasMorphismAction m sa ma ss ms sd md so sf mo2 mf2
  -> PageElementArrow ss source target -> sd source -> ()

composeAtlasMorphismNaturality second first arrow datum =
  let sourceOwner = atlasMorphismSource first
      targetFirst = atlasMorphismTarget first
      sourceSecond = atlasMorphismSource second
      source = normalizeAtlasElement sourceOwner (arrowSource arrow)
      target = normalizeAtlasElement sourceOwner (arrowTarget arrow)
      rawMiddleSource = mapAtlasMorphismActionObject first source
      rawMiddleTarget = mapAtlasMorphismActionObject first target
      middleSource = normalizedActionObject first (arrowSource arrow)
      middleTarget = normalizedActionObject first (arrowTarget arrow)
      witness = atlasWitnessData targetFirst
      targetDatum = applyInsertion (mapAtlasData sourceOwner arrow) datum
      secondSource = normalizeAtlasElement sourceSecond middleSource
      secondTarget = normalizeAtlasElement sourceSecond middleTarget
  in normalizeAtlasElementTraceValid sourceOwner (arrowSource arrow) `seq`
    normalizeAtlasElementTraceValid sourceOwner (arrowTarget arrow) `seq`
    atlasAcceptsDatumNormalized sourceOwner (arrowSource arrow) datum `seq`
    atlasAcceptsDatumNormalized sourceOwner (arrowTarget arrow) targetDatum `seq`
    atlasMorphismActionPreservesArrow first (SomePageElement (arrowSource arrow)) (SomePageElement (arrowTarget arrow)) `seq`
    let middleArrow = pageElementArrow middleSource middleTarget
        middleDatum = applyInsertion (mapAtlasMorphismActionComponent first source) datum
    in atlasWitnessOwnerAgrees witness targetFirst middleSource `seq`
    atlasWitnessOwnerAgrees witness targetFirst middleTarget `seq`
    atlasWitnessOwnerAgrees witness sourceSecond middleSource `seq`
    atlasWitnessOwnerAgrees witness sourceSecond middleTarget `seq`
    atlasOwnersMembershipAgrees targetFirst sourceSecond middleSource `seq`
    atlasOwnersMembershipAgrees targetFirst sourceSecond middleTarget `seq`
    atlasCoherenceIdempotent targetFirst rawMiddleSource `seq`
    atlasCoherenceIdempotent targetFirst rawMiddleTarget `seq`
    atlasCoherenceIdempotent sourceSecond middleSource `seq`
    atlasCoherenceIdempotent sourceSecond middleTarget `seq`
    atlasMorphismActionNaturality first arrow datum `seq`
    atlasOwnersMapDataAgree targetFirst sourceSecond middleArrow `seq`
    atlasMorphismActionNaturality second middleArrow middleDatum `seq`
    composeAtlasMorphismComponents second first source `seq`
    composeAtlasMorphismComponents second first target `seq`
    composeInsertionsApply (mapAtlasMorphismActionComponent second secondSource)
      (mapAtlasMorphismActionComponent first source) datum `seq`
    composeInsertionsApply (mapAtlasMorphismActionComponent second secondTarget)
      (mapAtlasMorphismActionComponent first target) targetDatum
