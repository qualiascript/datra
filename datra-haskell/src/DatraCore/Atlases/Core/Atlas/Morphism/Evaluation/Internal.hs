{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Evaluate materialized Atlas syntax into dependent object and data actions.
module Atlas.Morphism.Evaluation.Internal
  ( withAtlasMorphismAction, atlasMorphismPagination, mapAtlasMorphismElement
  , mapAtlasMorphismArrow, mapAtlasMorphismData, atlasHomPagination
  , mapAtlasHomElement, mapAtlasHomArrow, mapAtlasHomData
  ) where

import Atlas.Witness
  (AtlasObjectPaginationScope, AtlasObjectCellData, AtlasWitness)
import Atlas.Internal
  ( atlasCoherence
  , normalizeAtlasElement
  )
import Atlas.Morphism
  ( AtlasMorphismAction
  , AtlasMappedObject
  , identityAtlasMorphismAction
  , composeAtlasMorphismComponents
  , atlasObjectMap
  , atlasMorphismAction
  , composeAtlasMorphismNaturality
  , atlasMorphismActionPreservesArrow
  , atlasMorphismSource
  , atlasMorphismTarget
  , mapAtlasMorphismActionComponent
  , mapAtlasMorphismActionElement
  , mapAtlasMorphismActionObject
  , normalizedActionObject
  )
import Control.Category (Category (..))
import Atlas.Morphism.Internal
  ( AtlasMorphism (..), AtlasMorphismImage (..), AtlasHom
  , withAtlasMorphismImage, materializeAtlasHom )
import DomanialInsertion
  ( composeInsertions
  , identityInsertion
  )
import PageElements.Structure
  ( PageElement
  , PageElementArrow
  )
import PageElements.Structure (SomePageElement (..))
import Pagination
  ( PaginationMorphism
  , SomePageElementArrow
  , composePaginationMorphisms
  , mapPaginationArrow
  , paginationMorphism
  )
import Prelude hiding ((.), id)

-- | The object identity of a complete composite retains both component
-- symbols. Normalization preserves these phantom identities.
data CompositeAtlasObjectMap first second

type instance AtlasMappedObject (CompositeAtlasObjectMap first second) source =
  AtlasMappedObject second (AtlasMappedObject first source)

composeAtlasMorphismActions
  :: AtlasMorphismAction second middleAtlasScope targetAtlasScope middleScope targetScope
       middleCellData targetCellData middleOrigin middleFinal targetOrigin targetFinal
  -> AtlasMorphismAction first sourceAtlasScope middleAtlasScope sourceScope middleScope
       sourceCellData middleCellData sourceOrigin sourceFinal middleOrigin' middleFinal'
  -> AtlasMorphismAction (CompositeAtlasObjectMap first second)
       sourceAtlasScope targetAtlasScope sourceScope targetScope sourceCellData targetCellData
       sourceOrigin sourceFinal targetOrigin targetFinal
composeAtlasMorphismActions second first =
  atlasMorphismAction atlasObjectMap
    (atlasMorphismSource first) (atlasMorphismTarget second)
    (\source -> mapAtlasMorphismActionObject second
      (normalizeAtlasElement (atlasMorphismSource second)
        (normalizeAtlasElement (atlasMorphismTarget first) (mapAtlasMorphismActionObject first source))))
    (composeAtlasMorphismComponents second first)
    (\source target ->
      atlasMorphismActionPreservesArrow first source target `seq`
        atlasMorphismActionPreservesArrow second
          (mapAtlasMorphismActionElement first source)
          (mapAtlasMorphismActionElement first target))
    (composeAtlasMorphismNaturality second first)

-- | Expose one action for the complete morphism, preserving its normalized
-- object map and composed data insertion. Restrictions such as Charter must
-- be applied here: intermediate factors need not preserve the restricted data.
-- ALIGN: ATLAS-COMPLETE-ACTION.
withAtlasMorphismAction
  :: AtlasMorphism sourceAtlasScope targetAtlasScope sourceScope targetScope sourceCellData targetCellData
  -> (forall objectMap sourceOrigin sourceFinal targetOrigin targetFinal.
        AtlasMorphismAction objectMap sourceAtlasScope targetAtlasScope sourceScope targetScope
          sourceCellData targetCellData sourceOrigin sourceFinal targetOrigin targetFinal
        -> result)
  -> result
withAtlasMorphismAction (PrimitiveAtlasMorphism action) useAction = useAction action
withAtlasMorphismAction (IdentityAtlasMorphism valueAtlas) useAction =
  useAction (identityAtlasMorphismAction valueAtlas)
withAtlasMorphismAction (CompositeAtlasMorphism second first) useAction =
  withAtlasMorphismAction first $ \firstAction ->
    withAtlasMorphismAction second $ \secondAction ->
      useAction (composeAtlasMorphismActions secondAction firstAction)

-- | Apply an Atlas morphism to a cell and its attached data carrier.
-- Primitive maps normalize at both boundaries. Identity is coherence;
-- composition recursively inserts the middle object's coherence.
-- ALIGN: ATLAS-MATERIALIZED-DATA-INTERPRETATION.
mapAtlasMorphismData
  :: AtlasMorphism
       sourceAtlasScope targetAtlasScope
       sourceScope targetScope sourceCellData targetCellData
  -> PageElement sourceScope sourceObject
  -> AtlasMorphismImage
       targetScope sourceCellData targetCellData sourceObject
mapAtlasMorphismData (PrimitiveAtlasMorphism action) source =
  let sourceAtlas = atlasMorphismSource action
      normalizedSource = normalizeAtlasElement sourceAtlas source
  in AtlasMorphismImage
      (normalizedActionObject action source)
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
-- ALIGN: ATLAS-MATERIALIZED-OBJECT-INTERPRETATION.
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
-- ALIGN: ATLAS-SYMBOLIC-OBJECT-INTERPRETATION.
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
-- ALIGN: ATLASHOM-DATA-INTERPRETATION.
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
