{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
-- GHC does not count names referenced only by LiquidHaskell specifications.
{-# OPTIONS_GHC -Wno-unused-imports #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | Hidden implementation of Atlas transversals using Atlas coverage evidence.
module AtlasTransversal.Internal
  ( AtlasTransversal
  , atlasTransversal
  , atlasTransversalOrderedTransposal
  , atlasTransversalTransposal
  , atlasTransversalHom
  , atlasTransversalPreservesCoverage
  , mapAtlasTransversalCoveredDatum
  , identityAtlasTransversal
  , composeAtlasTransversals
  , mapAtlasTransversalObject
  , atlasTransversalPreimage
  , atlasTransversalLeftInverse
  , atlasTransversalPreservesOrder
  , atlasTransversalPagination
  , mapAtlasTransversalElement
  , mapAtlasTransversalArrow
  , mapAtlasTransversalData
  ) where

import Atlas
  ( Atlas
  , AtlasHom
  , AtlasMorphismImage
  , AtlasObject
  , AtlasObjectCellData
  , AtlasObjectPaginationScope
  , AtlasWitness
  , atlasWitness
  , withAtlasMorphismImage
  )
import AtlasCovered.Internal
  ( AtlasCoveredDatum (..)
  , AtlasCoverageWitness
  , coverageWitnessCovers
  )
import AtlasTransposal (AtlasTransposal, AtlasTransposalElement)
import Control.Category (Category (..))
import DomanialInsertion (applyInsertion)
import OrderedAtlasTransposal
  ( OrderedAtlasTransposal
  , composeOrderedAtlasTransposals
  , identityOrderedAtlasTransposal
  , mapOrderedAtlasTransposalArrow
  , mapOrderedAtlasTransposalData
  , mapOrderedAtlasTransposalElement
  , mapOrderedAtlasTransposalObject
  , orderedAtlasTransposalHom
  , orderedAtlasTransposalLeftInverse
  , orderedAtlasTransposalPagination
  , orderedAtlasTransposalPreimage
  , orderedAtlasTransposalPreservesOrder
  , orderedAtlasTransposalTransposal
  )
import PageElements
  ( PageElement
  , PageElementArrow
  , SomePageElement
  )
import Pagination (PaginationMorphism, SomePageElementArrow)
import Prelude hiding ((.), id)

-- | A transversal is an ordered transposal whose data action maps every covered
-- source datum to coverage evidence for its exact target image. Primitive
-- arrows retain source and target Atlases so this condition can be checked;
-- identities and composites derive it structurally.
type role AtlasTransversal nominal nominal
data AtlasTransversal source target where
  PrimitiveAtlasTransversal
    :: Atlas
         sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
    -> Atlas
         targetAtlasScope targetScope targetCellData targetOrigin targetFinal
    -> OrderedAtlasTransposal
         (AtlasObject sourceAtlasScope sourceScope sourceCellData)
         (AtlasObject targetAtlasScope targetScope targetCellData)
    -> (forall targetObject.
         AtlasCoveredDatum
           (AtlasObject sourceAtlasScope sourceScope sourceCellData)
         -> PageElement targetScope targetObject
         -> targetCellData targetObject
         -> AtlasCoverageWitness
              (AtlasObject targetAtlasScope targetScope targetCellData))
    -> AtlasTransversal
         (AtlasObject sourceAtlasScope sourceScope sourceCellData)
         (AtlasObject targetAtlasScope targetScope targetCellData)
  IdentityAtlasTransversal
    :: AtlasTransversal object object
  CompositeAtlasTransversal
    :: AtlasTransversal middle target
    -> AtlasTransversal source middle
    -> AtlasTransversal source target

-- | Add the covered-data clause to an ordered Atlas transposal.
--
-- The callback receives a covered source datum followed by the exact target
-- element and datum computed by the underlying Atlas morphism. Its result is
-- statically required to witness coverage of those exact values.
{-@
atlasTransversal
  :: sourceAtlas:Atlas
       sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> targetAtlas:Atlas
       targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> ordered:OrderedAtlasTransposal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> preservesCoverage:(forall targetObject.
       AtlasCoveredDatum
         (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       -> targetOccurrence:PageElement targetScope targetObject
       -> targetDatum:targetCellData targetObject
       -> { witness:AtlasCoverageWitness
              (AtlasObject targetAtlasScope targetScope targetCellData) |
            coverageWitnessCovers
              targetAtlas targetOccurrence targetDatum witness })
  -> AtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
@-}
atlasTransversal
  :: Atlas
       sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> Atlas
       targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> OrderedAtlasTransposal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> (forall targetObject.
       AtlasCoveredDatum
         (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       -> PageElement targetScope targetObject
       -> targetCellData targetObject
       -> AtlasCoverageWitness
            (AtlasObject targetAtlasScope targetScope targetCellData))
  -> AtlasTransversal
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
atlasTransversal = PrimitiveAtlasTransversal

-- | Forget the coverage condition while retaining injectivity and order.
atlasTransversalOrderedTransposal
  :: AtlasTransversal source target
  -> OrderedAtlasTransposal source target
atlasTransversalOrderedTransposal
  (PrimitiveAtlasTransversal _ _ ordered _) = ordered
atlasTransversalOrderedTransposal IdentityAtlasTransversal =
  identityOrderedAtlasTransposal
atlasTransversalOrderedTransposal
  (CompositeAtlasTransversal second first) =
    composeOrderedAtlasTransposals
      (atlasTransversalOrderedTransposal second)
      (atlasTransversalOrderedTransposal first)

-- | Include a transversal into the category of Atlas transposals.
atlasTransversalTransposal
  :: AtlasTransversal source target
  -> AtlasTransposal source target
atlasTransversalTransposal =
  orderedAtlasTransposalTransposal . atlasTransversalOrderedTransposal

-- | Include a transversal all the way into the Atlas category.
atlasTransversalHom
  :: AtlasTransversal source target
  -> AtlasHom source target
atlasTransversalHom =
  orderedAtlasTransposalHom . atlasTransversalOrderedTransposal

-- | Map a covered datum and derive coverage of its exact target image. This
-- is total: malformed preservation callbacks are rejected when the primitive
-- transversal is compiled, rather than producing a runtime failure here.
mapAtlasTransversalCoveredDatum
  :: AtlasTransversal source target
  -> AtlasCoveredDatum source
  -> AtlasCoveredDatum target
mapAtlasTransversalCoveredDatum IdentityAtlasTransversal covered =
  covered
mapAtlasTransversalCoveredDatum
  (CompositeAtlasTransversal second first)
  covered =
    mapAtlasTransversalCoveredDatum second
      (mapAtlasTransversalCoveredDatum first covered)
mapAtlasTransversalCoveredDatum
  (PrimitiveAtlasTransversal sourceAtlas _ ordered preservesCoverage)
  covered@(AtlasCoveredDatum sourceOccurrence sourceDatum _) =
    withAtlasMorphismImage
      (mapOrderedAtlasTransposalData
        (atlasWitness sourceAtlas)
        ordered
        sourceOccurrence) $ \targetOccurrence insertion ->
          let targetDatum = applyInsertion insertion sourceDatum
          in AtlasCoveredDatum
              targetOccurrence
              targetDatum
              (preservesCoverage covered targetOccurrence targetDatum)

-- | The covered-data preservation condition of an Atlas transversal.
-- This is named separately from the operational mapper so downstream
-- restrictions can refer directly to the condition they inherit.
atlasTransversalPreservesCoverage
  :: AtlasTransversal source target
  -> AtlasCoveredDatum source
  -> AtlasCoveredDatum target
atlasTransversalPreservesCoverage = mapAtlasTransversalCoveredDatum

-- | The identity transversal preserves every covered datum unchanged.
identityAtlasTransversal :: AtlasTransversal object object
identityAtlasTransversal = IdentityAtlasTransversal

-- | Compose Atlas transversals in categorical order.
composeAtlasTransversals
  :: AtlasTransversal middle target
  -> AtlasTransversal source middle
  -> AtlasTransversal source target
composeAtlasTransversals IdentityAtlasTransversal first = first
composeAtlasTransversals second IdentityAtlasTransversal = second
composeAtlasTransversals second (CompositeAtlasTransversal middle first) =
  CompositeAtlasTransversal (composeAtlasTransversals second middle) first
composeAtlasTransversals second first =
  CompositeAtlasTransversal second first

-- | Atlas transversals form the next wide subcategory in the restriction
-- chain.
instance Category AtlasTransversal where
  id = identityAtlasTransversal
  (.) = composeAtlasTransversals

-- | Apply the inherited injective, order-preserving object map.
mapAtlasTransversalObject
  :: AtlasTransversal source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement target
mapAtlasTransversalObject transversal =
  mapOrderedAtlasTransposalObject
    (atlasTransversalOrderedTransposal transversal)

-- | Try to recover an element under the inherited injective object map.
atlasTransversalPreimage
  :: AtlasTransversal source target
  -> AtlasTransposalElement target
  -> Maybe (AtlasTransposalElement source)
atlasTransversalPreimage transversal =
  orderedAtlasTransposalPreimage
    (atlasTransversalOrderedTransposal transversal)

-- | Invoke the inherited injectivity certificate.
atlasTransversalLeftInverse
  :: AtlasTransversal source target
  -> AtlasTransposalElement source
  -> ()
atlasTransversalLeftInverse transversal =
  orderedAtlasTransposalLeftInverse
    (atlasTransversalOrderedTransposal transversal)

-- | Invoke the inherited strict-order preservation certificate.
atlasTransversalPreservesOrder
  :: AtlasTransversal source target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement source
  -> ()
atlasTransversalPreservesOrder transversal =
  orderedAtlasTransposalPreservesOrder
    (atlasTransversalOrderedTransposal transversal)

-- | Recover the underlying pagination morphism.
atlasTransversalPagination
  :: AtlasWitness source
  -> AtlasTransversal source target
  -> PaginationMorphism
       (AtlasObjectPaginationScope source)
       (AtlasObjectPaginationScope target)
atlasTransversalPagination sourceWitness transversal =
  orderedAtlasTransposalPagination
    sourceWitness
    (atlasTransversalOrderedTransposal transversal)

-- | Apply the included arrow to a padded page element.
mapAtlasTransversalElement
  :: AtlasWitness source
  -> AtlasTransversal source target
  -> PageElement (AtlasObjectPaginationScope source) object
  -> SomePageElement (AtlasObjectPaginationScope target)
mapAtlasTransversalElement sourceWitness transversal =
  mapOrderedAtlasTransposalElement
    sourceWitness
    (atlasTransversalOrderedTransposal transversal)

-- | Apply the included arrow to a page-element arrow.
mapAtlasTransversalArrow
  :: AtlasWitness source
  -> AtlasTransversal source target
  -> PageElementArrow
       (AtlasObjectPaginationScope source) sourceObject targetObject
  -> SomePageElementArrow (AtlasObjectPaginationScope target)
mapAtlasTransversalArrow sourceWitness transversal =
  mapOrderedAtlasTransposalArrow
    sourceWitness
    (atlasTransversalOrderedTransposal transversal)

-- | Apply the included arrow to a cell and its dependent datum.
mapAtlasTransversalData
  :: AtlasWitness source
  -> AtlasTransversal source target
  -> PageElement (AtlasObjectPaginationScope source) sourceObject
  -> AtlasMorphismImage
       (AtlasObjectPaginationScope target)
       (AtlasObjectCellData source)
       (AtlasObjectCellData target)
       sourceObject
mapAtlasTransversalData sourceWitness transversal =
  mapOrderedAtlasTransposalData
    sourceWitness
    (atlasTransversalOrderedTransposal transversal)
