{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ embed Natural as int @-}

-- | Hidden implementation of Atlas transversals and coverage evidence.
module AtlasTransversal.Internal
  ( AtlasTransversal
  , AtlasCoveredDatum
  , AtlasCoverageWitness
  , atlasCoverageWitness
  , coverageWitnessCovers
  , coverageFinalPage
  , atlasCoveredDatum
  , withAtlasCoveredDatum
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
  , atlasCardinality
  , atlasDataAt
  , atlasOriginCell
  , atlasWitness
  , mapAtlasData
  , normalizeAtlasElement
  , withAtlasMorphismImage
  )
import AtlasTransposal (AtlasTransposal, AtlasTransposalElement)
import Control.Category (Category (..))
import DomanialInsertion (applyInsertion)
import Dominion (rank)
import Numeric.Natural (Natural)
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
  , pageElementArrow
  , pageElementPage
  , withPageElement
  )
import Pagination (PaginationMorphism, SomePageElementArrow)
import Prelude hiding ((.), id)

-- | The existential witness in Lean's @Covered X x t@ predicate: a datum in
-- a final region.  Its constructor is hidden; 'atlasCoverageWitness' is the
-- LiquidHaskell-checked introduction rule.
type role AtlasCoverageWitness nominal
data AtlasCoverageWitness atlasObject where
  AtlasCoverageWitness
    :: PageElement (AtlasObjectPaginationScope atlasObject) regionObject
    -> AtlasObjectCellData atlasObject regionObject
    -> Natural
    -> Natural
    -> AtlasCoverageWitness atlasObject

-- | A datum together with proof-carrying evidence for Lean's
-- @Covered X x t@ predicate.  The source datum is stored alongside its
-- existential final-region witness, so transversal composition never has to
-- reconstruct or dynamically revalidate the proposition.
type role AtlasCoveredDatum nominal
data AtlasCoveredDatum atlasObject where
  AtlasCoveredDatum
    :: PageElement (AtlasObjectPaginationScope atlasObject) object
    -> AtlasObjectCellData atlasObject object
    -> AtlasCoverageWitness atlasObject
    -> AtlasCoveredDatum atlasObject

-- | Rank the image of a datum in the Atlas extent. Dominion ranks are
-- injective, so equality of these ranks is equality of the origin images.
{-@ reflect atlasOriginImageRank @-}
atlasOriginImageRank
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> Natural
atlasOriginImageRank valueAtlas occurrence datum =
  withPageElement (atlasOriginCell valueAtlas) $ \origin ->
    rank
      (atlasDataAt valueAtlas origin)
      (applyInsertion
        (mapAtlasData valueAtlas (pageElementArrow occurrence origin))
        datum)

-- Local reflected aliases keep the coverage proposition available to
-- LiquidHaskell across the public facade modules.
{-@ reflect coveragePage @-}
coveragePage :: PageElement scope object -> Natural
coveragePage = pageElementPage

{-@ reflect coverageNormalize @-}
coverageNormalize
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> PageElement scope object
coverageNormalize = normalizeAtlasElement

{-@ reflect coverageFinalPage @-}
coverageFinalPage
  :: Atlas atlasScope scope cellData origin final
  -> Natural
coverageFinalPage valueAtlas = atlasCardinality valueAtlas - 1

-- | The proposition witnessed by an 'AtlasCoverageWitness'.  This is a
-- reflected specification function only: transversal execution does not call
-- it.  The first conjunct says that the witness lies in the final genuine
-- page; the second is Lean's equality after mapping both data to the origin.
{-@ reflect coverageWitnessCovers @-}
coverageWitnessCovers
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> AtlasCoverageWitness
       (AtlasObject atlasScope scope cellData)
  -> Bool
coverageWitnessCovers
  valueAtlas
  source
  sourceDatum
  (AtlasCoverageWitness _ _ regionPage regionOriginRank) =
    regionPage == coverageFinalPage valueAtlas
      && atlasOriginImageRank valueAtlas source sourceDatum
        == regionOriginRank

-- | Introduce the existential witness for coverage.  The final argument is
-- erased proof evidence. LiquidHaskell accepts a call only when the region is
-- final and the two data have equal images in the Atlas origin.
{-@
atlasCoverageWitness
  :: valueAtlas:Atlas atlasScope scope cellData origin final
  -> source:PageElement scope object
  -> sourceDatum:cellData object
  -> region:PageElement scope regionObject
  -> regionDatum:cellData regionObject
  -> conditions:{ proof:() |
       coveragePage (coverageNormalize valueAtlas region)
         == coverageFinalPage valueAtlas
       && atlasOriginImageRank
            valueAtlas
            (coverageNormalize valueAtlas source)
            sourceDatum
          == atlasOriginImageRank
               valueAtlas
               (coverageNormalize valueAtlas region)
               regionDatum }
  -> { witness:AtlasCoverageWitness
         (AtlasObject atlasScope scope cellData) |
       coverageWitnessCovers
         valueAtlas
         (coverageNormalize valueAtlas source)
         sourceDatum
         witness }
@-}
atlasCoverageWitness
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> PageElement scope regionObject
  -> cellData regionObject
  -> ()
  -> AtlasCoverageWitness
       (AtlasObject atlasScope scope cellData)
atlasCoverageWitness
  valueAtlas _ _ region regionDatum _ =
    AtlasCoverageWitness
      (coverageNormalize valueAtlas region)
      regionDatum
      (coveragePage (coverageNormalize valueAtlas region))
      (atlasOriginImageRank
        valueAtlas
        (coverageNormalize valueAtlas region)
        regionDatum)

-- | Construct coverage evidence using the compile-time-checked introduction
-- rule above. There is no runtime rejection path.
{-@
atlasCoveredDatum
  :: valueAtlas:Atlas atlasScope scope cellData origin final
  -> source:PageElement scope object
  -> sourceDatum:cellData object
  -> region:PageElement scope regionObject
  -> regionDatum:cellData regionObject
  -> conditions:{ proof:() |
       coveragePage (coverageNormalize valueAtlas region)
         == coverageFinalPage valueAtlas
       && atlasOriginImageRank
            valueAtlas
            (coverageNormalize valueAtlas source)
            sourceDatum
          == atlasOriginImageRank
               valueAtlas
               (coverageNormalize valueAtlas region)
               regionDatum }
  -> AtlasCoveredDatum (AtlasObject atlasScope scope cellData)
@-}
atlasCoveredDatum
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> PageElement scope regionObject
  -> cellData regionObject
  -> ()
  -> AtlasCoveredDatum
       (AtlasObject atlasScope scope cellData)
atlasCoveredDatum
  valueAtlas source sourceDatum region regionDatum conditions =
    AtlasCoveredDatum
      (coverageNormalize valueAtlas source)
      sourceDatum
      (atlasCoverageWitness
        valueAtlas source sourceDatum region regionDatum conditions)

-- | Eliminate a covered datum while retaining its dependent cell-data type.
withAtlasCoveredDatum
  :: AtlasCoveredDatum atlasObject
  -> (forall object.
        PageElement (AtlasObjectPaginationScope atlasObject) object
        -> AtlasObjectCellData atlasObject object
        -> result)
  -> result
withAtlasCoveredDatum
  (AtlasCoveredDatum occurrence datum _)
  useCovered = useCovered occurrence datum

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
