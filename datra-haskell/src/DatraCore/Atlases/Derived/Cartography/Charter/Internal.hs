{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

-- | Runtime construction of Charter from data with canonical coverage codes.
module Charter.Internal
  ( ChartedCellData
  , ChartedDatum
  , ChartedAtlasObject
  , chartCellData
  , chartedCellDataValue
  , chartedDatumValid
  , chartAtlas
  , chartAtlasMap
  , chartCounit
  , chartMap
  , charterFunctorObject
  , charterFunctorHom
  , charterFunctorIdentity
  , charterFunctorComposition
  , chartLift
  , chartLower
  , chartHomEquivTo
  , chartHomEquivFrom
  , chartHomEquivLeftInverse
  , chartHomEquivRightInverse
  , chartHomEquivNaturalityLeft
  , chartHomEquivNaturalityRight
  , cartographyAdjunction
  , cartographyLemma
  ) where

import Atlas
  ( AtlasObjectEquality (..)
  , Atlas
  , AtlasHom
  , AtlasMorphism
  , AtlasObject
  , AtlasObjectCellData
  , AtlasObjectAtlasScope
  , AtlasObjectPaginationScope
  , AtlasWitness
  , atlasHom
  , identityAtlasObjectMap
  , atlasMorphism
  , atlasMorphismAction
  , atlasWitness
  , withAtlasWitness
  , atlasMorphismActionNaturality
  , atlasMorphismObjectMapWitness
  , withAtlasMorphismAction
  , normalizeAtlasMorphismAction
  , atlasMorphismActionPreservesArrow
  , atlasMorphismSource
  , atlasMorphismTarget
  , mapAtlasMorphismActionComponent
  , mapAtlasMorphismActionObject
  , materializeAtlasHom
  )
import Atlas.Construction (ConstructedAtlasScope, constructAtlasData)
import AtlasCoveredPageElement
  ( AtlasCoverageWitness, atlasCoverageWitness, withAtlasCoverageWitness
  , atlasCoveredByWitness, atlasCoveredPageElementWitness, withAtlasCoveredPageElement )
import AtlasMap (AtlasMap, atlasMap, atlasMapAtlas, atlasMapCoversDatum)
import AtlasTransposal
  ( AtlasTransposalElement
  , atlasTransposal, atlasTransposalFromAction
  , atlasTransposalElement
  , withAtlasTransposalElement
  )
import AtlasTransversal
  ( AtlasTransversal
  , atlasTransversal
  , withTransversalImage
  , atlasTransversalHom
  , mapAtlasTransversalCoveredPageElement
  , atlasTransversalLeftInverse
  , atlasTransversalPreimage
  , atlasTransversalPreservesOrder
  , composeAtlasTransversals
  )
import AtlasTransversalMap
  ( AtlasTransversalMap
  , atlasTransversalMap
  , atlasTransversalMapTransversal
  , composeAtlasTransversalMaps
  )
import Charter.LiquidInternal ()
import Charter.Data
  ( ChartedCellData
  , ChartedDatum
  , chartCellData
  , chartCounitInsertion
  , chartMapInsertion
  , chartHomLeftInverseValue
  , chartHomNaturalityLeftValue
  , chartHomNaturalityRightValue
  , chartHomRightInverseValue
  , charterCompositionValue
  , charterIdentityValue
  , chartedCellDataValue
  , chartedDatumValid
  , chartedCellCoverage
  )
import DomanialInsertion
  ( applyInsertion
  , domanialInsertion
  )
import Numeric.Natural (Natural)
import OrderedAtlasTransposal (orderedAtlasTransposal)
import PageElements.Structure
  ( PageElement
  )
import PageElements.Structure
  ( somePageElementPrecedesReflexive
  , somePageElementTransportedReflexive
  )

-- | The cached-data construction and original owner jointly name the derived
-- Atlas, making the object action stable across separate calls.
type ChartedAtlasObject source =
  AtlasObject
    (ConstructedAtlasScope ChartedDatum (AtlasObjectAtlasScope source)
      (AtlasObjectPaginationScope source) (AtlasObjectCellData source))
    (AtlasObjectPaginationScope source)
    (ChartedCellData source)

-- | Retain exactly the covered page elements in every Atlas cell.
-- ALIGN: CHARTER-ATLAS-INTERPRETATION.
chartAtlas
  :: Atlas atlasScope scope cellData origin final
  -> Atlas
       (ConstructedAtlasScope ChartedDatum atlasScope scope cellData)
       scope
       (ChartedCellData (AtlasObject atlasScope scope cellData))
       origin
       final
chartAtlas = constructAtlasData

-- ALIGN: CHARTER-COVERAGE-WITNESS.
chartCoverageWitness
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> ChartedCellData (AtlasObject atlasScope scope cellData) object
  -> AtlasCoverageWitness
       (ChartedAtlasObject (AtlasObject atlasScope scope cellData))
chartCoverageWitness valueAtlas source covered =
  let original = chartedCellCoverage valueAtlas source covered
  in withAtlasCoverageWitness valueAtlas original $ \region regionDatum ->
      atlasCoverageWitness
        (chartAtlas valueAtlas)
        source
        covered
        region
        (chartCellData valueAtlas region regionDatum original ())
        ()

-- | Charter lands in Atlas maps: every charted datum already carries the
-- defining coverage property by construction.
-- ALIGN: CHARTER-ATLAS-COVERED.
chartAtlasMap
  :: Atlas atlasScope scope cellData origin final
  -> AtlasMap (ChartedAtlasObject (AtlasObject atlasScope scope cellData))
chartAtlasMap valueAtlas =
  atlasMap (chartAtlas valueAtlas) (chartCoverageWitness valueAtlas)

chartMorphism
  :: AtlasMorphism
       sourceAtlasScope targetAtlasScope
       sourceScope targetScope sourceCellData targetCellData
  -> AtlasTransversal (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
  -> (forall object. PageElement sourceScope object -> sourceCellData object
        -> Maybe (ChartedCellData (AtlasObject sourceAtlasScope sourceScope sourceCellData) object))
  -> (forall object. PageElement sourceScope object
        -> ChartedCellData (AtlasObject sourceAtlasScope sourceScope sourceCellData) object -> ())
  -> AtlasMorphism
       (ConstructedAtlasScope ChartedDatum sourceAtlasScope sourceScope sourceCellData)
       (ConstructedAtlasScope ChartedDatum targetAtlasScope targetScope targetCellData)
       sourceScope targetScope
       (ChartedCellData (AtlasObject sourceAtlasScope sourceScope sourceCellData))
       (ChartedCellData (AtlasObject targetAtlasScope targetScope targetCellData))
chartMorphism morphism transversal backward leftInverse =
  withAtlasMorphismAction morphism $ \completeAction ->
    let action = normalizeAtlasMorphismAction completeAction
    in atlasMorphism
      (atlasMorphismAction
        (atlasMorphismObjectMapWitness action)
        (chartAtlas (atlasMorphismSource action))
        (chartAtlas (atlasMorphismTarget action))
        (mapAtlasMorphismActionObject action)
        (\occurrence -> chartMapInsertion
          (atlasMorphismSource action) occurrence
          (atlasMorphismTarget action) (mapAtlasMorphismActionObject action occurrence)
          (mapAtlasMorphismActionComponent action occurrence)
          (\charted ->
            let sourceAtlas = atlasMorphismSource action
                targetAtlas = atlasMorphismTarget action
                sourceDatum = chartedCellDataValue charted
                sourceCoverage = chartedCellCoverage sourceAtlas occurrence charted
                covered = atlasCoveredByWitness sourceAtlas occurrence sourceDatum sourceCoverage
                mapped = mapAtlasTransversalCoveredPageElement transversal covered
                targetOccurrence = mapAtlasMorphismActionObject action occurrence
                targetDatum = applyInsertion (mapAtlasMorphismActionComponent action occurrence) sourceDatum
            in chartCellData targetAtlas targetOccurrence targetDatum
                 (atlasCoveredPageElementWitness mapped) ())
          (backward occurrence) (leftInverse occurrence))
        (atlasMorphismActionPreservesArrow action)
        (\pageArrow covered ->
          atlasMorphismActionNaturality action pageArrow (chartedCellDataValue covered)))

chartHom
  :: AtlasWitness source
  -> AtlasWitness target
  -> AtlasTransversal source target
  -> (forall object. PageElement (AtlasObjectPaginationScope source) object
        -> AtlasObjectCellData source object -> Maybe (ChartedCellData source object))
  -> (forall object. PageElement (AtlasObjectPaginationScope source) object
        -> ChartedCellData source object -> ())
  -> AtlasHom (ChartedAtlasObject source) (ChartedAtlasObject target)
chartHom sourceWitness targetWitness transversal backward leftInverse =
  withAtlasWitness sourceWitness $ \AtlasObjectEquality _ ->
  withAtlasWitness targetWitness $ \AtlasObjectEquality _ ->
  atlasHom (chartMorphism (materializeAtlasHom sourceWitness (atlasTransversalHom transversal)) transversal backward leftInverse)

relabelElement
  :: AtlasWitness (AtlasObject targetAtlasScope scope targetCellData)
  -> AtlasTransposalElement (AtlasObject sourceAtlasScope scope sourceCellData)
  -> AtlasTransposalElement (AtlasObject targetAtlasScope scope targetCellData)
relabelElement targetWitness element =
  withAtlasTransposalElement element (atlasTransposalElement targetWitness)

-- | Arrow action of the Charter functor.
-- ALIGN: CHARTER-MAP-INTERPRETATION.
-- ALIGN: CHARTER-MAP-FULL-SUBCATEGORY.
chartMap
  :: AtlasWitness source
  -> AtlasWitness target
  -> AtlasTransversal source target
  -> (forall object. PageElement (AtlasObjectPaginationScope source) object
        -> AtlasObjectCellData source object -> Maybe (ChartedCellData source object))
  -> (forall object. PageElement (AtlasObjectPaginationScope source) object
        -> ChartedCellData source object -> ())
  -> AtlasTransversalMap
       (ChartedAtlasObject source)
       (ChartedAtlasObject target)
chartMap sourceWitness targetWitness transversal backward leftInverse =
  withAtlasWitness sourceWitness $ \AtlasObjectEquality sourceAtlas ->
  withAtlasWitness targetWitness $ \AtlasObjectEquality targetAtlas ->
  let sourceChartWitness = atlasWitness (chartAtlas sourceAtlas)
      hom = chartHom sourceWitness targetWitness transversal backward leftInverse

      chartedTransposal =
        atlasTransposal
          sourceChartWitness
          hom
          (\targetElement ->
            relabelElement sourceChartWitness
              <$> atlasTransversalPreimage transversal
                    (relabelElement targetWitness targetElement))
          (atlasTransversalLeftInverse transversal . relabelElement sourceWitness)

      chartedOrdered =
        orderedAtlasTransposal chartedTransposal $ \left right ->
          atlasTransversalPreservesOrder
            transversal
            (relabelElement sourceWitness left)
            (relabelElement sourceWitness right)
  in atlasTransversalMap
    (atlasTransversal
      (chartAtlas sourceAtlas)
      (chartAtlas targetAtlas)
      chartedOrdered
      (\covered -> withTransversalImage (chartAtlas sourceAtlas) chartedOrdered covered $
        \targetOccurrence targetDatum ->
          chartCoverageWitness targetAtlas targetOccurrence targetDatum))

-- | Object and arrow actions, named separately instead of packaging a
-- record. This is the requested no-@data@ representation of the functor.
charterFunctorObject
  :: Atlas atlasScope scope cellData origin final
  -> AtlasMap (ChartedAtlasObject (AtlasObject atlasScope scope cellData))
charterFunctorObject = chartAtlasMap

-- ALIGN: CHARTER-ARROW-IDENTITY.
-- ALIGN: CHARTER-ARROW-COMPOSITION.
charterFunctorHom
  :: AtlasWitness source
  -> AtlasWitness target
  -> AtlasTransversal source target
  -> (forall object. PageElement (AtlasObjectPaginationScope source) object
        -> AtlasObjectCellData source object -> Maybe (ChartedCellData source object))
  -> (forall object. PageElement (AtlasObjectPaginationScope source) object
        -> ChartedCellData source object -> ())
  -> AtlasTransversalMap
       (ChartedAtlasObject source)
       (ChartedAtlasObject target)
charterFunctorHom = chartMap

charterFunctorIdentity
  :: (AtlasObjectCellData atlasObject object -> Natural)
  -> ChartedCellData atlasObject object
  -> ()
charterFunctorIdentity = charterIdentityValue

charterFunctorComposition
  :: forall source sourceObject middle middleObject target targetObject.
     (AtlasObjectCellData source sourceObject
      -> AtlasObjectCellData middle middleObject)
  -> (AtlasObjectCellData middle middleObject
      -> AtlasObjectCellData target targetObject)
  -> (AtlasObjectCellData middle middleObject -> Natural)
  -> (AtlasObjectCellData target targetObject -> Natural)
  -> ChartedCellData source sourceObject
  -> ()
charterFunctorComposition =
  charterCompositionValue
    @(AtlasObjectAtlasScope source) @(AtlasObjectPaginationScope source) @(AtlasObjectCellData source) @sourceObject @(AtlasObjectAtlasScope middle) @(AtlasObjectPaginationScope middle) @(AtlasObjectCellData middle) @middleObject @(AtlasObjectAtlasScope target) @(AtlasObjectPaginationScope target) @(AtlasObjectCellData target) @targetObject

-- | Counit component: forget the coverage subtype. Its explicit inverse
-- handles uncovered original data without an unbounded coverage search.
-- ALIGN: CHARTER-COUNIT-ARROW.
chartCounit
  :: Atlas atlasScope scope cellData origin final
  -> (forall object. PageElement scope object -> cellData object
        -> Maybe (ChartedCellData (AtlasObject atlasScope scope cellData) object))
  -> (forall object. PageElement scope object
        -> ChartedCellData (AtlasObject atlasScope scope cellData) object -> ())
  -> AtlasTransversal
       (ChartedAtlasObject (AtlasObject atlasScope scope cellData))
       (AtlasObject atlasScope scope cellData)
chartCounit valueAtlas backward leftInverse =
  atlasTransversal
    charted
    valueAtlas
    ordered
    (\covered -> withAtlasCoveredPageElement covered $ \occurrence datum ->
      chartedCellCoverage valueAtlas occurrence datum)
  where
    charted = chartAtlas valueAtlas
    chartedWitness = atlasWitness charted

    action =
      atlasMorphismAction
        identityAtlasObjectMap
        charted
        valueAtlas
        id
        (\occurrence -> chartCounitInsertion valueAtlas occurrence (backward occurrence) (leftInverse occurrence))
        (\source _ ->
          somePageElementPrecedesReflexive source `seq`
            somePageElementTransportedReflexive source)
        (\_ _ -> ())

    transposal =
      atlasTransposalFromAction
        chartedWitness
        (atlasWitness valueAtlas)
        action
        (Just . relabelElement chartedWitness)
        (const ())

    ordered = orderedAtlasTransposal transposal (\_ _ -> ())

-- | Unit-at-an-Atlas-map, used to define the forward hom equivalence.
-- ALIGN: CHARTER-UNIT-INTERPRETATION.
chartUnit
  :: AtlasMap source
  -> AtlasTransversal source (ChartedAtlasObject source)
chartUnit sourceMap =
  withAtlasWitness (atlasMapAtlas sourceMap) $ \AtlasObjectEquality valueAtlas ->
  let ordered = orderedAtlasTransposal transposal (\_ _ -> ())
      sourceWitness = atlasWitness valueAtlas
      action =
        atlasMorphismAction
          identityAtlasObjectMap
          valueAtlas
          (chartAtlas valueAtlas)
          id
          (\occurrence ->
            domanialInsertion
              (\datum ->
                chartCellData valueAtlas occurrence datum
                  (atlasMapCoversDatum sourceMap occurrence datum) ())
              (Just . chartedCellDataValue)
              (const ()))
          (\source _ ->
            somePageElementPrecedesReflexive source `seq`
              somePageElementTransportedReflexive source)
          (\_ _ -> ())

      transposal =
        atlasTransposalFromAction
          sourceWitness
          (atlasWitness (chartAtlas valueAtlas))
          action
          (Just . relabelElement sourceWitness)
          (const ())
  in atlasTransversal
      valueAtlas
      (chartAtlas valueAtlas)
      ordered
      (\covered -> withTransversalImage valueAtlas ordered covered $
        \targetOccurrence targetDatum ->
          chartCoverageWitness valueAtlas targetOccurrence targetDatum)

-- | Forward direction of the hom-set equivalence, Lean's @chartLift@.
-- ALIGN: CHARTER-LIFT-INTERPRETATION.
-- ALIGN: CHARTER-LIFT-FULL-SUBCATEGORY.
chartLift
  :: AtlasMap source
  -> AtlasWitness target
  -> AtlasTransversal source target
  -> AtlasTransversalMap source (ChartedAtlasObject target)
chartLift sourceMap targetWitness arrow =
  let sourceWitness = atlasMapAtlas sourceMap
  in withAtlasWitness sourceWitness $ \AtlasObjectEquality sourceAtlas ->
      composeAtlasTransversalMaps
        (chartMap sourceWitness targetWitness arrow
          (\occurrence datum -> Just (chartCellData sourceAtlas occurrence datum
            (atlasMapCoversDatum sourceMap occurrence datum) ()))
          (\_ _ -> ()))
        (atlasTransversalMap (chartUnit sourceMap))

-- | Inverse direction: include an Atlas-transversal map and compose it with
-- the chart counit.
-- ALIGN: CHARTER-LOWER-INTERPRETATION.
-- ALIGN: CHARTER-LOWER-FULL-SUBCATEGORY.
chartLower
  :: Atlas atlasScope scope cellData origin final
  -> (forall object. PageElement scope object -> cellData object
        -> Maybe (ChartedCellData (AtlasObject atlasScope scope cellData) object))
  -> (forall object. PageElement scope object
        -> ChartedCellData (AtlasObject atlasScope scope cellData) object -> ())
  -> AtlasTransversalMap source
       (ChartedAtlasObject (AtlasObject atlasScope scope cellData))
  -> AtlasTransversal source (AtlasObject atlasScope scope cellData)
chartLower valueAtlas backward leftInverse arrow =
  composeAtlasTransversals
    (chartCounit valueAtlas backward leftInverse)
    (atlasTransversalMapTransversal arrow)

-- ALIGN: CHARTER-HOM-EQUIV-TO.
chartHomEquivTo
  :: AtlasMap source
  -> AtlasWitness target
  -> AtlasTransversal source target
  -> AtlasTransversalMap source (ChartedAtlasObject target)
chartHomEquivTo = chartLift

-- ALIGN: CHARTER-HOM-EQUIV-FROM.
chartHomEquivFrom
  :: Atlas atlasScope scope cellData origin final
  -> (forall object. PageElement scope object -> cellData object
        -> Maybe (ChartedCellData (AtlasObject atlasScope scope cellData) object))
  -> (forall object. PageElement scope object
        -> ChartedCellData (AtlasObject atlasScope scope cellData) object -> ())
  -> AtlasTransversalMap source
       (ChartedAtlasObject (AtlasObject atlasScope scope cellData))
  -> AtlasTransversal source (AtlasObject atlasScope scope cellData)
chartHomEquivFrom = chartLower

-- The remaining functions are the checked pointwise equations underlying
-- Lean's two inverse and two naturality extensionality proofs.
-- ALIGN: CHARTER-HOM-LEFT-INVERSE-FULL.
chartHomEquivLeftInverse
  :: forall sourceValue target targetObject.
     (sourceValue -> AtlasObjectCellData target targetObject)
  -> (AtlasObjectCellData target targetObject -> Natural)
  -> sourceValue
  -> ()
chartHomEquivLeftInverse =
  chartHomLeftInverseValue @sourceValue @(AtlasObjectAtlasScope target) @(AtlasObjectPaginationScope target) @(AtlasObjectCellData target) @targetObject

-- ALIGN: CHARTER-HOM-RIGHT-INVERSE-FULL.
chartHomEquivRightInverse
  :: forall sourceValue target targetObject.
     (sourceValue -> ChartedCellData target targetObject)
  -> (AtlasObjectCellData target targetObject -> Natural)
  -> (sourceValue -> ())
  -> sourceValue
  -> ()
chartHomEquivRightInverse =
  chartHomRightInverseValue @sourceValue @(AtlasObjectAtlasScope target) @(AtlasObjectPaginationScope target) @(AtlasObjectCellData target) @targetObject

-- ALIGN: CHARTER-HOM-NATURALITY-LEFT-FULL.
chartHomEquivNaturalityLeft
  :: forall firstValue secondValue target targetObject.
     (firstValue -> secondValue)
  -> (secondValue -> AtlasObjectCellData target targetObject)
  -> (AtlasObjectCellData target targetObject -> Natural)
  -> firstValue
  -> ()
chartHomEquivNaturalityLeft =
  chartHomNaturalityLeftValue
    @firstValue @secondValue @(AtlasObjectAtlasScope target) @(AtlasObjectPaginationScope target) @(AtlasObjectCellData target) @targetObject

-- ALIGN: CHARTER-HOM-NATURALITY-RIGHT-FULL.
chartHomEquivNaturalityRight
  :: forall sourceValue middle middleObject target targetObject.
     (sourceValue -> AtlasObjectCellData middle middleObject)
  -> (AtlasObjectCellData middle middleObject
      -> AtlasObjectCellData target targetObject)
  -> (AtlasObjectCellData middle middleObject -> Natural)
  -> (AtlasObjectCellData target targetObject -> Natural)
  -> sourceValue
  -> ()
chartHomEquivNaturalityRight =
  chartHomNaturalityRightValue
    @sourceValue @(AtlasObjectAtlasScope middle) @(AtlasObjectPaginationScope middle) @(AtlasObjectCellData middle) @middleObject @(AtlasObjectAtlasScope target) @(AtlasObjectPaginationScope target) @(AtlasObjectCellData target) @targetObject

-- | Proof aliases rather than record-shaped proof tokens. Their polymorphic
-- function values are the hom-equivalence and naturality witnesses checked in
-- "Charter.Data".
cartographyAdjunction =
  ( chartHomEquivLeftInverse
  , chartHomEquivRightInverse
  , chartHomEquivNaturalityLeft
  , chartHomEquivNaturalityRight
  )

cartographyLemma = cartographyAdjunction
