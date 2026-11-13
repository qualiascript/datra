{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

-- | Runtime construction of the Charter functor and its hom-set
-- correspondence. The module intentionally introduces no @data@
-- declaration: the only new carrier is the proof-transparent newtype in
-- "Charter.LiquidInternal".
module Charter.Internal
  ( ChartedCellData
  , ChartedAtlasObject
  , chartCellData
  , chartedCellDataValue
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
  ( Atlas
  , AtlasHom
  , AtlasMorphism
  , AtlasObject
  , AtlasObjectCellData
  , AtlasObjectPaginationScope
  , AtlasWitness
  , atlasHom
  , identityAtlasObjectMap
  , atlasMorphism
  , atlasMorphismAction
  , atlasPagination
  , atlasPageElements
  , atlasDataAt
  , atlasWitness
  , mapAtlasData
  , materializeAtlasHom
  )
import Atlas.Internal
  ( atlasCoherenceWitness
  , atlasCompositionWitness
  , atlasDataAction
  , atlasDisjointWitness
  , atlasIdentityWitness
  , atlasWithScope
  )
import Atlas.Morphism.Internal
  ( AtlasWitness (..)
  , atlasMorphismActionNaturality
  , atlasMorphismObjectMapWitness
  , withAtlasMorphismAction
  , normalizeAtlasMorphismAction
  , atlasMorphismActionPreservesArrow
  , atlasMorphismSource
  , atlasMorphismTarget
  , mapAtlasMorphismActionComponent
  , mapAtlasMorphismActionObject
  )
import AtlasCoveredPageElement.Internal
  ( AtlasCoverageWitness (..)
  , atlasCoveredPageElementAt
  , findAtlasCoverage
  , findAtlasCoverageRank
  , atlasCoverageWitness
  )
import AtlasMap (AtlasMap, atlasMap, atlasMapAtlas)
import AtlasMap.Internal (atlasMapCoversDatum)
import AtlasTransposal
  ( AtlasTransposalElement
  , atlasTransposal
  , atlasTransposalElement
  , withAtlasTransposalElement
  )
import AtlasTransversal
  ( AtlasTransversal
  , atlasTransversal
  , withTransversalImage
  , atlasTransversalHom
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
import Charter.LiquidInternal
  ( ChartedCellData
  , chartCellData
  , chartCounitInsertion
  , chartMapInsertion
  , chartHomLeftInverseValue
  , chartHomNaturalityLeftValue
  , chartHomNaturalityRightValue
  , chartHomRightInverseValue
  , charterCompositionValue
  , charterIdentityValue
  , chartedCellData
  , chartedCellDataValue
  , mapChartedCellData
  )
import DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , domanialInsertion
  , insertionLeftInverse
  , preimage
  )
import Dominion
  ( Dominion
  , dominion
  , rank
  )
import OrderedAtlasTransposal (orderedAtlasTransposal)
import PageElements.Structure
  ( PageElement
  , PageElementArrow
  , arrowTarget
  )
import PageElements.Structure
  ( somePageElementPrecedesReflexive
  , somePageElementTransportedReflexive
  )

-- | The type-level Atlas object produced by Charter. The original Atlas
-- object itself names the new Atlas scope, making the object action stable
-- across separate calls without an empty tag declaration.
type ChartedAtlasObject source =
  AtlasObject
    source
    (AtlasObjectPaginationScope source)
    (ChartedCellData source)

-- | The covered sub-dominion at a cell. Lean only needs the old rank composed
-- with subtype projection. Haskell's stronger 'Dominion' API also requires an
-- executable @unrank@, so both directions use the canonical enumeration of
-- final-region witnesses.
-- ALIGN: CHARTER-DOMINION-ROUNDTRIP.
chartedDominion
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> Dominion (ChartedCellData (AtlasObject atlasScope scope cellData) object)
chartedDominion valueAtlas occurrence =
  dominion chartRank chartUnrank chartRoundTrip
  where
    chartRank =
      findAtlasCoverageRank valueAtlas occurrence . chartedCellDataValue

    chartUnrank =
      fmap chartedCellData . atlasCoveredPageElementAt valueAtlas occurrence

    chartRoundTrip _ = ()

-- ALIGN: CHARTER-DATA-INSERTION.
-- ALIGN: CHARTER-DATA-INVERSE-SOUND.
chartedInsertion
  :: Atlas atlasScope scope cellData origin final
  -> PageElementArrow scope source target
  -> DomanialInsertion
       (ChartedCellData (AtlasObject atlasScope scope cellData) source)
       (ChartedCellData (AtlasObject atlasScope scope cellData) target)
chartedInsertion valueAtlas pageArrow =
  domanialInsertion forward backward leftInverse
  where
    original = mapAtlasData valueAtlas pageArrow

    forward = mapChartedCellData (applyInsertion original)

    backward target = do
      -- A left inverse may return an arbitrary candidate outside its image.
      -- Only an actual preimage inherits coverage from the target datum.
      let targetValue = chartedCellDataValue target
          targetRank = rank (atlasDataAt valueAtlas (arrowTarget pageArrow))
      candidate <- preimage original targetValue
      if targetRank (applyInsertion original candidate) == targetRank targetValue
        then Just (chartedCellData candidate)
        else Nothing

    leftInverse source =
      insertionLeftInverse original (chartedCellDataValue source)

-- | Retain exactly the covered page elements in every Atlas cell.
-- ALIGN: CHARTER-ATLAS-INTERPRETATION.
chartAtlas
  :: Atlas atlasScope scope cellData origin final
  -> Atlas
       (AtlasObject atlasScope scope cellData)
       scope
       (ChartedCellData (AtlasObject atlasScope scope cellData))
       origin
       final
chartAtlas valueAtlas =
  atlasWithScope
    (atlasPagination valueAtlas)
    (atlasDataAction (atlasPageElements valueAtlas)
      (chartedDominion valueAtlas)
      (chartedInsertion valueAtlas))
    (\occurrence covered ->
      atlasIdentityWitness
        valueAtlas occurrence (chartedCellDataValue covered))
    (\second first _ covered ->
      atlasCompositionWitness
        valueAtlas second first (chartedCellDataValue covered))
    (\occurrence coherenceArrow _ covered ->
      atlasCoherenceWitness
        valueAtlas occurrence coherenceArrow (chartedCellDataValue covered))
    (\left right leftToOrigin rightToOrigin _ leftDatum rightDatum ->
      atlasDisjointWitness
        valueAtlas
        left
        right
        leftToOrigin
        rightToOrigin
        (chartedCellDataValue leftDatum)
        (chartedCellDataValue rightDatum))

-- ALIGN: CHARTER-COVERAGE-WITNESS.
chartCoverageWitness
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> ChartedCellData (AtlasObject atlasScope scope cellData) object
  -> AtlasCoverageWitness
       (ChartedAtlasObject (AtlasObject atlasScope scope cellData))
chartCoverageWitness valueAtlas source covered =
  case findAtlasCoverage valueAtlas source (chartedCellDataValue covered) of
    AtlasCoverageWitness region regionDatum _ _ ->
      atlasCoverageWitness
        (chartAtlas valueAtlas)
        source
        covered
        region
        (chartedCellData regionDatum)
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
  -> (forall object. PageElement sourceScope object -> sourceCellData object
        -> Maybe (ChartedCellData (AtlasObject sourceAtlasScope sourceScope sourceCellData) object))
  -> (forall object. PageElement sourceScope object
        -> ChartedCellData (AtlasObject sourceAtlasScope sourceScope sourceCellData) object -> ())
  -> AtlasMorphism
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
       sourceScope targetScope
       (ChartedCellData (AtlasObject sourceAtlasScope sourceScope sourceCellData))
       (ChartedCellData (AtlasObject targetAtlasScope targetScope targetCellData))
chartMorphism morphism backward leftInverse =
  withAtlasMorphismAction morphism $ \completeAction ->
    let action = normalizeAtlasMorphismAction completeAction
    in atlasMorphism
      (atlasMorphismAction
        (atlasMorphismObjectMapWitness action)
        (chartAtlas (atlasMorphismSource action))
        (chartAtlas (atlasMorphismTarget action))
        (mapAtlasMorphismActionObject action)
        (\occurrence -> chartMapInsertion
          (mapAtlasMorphismActionComponent action occurrence)
          (backward occurrence) (leftInverse occurrence))
        (atlasMorphismActionPreservesArrow action)
        (\pageArrow covered ->
          atlasMorphismActionNaturality action pageArrow (chartedCellDataValue covered)))

chartHom
  :: AtlasWitness source
  -> AtlasWitness target
  -> AtlasHom source target
  -> (forall object. PageElement (AtlasObjectPaginationScope source) object
        -> AtlasObjectCellData source object -> Maybe (ChartedCellData source object))
  -> (forall object. PageElement (AtlasObjectPaginationScope source) object
        -> ChartedCellData source object -> ())
  -> AtlasHom (ChartedAtlasObject source) (ChartedAtlasObject target)
chartHom sourceWitness@(AtlasWitness _) (AtlasWitness _) hom backward leftInverse =
  atlasHom (chartMorphism (materializeAtlasHom sourceWitness hom) backward leftInverse)

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
chartMap sourceWitness@(AtlasWitness sourceAtlas)
         targetWitness@(AtlasWitness targetAtlas)
         transversal backward leftInverse =
  atlasTransversalMap
    (atlasTransversal
      (chartAtlas sourceAtlas)
      (chartAtlas targetAtlas)
      chartedOrdered
      (\covered -> withTransversalImage (chartAtlas sourceAtlas) chartedOrdered covered $
        \targetOccurrence targetDatum ->
          chartCoverageWitness targetAtlas targetOccurrence targetDatum))
  where
    sourceChartWitness = atlasWitness (chartAtlas sourceAtlas)
    hom = chartHom sourceWitness targetWitness (atlasTransversalHom transversal) backward leftInverse

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
  :: ChartedCellData atlasObject object
  -> ()
charterFunctorIdentity = charterIdentityValue

charterFunctorComposition
  :: forall source sourceObject middle middleObject target targetObject.
     (AtlasObjectCellData source sourceObject
      -> AtlasObjectCellData middle middleObject)
  -> (AtlasObjectCellData middle middleObject
      -> AtlasObjectCellData target targetObject)
  -> ChartedCellData source sourceObject
  -> ()
charterFunctorComposition =
  charterCompositionValue
    @source @sourceObject @middle @middleObject @target @targetObject

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
    (\covered -> withTransversalImage charted ordered covered $
      \targetOccurrence targetDatum ->
        findAtlasCoverage valueAtlas targetOccurrence targetDatum)
  where
    charted = chartAtlas valueAtlas
    chartedWitness = atlasWitness charted

    action =
      atlasMorphismAction
        identityAtlasObjectMap
        charted
        valueAtlas
        id
        (\occurrence -> chartCounitInsertion (backward occurrence) (leftInverse occurrence))
        (\source _ ->
          somePageElementPrecedesReflexive source `seq`
            somePageElementTransportedReflexive source)
        (\_ _ -> ())

    hom = atlasHom (atlasMorphism action)

    transposal =
      atlasTransposal
        chartedWitness
        hom
        (Just . relabelElement chartedWitness)
        (const ())

    ordered = orderedAtlasTransposal transposal (\_ _ -> ())

-- | Unit-at-an-Atlas-map, used to define the forward hom equivalence.
-- ALIGN: CHARTER-UNIT-INTERPRETATION.
chartUnit
  :: AtlasMap source
  -> AtlasTransversal source (ChartedAtlasObject source)
chartUnit sourceMap =
  case atlasMapAtlasWitness sourceMap of
    AtlasWitness valueAtlas ->
      atlasTransversal
        valueAtlas
        (chartAtlas valueAtlas)
        ordered
        (\covered -> withTransversalImage valueAtlas ordered covered $
          \targetOccurrence targetDatum ->
            chartCoverageWitness valueAtlas targetOccurrence targetDatum)
      where
        ordered = orderedAtlasTransposal transposal (\_ _ -> ())
        sourceWitness = AtlasWitness valueAtlas
        action =
          atlasMorphismAction
            identityAtlasObjectMap
            valueAtlas
            (chartAtlas valueAtlas)
            id
            (\occurrence ->
              domanialInsertion
                (\datum ->
                  atlasMapCoversDatum sourceMap occurrence datum `seq`
                    chartedCellData datum)
                (Just . chartedCellDataValue)
                (const ()))
            (\source _ ->
              somePageElementPrecedesReflexive source `seq`
                somePageElementTransportedReflexive source)
            (\_ _ -> ())

        transposal =
          atlasTransposal
            sourceWitness
            (atlasHom (atlasMorphism action))
            (Just . relabelElement sourceWitness)
            (const ())

-- Internal elimination of the Atlas map's witness, kept here so the public
-- Charter surface need not expose representation constructors.
atlasMapAtlasWitness :: AtlasMap object -> AtlasWitness object
atlasMapAtlasWitness = atlasMapAtlas

-- | Forward direction of the hom-set equivalence, Lean's @chartLift@.
-- ALIGN: CHARTER-LIFT-INTERPRETATION.
-- ALIGN: CHARTER-LIFT-FULL-SUBCATEGORY.
chartLift
  :: AtlasMap source
  -> AtlasWitness target
  -> AtlasTransversal source target
  -> AtlasTransversalMap source (ChartedAtlasObject target)
chartLift sourceMap targetWitness arrow =
  case atlasMapAtlasWitness sourceMap of
    sourceWitness@(AtlasWitness sourceAtlas) ->
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
  -> sourceValue
  -> ()
chartHomEquivLeftInverse =
  chartHomLeftInverseValue @sourceValue @target @targetObject

-- ALIGN: CHARTER-HOM-RIGHT-INVERSE-FULL.
chartHomEquivRightInverse
  :: forall sourceValue target targetObject.
     (sourceValue -> ChartedCellData target targetObject)
  -> sourceValue
  -> ()
chartHomEquivRightInverse =
  chartHomRightInverseValue @sourceValue @target @targetObject

-- ALIGN: CHARTER-HOM-NATURALITY-LEFT-FULL.
chartHomEquivNaturalityLeft
  :: forall firstValue secondValue target targetObject.
     (firstValue -> secondValue)
  -> (secondValue -> AtlasObjectCellData target targetObject)
  -> firstValue
  -> ()
chartHomEquivNaturalityLeft =
  chartHomNaturalityLeftValue
    @firstValue @secondValue @target @targetObject

-- ALIGN: CHARTER-HOM-NATURALITY-RIGHT-FULL.
chartHomEquivNaturalityRight
  :: forall sourceValue middle middleObject target targetObject.
     (sourceValue -> AtlasObjectCellData middle middleObject)
  -> (AtlasObjectCellData middle middleObject
      -> AtlasObjectCellData target targetObject)
  -> sourceValue
  -> ()
chartHomEquivNaturalityRight =
  chartHomNaturalityRightValue
    @sourceValue @middle @middleObject @target @targetObject

-- | Proof aliases rather than record-shaped proof tokens. Their polymorphic
-- function values are the hom-equivalence and naturality witnesses checked in
-- "Charter.LiquidInternal".
cartographyAdjunction =
  ( chartHomEquivLeftInverse
  , chartHomEquivRightInverse
  , chartHomEquivNaturalityLeft
  , chartHomEquivNaturalityRight
  )

cartographyLemma = cartographyAdjunction
