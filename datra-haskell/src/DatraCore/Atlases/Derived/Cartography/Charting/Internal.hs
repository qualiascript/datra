{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

-- | Runtime construction of the Charting functor and its hom-set
-- correspondence. The module intentionally introduces no @data@
-- declaration: the only new carrier is the proof-transparent newtype in
-- "Charting.LiquidInternal".
module Charting.Internal
  ( ChartedCellData
  , ChartedAtlasObject
  , chartedCellDataValue
  , chartAtlas
  , chartAtlasMap
  , chartCounit
  , chartMap
  , chartingFunctorObject
  , chartingFunctorHom
  , chartingFunctorIdentity
  , chartingFunctorComposition
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
  ( AtlasMorphism (..)
  , AtlasWitness (..)
  , atlasMorphismActionNaturality
  , atlasMorphismObjectMapWitness
  , atlasMorphismActionPreservesArrow
  , atlasMorphismSource
  , atlasMorphismTarget
  , mapAtlasMorphismActionComponent
  , mapAtlasMorphismActionObject
  )
import AtlasCovered.Internal
  ( AtlasCoverageWitness (..)
  , atlasCoveredDatumAt
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
import Charting.LiquidInternal
  ( ChartedCellData
  , chartHomLeftInverseValue
  , chartHomNaturalityLeftValue
  , chartHomNaturalityRightValue
  , chartHomRightInverseValue
  , chartingCompositionValue
  , chartingIdentityValue
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
  )
import OrderedAtlasTransposal (orderedAtlasTransposal)
import PageElements
  ( PageElement
  , PageElementArrow
  )
import PageElements.LiquidInternal
  ( somePageElementPrecedesReflexive
  , somePageElementTransportedReflexive
  )

-- | The type-level Atlas object produced by Charting. The original Atlas
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
      fmap chartedCellData . atlasCoveredDatumAt valueAtlas occurrence

    chartRoundTrip _ = ()

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

    backward target =
      chartedCellData <$> preimage original (chartedCellDataValue target)

    leftInverse source =
      insertionLeftInverse original (chartedCellDataValue source)

-- | Retain exactly the covered data in every Atlas cell.
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
    (atlasDataAction
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

-- | Charting lands in Atlas maps: every charted datum already carries the
-- defining coverage property by construction.
chartAtlasMap
  :: Atlas atlasScope scope cellData origin final
  -> AtlasMap (ChartedAtlasObject (AtlasObject atlasScope scope cellData))
chartAtlasMap valueAtlas =
  atlasMap (chartAtlas valueAtlas) (chartCoverageWitness valueAtlas)

chartMorphism
  :: AtlasMorphism
       sourceAtlasScope targetAtlasScope
       sourceScope targetScope sourceCellData targetCellData
  -> AtlasMorphism
       (AtlasObject sourceAtlasScope sourceScope sourceCellData)
       (AtlasObject targetAtlasScope targetScope targetCellData)
       sourceScope
       targetScope
       (ChartedCellData
          (AtlasObject sourceAtlasScope sourceScope sourceCellData))
       (ChartedCellData
          (AtlasObject targetAtlasScope targetScope targetCellData))
chartMorphism (PrimitiveAtlasMorphism action) =
  atlasMorphism
    (atlasMorphismAction
      (atlasMorphismObjectMapWitness action)
      (chartAtlas (atlasMorphismSource action))
      (chartAtlas (atlasMorphismTarget action))
      (mapAtlasMorphismActionObject action)
      (\occurrence ->
        let original = mapAtlasMorphismActionComponent action occurrence
        in domanialInsertion
             (mapChartedCellData (applyInsertion original))
             (\target ->
               chartedCellData
                 <$> preimage original (chartedCellDataValue target))
             (insertionLeftInverse original . chartedCellDataValue))
      (atlasMorphismActionPreservesArrow action)
      (\pageArrow covered ->
        atlasMorphismActionNaturality
          action pageArrow (chartedCellDataValue covered)))
chartMorphism (IdentityAtlasMorphism valueAtlas) =
  IdentityAtlasMorphism (chartAtlas valueAtlas)
chartMorphism (CompositeAtlasMorphism second first) =
  CompositeAtlasMorphism
    (chartMorphism second)
    (chartMorphism first)

chartHom
  :: AtlasWitness source
  -> AtlasWitness target
  -> AtlasHom source target
  -> AtlasHom (ChartedAtlasObject source) (ChartedAtlasObject target)
chartHom
  sourceWitness@(AtlasWitness _)
  (AtlasWitness _)
  hom =
    atlasHom (chartMorphism (materializeAtlasHom sourceWitness hom))

relabelElement
  :: (AtlasObjectPaginationScope source
        ~ AtlasObjectPaginationScope target)
  => AtlasWitness target
  -> AtlasTransposalElement source
  -> AtlasTransposalElement target
relabelElement targetWitness element =
  withAtlasTransposalElement element (atlasTransposalElement targetWitness)

-- | Arrow action of the Charting functor.
chartMap
  :: AtlasWitness source
  -> AtlasWitness target
  -> AtlasTransversal source target
  -> AtlasTransversalMap
       (ChartedAtlasObject source)
       (ChartedAtlasObject target)
chartMap sourceWitness@(AtlasWitness sourceAtlas)
         targetWitness@(AtlasWitness targetAtlas)
         transversal =
  atlasTransversalMap
    (atlasTransversal
      (chartAtlas sourceAtlas)
      (chartAtlas targetAtlas)
      chartedOrdered
      (\_ targetOccurrence targetDatum ->
        chartCoverageWitness targetAtlas targetOccurrence targetDatum))
  where
    sourceChartWitness = atlasWitness (chartAtlas sourceAtlas)
    hom = chartHom sourceWitness targetWitness (atlasTransversalHom transversal)

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
chartingFunctorObject
  :: Atlas atlasScope scope cellData origin final
  -> AtlasMap (ChartedAtlasObject (AtlasObject atlasScope scope cellData))
chartingFunctorObject = chartAtlasMap

chartingFunctorHom
  :: AtlasWitness source
  -> AtlasWitness target
  -> AtlasTransversal source target
  -> AtlasTransversalMap
       (ChartedAtlasObject source)
       (ChartedAtlasObject target)
chartingFunctorHom = chartMap

chartingFunctorIdentity
  :: ChartedCellData atlasObject object
  -> ()
chartingFunctorIdentity = chartingIdentityValue

chartingFunctorComposition
  :: forall source sourceObject middle middleObject target targetObject.
     (AtlasObjectCellData source sourceObject
      -> AtlasObjectCellData middle middleObject)
  -> (AtlasObjectCellData middle middleObject
      -> AtlasObjectCellData target targetObject)
  -> ChartedCellData source sourceObject
  -> ()
chartingFunctorComposition =
  chartingCompositionValue
    @source @sourceObject @middle @middleObject @target @targetObject

-- | Counit component: forget the coverage subtype.
chartCounit
  :: Atlas atlasScope scope cellData origin final
  -> AtlasTransversal
       (ChartedAtlasObject (AtlasObject atlasScope scope cellData))
       (AtlasObject atlasScope scope cellData)
chartCounit valueAtlas =
  atlasTransversal
    charted
    valueAtlas
    ordered
    (\_ targetOccurrence targetDatum ->
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
        (\occurrence ->
          domanialInsertion
            chartedCellDataValue
            (\datum ->
              findAtlasCoverage valueAtlas occurrence datum `seq`
                Just (chartedCellData datum))
            (const ()))
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
chartUnit
  :: AtlasMap source
  -> AtlasTransversal source (ChartedAtlasObject source)
chartUnit sourceMap =
  case atlasMapAtlasWitness sourceMap of
    AtlasWitness valueAtlas ->
      atlasTransversal
        valueAtlas
        (chartAtlas valueAtlas)
        (orderedAtlasTransposal transposal (\_ _ -> ()))
        (\_ targetOccurrence targetDatum ->
          chartCoverageWitness valueAtlas targetOccurrence targetDatum)
      where
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
-- Charting surface need not expose representation constructors.
atlasMapAtlasWitness :: AtlasMap object -> AtlasWitness object
atlasMapAtlasWitness = atlasMapAtlas

-- | Forward direction of the hom-set equivalence, Lean's @chartLift@.
chartLift
  :: AtlasMap source
  -> AtlasWitness target
  -> AtlasTransversal source target
  -> AtlasTransversalMap source (ChartedAtlasObject target)
chartLift sourceMap targetWitness arrow =
  composeAtlasTransversalMaps
    (chartMap (atlasMapAtlasWitness sourceMap) targetWitness arrow)
    (atlasTransversalMap (chartUnit sourceMap))

-- | Inverse direction: include an Atlas-transversal map and compose it with
-- the chart counit.
chartLower
  :: Atlas atlasScope scope cellData origin final
  -> AtlasTransversalMap source
       (ChartedAtlasObject (AtlasObject atlasScope scope cellData))
  -> AtlasTransversal source (AtlasObject atlasScope scope cellData)
chartLower valueAtlas arrow =
  composeAtlasTransversals
    (chartCounit valueAtlas)
    (atlasTransversalMapTransversal arrow)

chartHomEquivTo
  :: AtlasMap source
  -> AtlasWitness target
  -> AtlasTransversal source target
  -> AtlasTransversalMap source (ChartedAtlasObject target)
chartHomEquivTo = chartLift

chartHomEquivFrom
  :: Atlas atlasScope scope cellData origin final
  -> AtlasTransversalMap source
       (ChartedAtlasObject (AtlasObject atlasScope scope cellData))
  -> AtlasTransversal source (AtlasObject atlasScope scope cellData)
chartHomEquivFrom = chartLower

-- The remaining functions are the checked pointwise equations underlying
-- Lean's two inverse and two naturality extensionality proofs.
chartHomEquivLeftInverse
  :: forall sourceValue target targetObject.
     (sourceValue -> AtlasObjectCellData target targetObject)
  -> sourceValue
  -> ()
chartHomEquivLeftInverse =
  chartHomLeftInverseValue @sourceValue @target @targetObject

chartHomEquivRightInverse
  :: forall sourceValue target targetObject.
     (sourceValue -> ChartedCellData target targetObject)
  -> sourceValue
  -> ()
chartHomEquivRightInverse =
  chartHomRightInverseValue @sourceValue @target @targetObject

chartHomEquivNaturalityLeft
  :: forall firstValue secondValue target targetObject.
     (firstValue -> secondValue)
  -> (secondValue -> AtlasObjectCellData target targetObject)
  -> firstValue
  -> ()
chartHomEquivNaturalityLeft =
  chartHomNaturalityLeftValue
    @firstValue @secondValue @target @targetObject

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
-- "Charting.LiquidInternal".
cartographyAdjunction =
  ( chartHomEquivLeftInverse
  , chartHomEquivRightInverse
  , chartHomEquivNaturalityLeft
  , chartHomEquivNaturalityRight
  )

cartographyLemma = cartographyAdjunction
