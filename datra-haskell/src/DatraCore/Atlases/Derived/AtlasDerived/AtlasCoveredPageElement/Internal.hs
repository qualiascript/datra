{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ LIQUID "--max-case-expand=0" @-}
{-@ LIQUID "--smt-timeout=10000" @-}
{-@ embed Natural as int @-}

-- | Hidden implementation of coverage by final Atlas regions.
module AtlasCoveredPageElement.Internal
  ( AtlasCoverageWitness
  , CoverageWitness
  , AtlasCoveredPageElement
  , CoveredPageElement (..)
  , atlasCoverageWitness
  , coverageWitnessCovers
  , coverageWitnessValid
  , withAtlasCoverageWitness
  , coverageWitnessOriginRank
  , coverageWitnessRankMatches
  , coverageWitnessCode
  , coverageWitnessBound
  , coverageWitnessAlongArrow
  , coverageWitnessTransport
  , coverageFinalPage
  , coverageNormalize
  , atlasOriginImageRank
  , atlasOriginImageRankNormalized
  , atlasCoverageAt
  , coverageResultCovers
  , coverageRankCandidate
  , coverageRankCandidateExact
  , coverageRankWitness
  , atlasCoverageRankWithin
  , atlasCoverageRank
  , atlasCoverageRankLeast
  , coverageRankCanonical
  , coverageRankCanonicalUnique
  , coverageRankCandidateSameOrigin
  , coverageRankCanonicalSameOrigin
  , coverageRankAlongArrow
  , coverageRankNormalized
  , atlasCoveredPageElementAt
  , atlasCoveredPageElement
  , withAtlasCoveredPageElement
  , coveredPageElementValid
  , coveredPageElementSource
  , withAtlasCoveredPageElementOf
  , atlasCoveredPageElementWitness
  ) where

import Atlas
  ( Atlas
  , AtlasObject
  , AtlasObjectCellData
  , AtlasObjectAtlasScope
  , AtlasObjectPaginationScope
  , atlasCardinality
  , atlasDataAt
  , atlasAcceptsDatum
  , mapAtlasData
  , normalizeAtlasElementTraceValid
  , atlasAcceptsDatumNormalized
  , normalizeAtlasElement
  , atlasNormalizationArrow
  , atlasCoherenceWitness
  )
import AtlasExtent (atlasCellOriginRankInsertion, cellTraceHasOrigin, cellTraceValid, cellOriginRankMap)
import AtlasTerritory
  ( withAtlasTerritory
  , withAtlasTerritoryOf
  , atlasTerritoryChain
  , atlasTerritoryElement
  )
import DomanialInsertion.Core (applyInsertion, preimage, insertionLeftInverse)
import Chain (ChainIndex, chainIndex, chainIndexPosition, chainObjectAt, chainPosition)
import DatraOrdinal (ordinal, ordinalCoefficients)
import DatraOrdinal.Laws (ordinalDecodeEncode)

{-@ reflect ordinalCoefficients @-}
import Dominion (Dominion, rank, unrank, dominionCoherence)

{-@ opaque-reflect rank @-}
import qualified NaturalSearch
import Numeric.Natural (Natural)
import Data.Kind (Type)
import NaturalEncoding (pairNatural, unpairNatural, unpairPair, encodeNaturalList, decodeNaturalList)
import PageElements.Structure
  ( PageElement
  , SomePageElement (..)
  , PageElementArrow
  , arrowSource
  , arrowTarget
  , pageElementPage
  , pageElementPosition
  )

-- | The existential witness in Lean's @Covered X x t@ predicate: a datum in
-- a final region whose image in the origin is the image of the source datum.
-- Its constructor is hidden; 'atlasCoverageWitness' is the checked
-- introduction rule.
type AtlasCoverageWitness atlasObject =
  CoverageWitness (AtlasObjectAtlasScope atlasObject)
    (AtlasObjectPaginationScope atlasObject) (AtlasObjectCellData atlasObject)

type role CoverageWitness nominal nominal nominal
{-@ data CoverageWitness a s d where
      AtlasCoverageWitness :: forall a s d object.
        payload:CoverageRegionData s d object -> CoverageWitness a s d @-}
data CoverageWitness (atlasScope :: Type) scope cellData where
  AtlasCoverageWitness
    :: forall atlasScope scope cellData regionObject.
       CoverageRegionData scope cellData regionObject
    -> CoverageWitness atlasScope scope cellData

type role CoverageRegionData nominal nominal nominal
{-@ data CoverageRegionData s d object = CoverageRegionData
      { coverageRegion :: PageElement s object
      , coverageRegionDatum :: d object
      , coverageRegionPage :: Natural
      , coverageRegionRank :: Natural
      } @-}
data CoverageRegionData scope cellData regionObject = CoverageRegionData
  { coverageRegion :: PageElement scope regionObject
  , coverageRegionDatum :: cellData regionObject
  , coverageRegionPage :: Natural
  , coverageRegionRank :: Natural
  }

-- | Observe the certified final region and its accepted datum through the
-- owning Atlas, retaining the equality with the witness's cached origin rank.
-- ALIGN: ATLAS-COVERAGE-ELIM.
{-@ withAtlasCoverageWitness :: owner:Atlas a s d o f
      -> witness:{CoverageWitness a s d | coverageWitnessValid owner witness}
      -> (forall object. region:{PageElement s object | cellTraceValid owner region
             && coveragePage region == coverageFinalPage owner}
            -> datum:{d object | atlasAcceptsDatum owner region datum
                 && atlasOriginImageRank owner region datum == coverageWitnessOriginRank witness}
            -> result)
      -> result @-}
withAtlasCoverageWitness
  :: Atlas a s d o f -> CoverageWitness a s d
  -> (forall object. PageElement s object -> d object -> result)
  -> result
withAtlasCoverageWitness _owner (AtlasCoverageWitness value) useRegion =
  useRegion (coverageRegion value) (coverageRegionDatum value)

-- ALIGN: ATLAS-COVERAGE-RANK-OBSERVE.
{-@ reflect coverageWitnessOriginRank @-}
-- Keep callers' reflected equations in terms of this checked observation.
{-# OPAQUE coverageWitnessOriginRank #-}
coverageWitnessOriginRank :: CoverageWitness a s d -> Natural
coverageWitnessOriginRank (AtlasCoverageWitness value) = coverageRegionRank value

-- | Coverage certifies the cached rank of this exact source datum.
-- ALIGN: ATLAS-COVERAGE-CACHED-RANK-MATCHES.
{-@ coverageWitnessRankMatches :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> witness:{CoverageWitness a s d | coverageWitnessCovers owner source datum witness}
      -> {coverageWitnessOriginRank witness == atlasOriginImageRank owner source datum} @-}
coverageWitnessRankMatches :: Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d -> ()
coverageWitnessRankMatches _ _ _ (AtlasCoverageWitness _) = ()

-- | Encode the datum after transporting it to the territory representative
-- selected by its final-page position. Reconstruction is certified to succeed;
-- the empty branch is unreachable for a valid coverage witness.
-- ALIGN: ATLAS-COVERAGE-WITNESS-CODE.
{-@ coverageWitnessCode :: owner:Atlas a s d o f
      -> witness:{CoverageWitness a s d | coverageWitnessValid owner witness} -> Natural @-}
coverageWitnessCode :: Atlas a s d o f -> CoverageWitness a s d -> Natural
coverageWitnessCode owner witness =
  withAtlasCoverageWitness owner witness $ \region datum ->
    coverageCodeFor owner region datum region datum

-- | A covering witness supplies a finite, successful candidate for this datum.
-- ALIGN: ATLAS-COVERAGE-WITNESS-BOUND.
{-@ coverageWitnessBound :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> witness:{CoverageWitness a s d | coverageWitnessCovers owner source datum witness}
      -> {candidate:Natural | coverageRankCandidate owner source datum candidate} @-}
coverageWitnessBound :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d -> Natural
coverageWitnessBound owner source datum witness =
  withAtlasCoverageWitness owner witness $ \region regionDatum ->
    coverageCodeFor owner source datum region regionDatum

{-@ coverageCodeFor :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> region:{PageElement s other | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner}
      -> regionDatum:{d other | atlasAcceptsDatum owner region regionDatum
           && atlasOriginImageRank owner region regionDatum == atlasOriginImageRank owner source datum}
      -> {candidate:Natural | coverageRankCandidate owner source datum candidate} @-}
coverageCodeFor :: Atlas a s d o f -> PageElement s object -> d object -> PageElement s other -> d other -> Natural
coverageCodeFor owner source datum region regionDatum =
  case withAtlasTerritoryOf owner region (\index arrow ->
    let target = arrowTarget arrow
        transported = applyInsertion (mapAtlasData owner arrow) regionDatum
        datumRank = rank (atlasDataAt owner target) transported
        code = pairNatural (encodeNaturalList (ordinalCoefficients (pageElementPosition target))) datumRank
    in cellTraceHasOrigin owner region `seq`
       cellTraceHasOrigin owner target `seq`
       cellOriginRankMap owner arrow regionDatum `seq`
       coverageSelectedIndexInverse owner source datum index target transported `seq` code) of
    Nothing -> 0
    Just code -> code

-- | A page element paired with its datum and evidence that it is covered by a
-- final region.
type AtlasCoveredPageElement atlasObject =
  CoveredPageElement (AtlasObjectAtlasScope atlasObject)
    (AtlasObjectPaginationScope atlasObject) (AtlasObjectCellData atlasObject)

type role CoveredPageElement nominal nominal nominal
{-@ data CoveredPageElement a s d where
      AtlasCoveredPageElement :: forall a s d object.
        PageElement s object -> d object -> CoverageWitness a s d
        -> CoveredPageElement a s d @-}
data CoveredPageElement atlasScope scope cellData where
  AtlasCoveredPageElement
    :: forall atlasScope scope cellData object. PageElement scope object
    -> cellData object
    -> CoverageWitness atlasScope scope cellData
    -> CoveredPageElement atlasScope scope cellData

-- | Validate coverage for the exact dependent source and datum stored here.
-- ALIGN: ATLAS-COVERED-PAYLOAD-VALIDITY.
{-@ reflect coveredPageElementValid @-}
coveredPageElementValid :: Atlas a s d o f -> CoveredPageElement a s d -> Bool
coveredPageElementValid owner (AtlasCoveredPageElement source datum witness) =
  coverageWitnessCovers owner source datum witness

-- ALIGN: ATLAS-COVERED-SOURCE.
{-@ reflect coveredPageElementSource @-}
coveredPageElementSource :: CoveredPageElement a s d -> SomePageElement s
coveredPageElementSource (AtlasCoveredPageElement source _ _) = SomePageElement source

-- | Rank the image of a datum in the Atlas extent. Dominion ranks are
-- injective, so equality of these ranks is equality of the origin images.
-- ALIGN: ATLAS-COVERAGE-RANK-EQUALITY.
-- ALIGN: ATLAS-ORIGIN-IMAGE-INTERPRETATION.
-- ALIGN: ATLAS-ORIGIN-RANK-INTERPRETATION.
{-@ reflect atlasOriginImageRank @-}
{-@ atlasOriginImageRank :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> Natural @-}
atlasOriginImageRank
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> Natural
atlasOriginImageRank valueAtlas occurrence datum =
  cellTraceHasOrigin valueAtlas occurrence `seq`
    applyInsertion (atlasCellOriginRankInsertion valueAtlas occurrence) datum

-- | Normalization keeps the exact image in the owning Atlas extent.
-- ALIGN: ATLAS-ORIGIN-RANK-NORMALIZATION.
{-@ atlasOriginImageRankNormalized :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> {atlasOriginImageRank owner (normalizeAtlasElement owner source) datum
           == atlasOriginImageRank owner source datum} @-}
atlasOriginImageRankNormalized :: Atlas a s d o f -> PageElement s object -> d object -> ()
atlasOriginImageRankNormalized owner source datum =
  let arrow = atlasNormalizationArrow owner source
  in arrow `seq`
     normalizeAtlasElementTraceValid owner source `seq`
     atlasCoherenceWitness owner source arrow datum `seq`
     cellTraceHasOrigin owner source `seq`
     cellTraceHasOrigin owner (normalizeAtlasElement owner source) `seq`
     atlasAcceptsDatumNormalized owner source datum `seq`
     cellOriginRankMap owner arrow datum

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

-- | Check the owning trace and carrier before comparing the cached final
-- page and origin rank with the source datum's actual origin image.
-- ALIGN: ATLAS-COVERAGE-VALIDATION.
{-@ reflect coverageWitnessValid @-}
coverageWitnessValid
  :: forall a s d o f. Atlas a s d o f -> CoverageWitness a s d -> Bool
coverageWitnessValid owner
    (AtlasCoverageWitness (value :: CoverageRegionData s d object)) =
  coverageRegionDataValid owner value

{-@ reflect coverageRegionDataValid @-}
coverageRegionDataValid :: Atlas a s d o f -> CoverageRegionData s d object -> Bool
coverageRegionDataValid owner value
  | cellTraceValid owner (coverageRegion value)
  , atlasAcceptsDatum owner (coverageRegion value) (coverageRegionDatum value) =
      coveragePage (coverageRegion value) == coverageFinalPage owner
        && coverageRegionPage value == coveragePage (coverageRegion value)
        && coverageRegionRank value ==
             atlasOriginImageRank owner (coverageRegion value) (coverageRegionDatum value)
  | otherwise = False

-- ALIGN: ATLAS-COVERAGE-INTERPRETATION.
{-@ reflect coverageWitnessCovers @-}
-- ALIGN: ATLAS-COVERAGE-WITNESS-SOUND.
coverageWitnessCovers
  :: Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d -> Bool
coverageWitnessCovers owner source sourceDatum witness
  | cellTraceValid owner source
  , atlasAcceptsDatum owner source sourceDatum =
      coverageWitnessAtRank owner (atlasOriginImageRank owner source sourceDatum) witness
  | otherwise = False

{-@ reflect coverageWitnessAtRank @-}
coverageWitnessAtRank
  :: forall a s d o f. Atlas a s d o f -> Natural
  -> CoverageWitness a s d -> Bool
coverageWitnessAtRank owner sourceRank
    (AtlasCoverageWitness (value :: CoverageRegionData s d regionObject)) =
  coverageRegionDataValid owner value
    && coverageRegionPage value == coverageFinalPage owner
    && sourceRank == coverageRegionRank value

-- | The same witness covers a datum exactly when it covers its transported image.
-- ALIGN: ATLAS-COVERAGE-TRANSPORT-EQUALITY.
{-@ coverageWitnessTransport :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           cellTraceValid owner (arrowSource arrow) && cellTraceValid owner (arrowTarget arrow)}
      -> datum:{d source | atlasAcceptsDatum owner (arrowSource arrow) datum}
      -> witness:CoverageWitness a s d
      -> {coverageWitnessCovers owner (arrowSource arrow) datum witness
           == coverageWitnessCovers owner (arrowTarget arrow)
                (applyInsertion (mapAtlasData owner arrow) datum) witness} @-}
coverageWitnessTransport
  :: Atlas a s d o f -> PageElementArrow s source target -> d source
  -> CoverageWitness a s d -> ()
coverageWitnessTransport owner arrow datum _witness =
  cellTraceHasOrigin owner (arrowSource arrow) `seq`
  cellTraceHasOrigin owner (arrowTarget arrow) `seq`
  applyInsertion (mapAtlasData owner arrow) datum `seq`
  cellOriginRankMap owner arrow datum

-- | A witness for a transported datum also covers the original datum.
-- ALIGN: ATLAS-COVERAGE-TRANSPORT.
{-@ coverageWitnessAlongArrow :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           cellTraceValid owner (arrowSource arrow) && cellTraceValid owner (arrowTarget arrow)}
      -> datum:{d source | atlasAcceptsDatum owner (arrowSource arrow) datum}
      -> witness:{CoverageWitness a s d |
           coverageWitnessCovers owner (arrowTarget arrow)
             (applyInsertion (mapAtlasData owner arrow) datum) witness}
      -> {coverageWitnessCovers owner (arrowSource arrow) datum witness} @-}
coverageWitnessAlongArrow
  :: Atlas a s d o f -> PageElementArrow s source target -> d source
  -> CoverageWitness a s d -> ()
coverageWitnessAlongArrow = coverageWitnessTransport

{-@ opaque-reflect coverageRegionWitness @-}
{-@ coverageRegionWitness :: owner:Atlas a s d o f
      -> region:{PageElement s object | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner}
      -> datum:{d object | atlasAcceptsDatum owner region datum}
      -> {witness:CoverageWitness a s d |
           coverageWitnessValid owner witness && coverageWitnessCovers owner region datum witness} @-}
coverageRegionWitness
  :: forall a s d o f object. Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d
coverageRegionWitness owner region datum =
  AtlasCoverageWitness (CoverageRegionData region datum
    (coveragePage region) (atlasOriginImageRank owner region datum))

-- | Introduce a coverage witness. LiquidHaskell checks that the region is on
-- the final page and that its datum has the same origin image as the source.
{-@
atlasCoverageWitness
  :: valueAtlas:Atlas atlasScope scope cellData origin final
  -> source:{PageElement scope object | cellTraceValid valueAtlas source}
  -> sourceDatum:{cellData object | atlasAcceptsDatum valueAtlas source sourceDatum}
  -> region:{PageElement scope regionObject | cellTraceValid valueAtlas region}
  -> regionDatum:{cellData regionObject | atlasAcceptsDatum valueAtlas region regionDatum}
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
  -> { witness:CoverageWitness atlasScope scope cellData |
       coverageWitnessCovers
         valueAtlas
         (coverageNormalize valueAtlas source)
         sourceDatum
         witness }
@-}
-- ALIGN: ATLAS-COVERAGE-CONSTRUCTOR.
atlasCoverageWitness
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> PageElement scope regionObject
  -> cellData regionObject
  -> ()
  -> CoverageWitness atlasScope scope cellData
atlasCoverageWitness valueAtlas source sourceDatum region regionDatum _ =
  normalizeAtlasElementTraceValid valueAtlas source `seq`
  atlasAcceptsDatumNormalized valueAtlas source sourceDatum `seq`
  normalizeAtlasElementTraceValid valueAtlas region `seq`
  atlasAcceptsDatumNormalized valueAtlas region regionDatum `seq`
  coverageRegionWitness valueAtlas (coverageNormalize valueAtlas region) regionDatum

-- | Construct a covered page element using the checked introduction rule.
{-@
atlasCoveredPageElement
  :: valueAtlas:Atlas atlasScope scope cellData origin final
  -> source:{PageElement scope object | cellTraceValid valueAtlas source}
  -> sourceDatum:{cellData object | atlasAcceptsDatum valueAtlas source sourceDatum}
  -> region:{PageElement scope regionObject | cellTraceValid valueAtlas region}
  -> regionDatum:{cellData regionObject | atlasAcceptsDatum valueAtlas region regionDatum}
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
  -> {element:CoveredPageElement atlasScope scope cellData |
       coveredPageElementValid valueAtlas element}
@-}
-- ALIGN: ATLAS-COVERED-CONSTRUCTOR.
atlasCoveredPageElement
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> PageElement scope regionObject
  -> cellData regionObject
  -> ()
  -> CoveredPageElement atlasScope scope cellData
atlasCoveredPageElement
  valueAtlas source sourceDatum region regionDatum conditions =
    AtlasCoveredPageElement
      (coverageNormalize valueAtlas source)
      sourceDatum
      (atlasCoverageWitness
        valueAtlas source sourceDatum region regionDatum conditions)

-- | Eliminate a covered page element while retaining its dependent cell-data
-- type.
-- ALIGN: ATLAS-COVERED-SEMANTICS.
{-@ reflect withAtlasCoveredPageElement @-}
withAtlasCoveredPageElement
  :: CoveredPageElement atlasScope scope cellData
  -> (forall object.
        PageElement scope object
        -> cellData object
        -> result)
  -> result
withAtlasCoveredPageElement
  (AtlasCoveredPageElement occurrence datum _)
  useCovered = useCovered occurrence datum

-- | Eliminate a validated payload while keeping its owner-specific evidence.
-- ALIGN: ATLAS-COVERED-CERTIFIED-ELIM.
{-@ withAtlasCoveredPageElementOf :: owner:Atlas a s d o f
      -> element:{CoveredPageElement a s d | coveredPageElementValid owner element}
      -> (forall object. source:{PageElement s object | cellTraceValid owner source
                && SomePageElement source == coveredPageElementSource element}
           -> datum:{d object | atlasAcceptsDatum owner source datum}
           -> witness:{CoverageWitness a s d | coverageWitnessCovers owner source datum witness
                && witness == atlasCoveredPageElementWitness element}
           -> result)
      -> result @-}
withAtlasCoveredPageElementOf :: Atlas a s d o f -> CoveredPageElement a s d
  -> (forall object. PageElement s object -> d object -> CoverageWitness a s d -> result) -> result
withAtlasCoveredPageElementOf _ (AtlasCoveredPageElement source datum witness) useCovered =
  useCovered source datum witness

-- | Recover the evidence already carried by a covered datum.
-- ALIGN: ATLAS-COVERED-WITNESS.
{-@ reflect atlasCoveredPageElementWitness @-}
-- Preserve the public observation across worker/wrapper optimization.
{-# OPAQUE atlasCoveredPageElementWitness #-}
atlasCoveredPageElementWitness
  :: CoveredPageElement atlasScope scope cellData -> CoverageWitness atlasScope scope cellData
atlasCoveredPageElementWitness (AtlasCoveredPageElement _ _ witness) = witness

-- | Test whether a finite candidate decodes the requested source datum.
{-@ reflect atlasCoveredPageElementAt @-}
{-@ reflect coverageRankCandidate @-}
{-@ coverageRankCandidate :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> Natural -> Bool @-}
coverageRankCandidate
  :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> Bool
coverageRankCandidate owner source datum candidate =
  coverageValueMatches (atlasDataAt owner source) datum (atlasCoveredPageElementAt owner source candidate)

{-@ reflect coverageValueMatches @-}
coverageValueMatches :: Dominion value -> value -> Maybe value -> Bool
coverageValueMatches _ _ Nothing = False
coverageValueMatches values datum (Just value) = rank values value == rank values datum

{-@ coverageValueMatchesExact :: values:Dominion value -> datum:value -> candidate:Maybe value
      -> {coverageValueMatches values datum candidate <=> candidate == Just datum} @-}
coverageValueMatchesExact :: Dominion value -> value -> Maybe value -> ()
coverageValueMatchesExact _ _ Nothing = ()
coverageValueMatchesExact values datum (Just value) =
  dominionCoherence values datum `seq` dominionCoherence values value

-- | Successful rank comparison identifies the exact decoded datum.
-- ALIGN: ATLAS-COVERAGE-CANDIDATE-EXACT.
{-@ coverageRankCandidateExact :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> candidate:Natural
      -> {coverageRankCandidate owner source datum candidate
           <=> atlasCoveredPageElementAt owner source candidate == Just datum} @-}
coverageRankCandidateExact :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> ()
coverageRankCandidateExact owner source datum candidate =
  coverageValueMatchesExact (atlasDataAt owner source) datum (atlasCoveredPageElementAt owner source candidate)

-- | Recover evidence at a certified rank without searching for another code.
-- ALIGN: ATLAS-COVERAGE-RANK-WITNESS.
{-@ coverageRankWitness :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> candidate:{Natural | coverageRankCandidate owner source datum candidate}
      -> {result:Maybe ({witness:CoverageWitness a s d |
           coverageWitnessCovers owner source datum witness}) | result /= Nothing} @-}
coverageRankWitness
  :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> Maybe (CoverageWitness a s d)
coverageRankWitness owner source datum candidate =
  coverageValueMatchesExact (atlasDataAt owner source) datum (atlasCoveredPageElementAt owner source candidate) `seq`
  case atlasCoverageAt owner source candidate of
    Nothing -> Nothing
    Just (decoded, witness) ->
      dominionCoherence (atlasDataAt owner source) decoded `seq`
      dominionCoherence (atlasDataAt owner source) datum `seq` Just witness

-- | Search the inclusive interval from zero through the supplied limit.
-- ALIGN: ATLAS-COVERAGE-BOUNDED-RANK.
{-@ reflect atlasCoverageRankWithin @-}
{-@ atlasCoverageRankWithin :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> limit:Natural
      -> {result:Maybe ({found:Natural | found <= limit && coverageRankCandidate owner source datum found}) |
           coverageRankCandidate owner source datum limit => result /= Nothing} @-}
atlasCoverageRankWithin
  :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> Maybe Natural
atlasCoverageRankWithin owner source datum limit = searchCoverageRank owner source datum 0 limit

{-@ reflect searchCoverageRank @-}
{-@ searchCoverageRank :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> candidate:Natural -> remaining:Natural
      -> {result:Maybe ({found:Natural | candidate <= found && found <= candidate + remaining
           && coverageRankCandidate owner source datum found}) |
           coverageRankCandidate owner source datum (candidate + remaining) => result /= Nothing} / [remaining] @-}
searchCoverageRank
  :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> Natural -> Maybe Natural
searchCoverageRank owner source datum candidate remaining =
  NaturalSearch.search (coverageRankCandidate owner source datum) candidate remaining

-- | Least coverage rank, bounded by explicit evidence for this exact datum.
-- ALIGN: ATLAS-COVERAGE-WITNESS-RANK.
{-@ atlasCoverageRank :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> witness:{CoverageWitness a s d | coverageWitnessCovers owner source datum witness}
      -> {found:Natural | coverageRankCandidate owner source datum found
           && coverageRankCanonical owner source datum found} @-}
atlasCoverageRank
  :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d -> Natural
atlasCoverageRank owner source datum witness =
  let limit = coverageWitnessBound owner source datum witness
  in case atlasCoverageRankWithin owner source datum limit of
       Nothing -> 0
       Just found -> NaturalSearch.trim (coverageRankCandidate owner source datum) 0 limit found `seq` found

-- | A finite code is canonical exactly when the bounded search selects it.
{-@ reflect coverageRankCanonical @-}
{-@ coverageRankCanonical :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> Natural -> Bool @-}
coverageRankCanonical :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> Bool
coverageRankCanonical owner source datum candidate =
  atlasCoverageRankWithin owner source datum candidate == Just candidate

-- | Canonical codes do not depend on which coverage witness supplied the bound.
-- ALIGN: ATLAS-COVERAGE-CANONICAL-UNIQUE.
{-@ coverageRankCanonicalUnique :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> left:{Natural | coverageRankCanonical owner source datum left}
      -> right:{Natural | coverageRankCanonical owner source datum right}
      -> {left == right} @-}
coverageRankCanonicalUnique
  :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> Natural -> ()
coverageRankCanonicalUnique owner source datum left right =
  NaturalSearch.unique (coverageRankCandidate owner source datum) left right

-- | Equal origin images have exactly the same successful enumeration codes.
-- ALIGN: ATLAS-COVERAGE-CANDIDATE-SAME-ORIGIN.
{-@ coverageRankCandidateSameOrigin :: owner:Atlas a s d o f
      -> source:{PageElement s sourceObject | cellTraceValid owner source}
      -> datum:{d sourceObject | atlasAcceptsDatum owner source datum}
      -> target:{PageElement s targetObject | cellTraceValid owner target}
      -> targetDatum:{d targetObject | atlasAcceptsDatum owner target targetDatum
           && atlasOriginImageRank owner source datum == atlasOriginImageRank owner target targetDatum}
      -> candidate:Natural
      -> {coverageRankCandidate owner source datum candidate == coverageRankCandidate owner target targetDatum candidate} @-}
coverageRankCandidateSameOrigin
  :: Atlas a s d o f -> PageElement s sourceObject -> d sourceObject
  -> PageElement s targetObject -> d targetObject -> Natural -> ()
coverageRankCandidateSameOrigin owner source datum target targetDatum candidate =
  case unpairNatural candidate of
    (positionCode, datumRank) ->
      case chainIndex (atlasTerritoryChain owner) (ordinal (decodeNaturalList positionCode)) of
        Nothing -> ()
        Just index -> case atlasTerritoryElement owner index of
          SomePageElement region ->
            coverageAtIndexSelected owner source index datumRank region `seq`
            coverageAtIndexSelected owner target index datumRank region `seq`
            case unrank (atlasDataAt owner region) datumRank of
              Nothing -> ()
              Just regionDatum ->
                coveragePullbackMatches owner source datum region regionDatum `seq`
                coveragePullbackMatches owner target targetDatum region regionDatum

-- | The canonical cache is unchanged by any origin-image-preserving transport.
-- ALIGN: ATLAS-COVERAGE-CANONICAL-SAME-ORIGIN.
{-@ coverageRankCanonicalSameOrigin :: owner:Atlas a s d o f
      -> source:{PageElement s sourceObject | cellTraceValid owner source}
      -> datum:{d sourceObject | atlasAcceptsDatum owner source datum}
      -> target:{PageElement s targetObject | cellTraceValid owner target}
      -> targetDatum:{d targetObject | atlasAcceptsDatum owner target targetDatum
           && atlasOriginImageRank owner source datum == atlasOriginImageRank owner target targetDatum}
      -> candidate:Natural
      -> {coverageRankCanonical owner source datum candidate == coverageRankCanonical owner target targetDatum candidate} @-}
coverageRankCanonicalSameOrigin
  :: Atlas a s d o f -> PageElement s sourceObject -> d sourceObject
  -> PageElement s targetObject -> d targetObject -> Natural -> ()
coverageRankCanonicalSameOrigin owner source datum target targetDatum candidate =
  NaturalSearch.congruent (coverageRankCandidate owner source datum)
    (coverageRankCandidate owner target targetDatum)
    (coverageRankCandidateSameOrigin owner source datum target targetDatum) 0 candidate

-- | A data arrow preserves both successful codes and their canonical minimum.
-- ALIGN: ATLAS-COVERAGE-RANK-TRANSPORT.
{-@ coverageRankAlongArrow :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           cellTraceValid owner (arrowSource arrow) && cellTraceValid owner (arrowTarget arrow)}
      -> datum:{d source | atlasAcceptsDatum owner (arrowSource arrow) datum}
      -> candidate:Natural
      -> {coverageRankCandidate owner (arrowSource arrow) datum candidate
           == coverageRankCandidate owner (arrowTarget arrow) (applyInsertion (mapAtlasData owner arrow) datum) candidate
           && coverageRankCanonical owner (arrowSource arrow) datum candidate
           == coverageRankCanonical owner (arrowTarget arrow) (applyInsertion (mapAtlasData owner arrow) datum) candidate} @-}
coverageRankAlongArrow
  :: Atlas a s d o f -> PageElementArrow s source target -> d source -> Natural -> ()
coverageRankAlongArrow owner arrow datum candidate =
  cellTraceHasOrigin owner (arrowSource arrow) `seq`
  cellTraceHasOrigin owner (arrowTarget arrow) `seq`
  cellOriginRankMap owner arrow datum `seq`
  let transported = applyInsertion (mapAtlasData owner arrow) datum
  in coverageRankCandidateSameOrigin owner (arrowSource arrow) datum (arrowTarget arrow) transported candidate `seq`
     coverageRankCanonicalSameOrigin owner (arrowSource arrow) datum (arrowTarget arrow) transported candidate

-- | Padding normalization preserves successful and canonical coverage codes.
-- ALIGN: ATLAS-COVERAGE-RANK-NORMALIZATION.
{-@ coverageRankNormalized :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> candidate:Natural
      -> {coverageRankCandidate owner source datum candidate
           == coverageRankCandidate owner (normalizeAtlasElement owner source) datum candidate
           && coverageRankCanonical owner source datum candidate
           == coverageRankCanonical owner (normalizeAtlasElement owner source) datum candidate} @-}
coverageRankNormalized :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> ()
coverageRankNormalized owner source datum candidate =
  normalizeAtlasElementTraceValid owner source `seq`
  atlasAcceptsDatumNormalized owner source datum `seq`
  atlasOriginImageRankNormalized owner source datum `seq`
  coverageRankCandidateSameOrigin owner source datum (normalizeAtlasElement owner source) datum candidate `seq`
  coverageRankCanonicalSameOrigin owner source datum (normalizeAtlasElement owner source) datum candidate

-- | A successful bounded search selects the least successful candidate.
-- ALIGN: ATLAS-COVERAGE-BOUNDED-MINIMAL.
{-@ atlasCoverageRankLeast :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum} -> limit:Natural
      -> found:{Natural | atlasCoverageRankWithin owner source datum limit == Just found}
      -> earlier:{Natural | earlier < found}
      -> {not (coverageRankCandidate owner source datum earlier)} @-}
atlasCoverageRankLeast
  :: Atlas a s d o f -> PageElement s object -> d object -> Natural -> Natural -> Natural -> ()
atlasCoverageRankLeast owner source datum limit found earlier =
  NaturalSearch.least (coverageRankCandidate owner source datum) 0 limit found earlier

-- | Decode one finite coverage candidate. A final-region datum is transported
-- to the origin and pulled back along the selected source cell. Unlike a
-- membership filter, this operation terminates for every index.
{-@ atlasCoveredPageElementAt :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source} -> Natural
      -> Maybe ({datum:d object | atlasAcceptsDatum owner source datum}) @-}
atlasCoveredPageElementAt
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> Natural
  -> Maybe (cellData object)
atlasCoveredPageElementAt valueAtlas source candidate =
  coverageDecodedDatum (atlasCoverageAt valueAtlas source candidate)

-- | Decode one coverage candidate together with the evidence that made it a
-- member of the covered carrier.  Returning the witness alongside the datum
-- lets downstream dependent carriers stay total instead of reconstructing
-- evidence with an unchecked search.
-- ALIGN: ATLAS-COVERAGE-DECODE-SOUND.
-- ALIGN: ATLAS-COVERAGE-RANK-DECODER.
-- ALIGN: ATLAS-COVERAGE-DECODE-COMPLETE.
{-@ reflect atlasCoverageAt @-}
{-@ atlasCoverageAt :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source} -> Natural
      -> Maybe ({result:({datum:d object | atlasAcceptsDatum owner source datum}, CoverageWitness a s d) |
           coverageResultCovers owner source result}) @-}
atlasCoverageAt
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> Natural
  -> Maybe
       ( cellData object
       , CoverageWitness atlasScope scope cellData
       )
atlasCoverageAt valueAtlas source candidate =
  case unpairNatural candidate of
    (positionCode, datumRank) ->
      case chainIndex
        (atlasTerritoryChain valueAtlas)
        (ordinal (decodeNaturalList positionCode)) of
          Nothing -> Nothing
          Just territoryIndex -> coverageAtIndex valueAtlas source datumRank territoryIndex

{-@ reflect coverageAtIndex @-}
{-@ coverageAtIndex :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source} -> Natural
      -> index:{ChainIndex f |
           chainPosition (atlasTerritoryChain owner) (chainObjectAt index) == chainIndexPosition index}
      -> Maybe ({result:({datum:d object | atlasAcceptsDatum owner source datum}, CoverageWitness a s d) |
           coverageResultCovers owner source result}) @-}
coverageAtIndex
  :: Atlas a s d o f -> PageElement s object -> Natural -> ChainIndex f
  -> Maybe (d object, CoverageWitness a s d)
coverageAtIndex owner source datumRank index =
  withAtlasTerritory owner index (coverageAtRegion owner source datumRank)

-- | The public selector's exact occurrence determines the regional decoder.
-- ALIGN: ATLAS-COVERAGE-SELECTED-REGION.
{-@ coverageAtIndexSelected :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> index:{ChainIndex f |
           chainPosition (atlasTerritoryChain owner) (chainObjectAt index) == chainIndexPosition index}
      -> datumRank:Natural
      -> region:{PageElement s other | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner
           && SomePageElement region == atlasTerritoryElement owner index}
      -> {coverageAtIndex owner source datumRank index == coverageAtRegion owner source datumRank region} @-}
coverageAtIndexSelected
  :: Atlas a s d o f -> PageElement s object -> ChainIndex f -> Natural -> PageElement s other -> ()
coverageAtIndexSelected _owner _source _index _datumRank _region = ()

-- | The position codec selects the same certified territory index.
-- ALIGN: ATLAS-COVERAGE-INDEX-DECODE.
{-@ coverageIndexEncode :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> index:{ChainIndex f |
           chainPosition (atlasTerritoryChain owner) (chainObjectAt index) == chainIndexPosition index
           && chainIndex (atlasTerritoryChain owner) (chainIndexPosition index) == Just index}
      -> datumRank:Natural
      -> {atlasCoverageAt owner source
           (pairNatural (encodeNaturalList (ordinalCoefficients (chainIndexPosition index))) datumRank)
             == coverageAtIndex owner source datumRank index} @-}
coverageIndexEncode :: Atlas a s d o f -> PageElement s object -> ChainIndex f -> Natural -> ()
coverageIndexEncode _owner _source index datumRank =
  unpairPair (encodeNaturalList (ordinalCoefficients (chainIndexPosition index))) datumRank `seq`
    ordinalDecodeEncode (chainIndexPosition index)

{-@ reflect coverageAtRegion @-}
{-@ coverageAtRegion :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> Natural
      -> region:{PageElement s regionObject | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner}
      -> Maybe ({result:({datum:d object | atlasAcceptsDatum owner source datum}, CoverageWitness a s d) |
           coverageResultCovers owner source result}) @-}
coverageAtRegion
  :: Atlas a s d o f -> PageElement s object -> Natural
  -> PageElement s regionObject
  -> Maybe (d object, CoverageWitness a s d)
coverageAtRegion owner source datumRank region =
  case unrank (atlasDataAt owner region) datumRank of
    Nothing -> Nothing
    Just regionDatum -> coveragePullback owner source region regionDatum

-- | Pull a decoded region datum back through the source's checked insertion.
{-@ reflect coveragePullback @-}
{-@ coveragePullback :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> region:{PageElement s regionObject | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner}
      -> regionDatum:{d regionObject | atlasAcceptsDatum owner region regionDatum}
      -> Maybe ({result:({datum:d object | atlasAcceptsDatum owner source datum}, CoverageWitness a s d) |
           coverageResultCovers owner source result}) @-}
coveragePullback
  :: Atlas a s d o f -> PageElement s object -> PageElement s regionObject
  -> d regionObject -> Maybe (d object, CoverageWitness a s d)
coveragePullback owner source region regionDatum =
  cellTraceHasOrigin owner source `seq`
  let regionOriginRank = atlasOriginImageRank owner region regionDatum
  in case preimage (atlasCellOriginRankInsertion owner source) regionOriginRank of
    Nothing -> Nothing
    Just sourceDatum
      | atlasOriginImageRank owner source sourceDatum == regionOriginRank ->
          Just (coveragePair owner source sourceDatum
            (coverageRegionWitness owner region regionDatum))
      | otherwise -> Nothing

{-@ reflect coverageDecodedDatum @-}
coverageDecodedDatum :: Maybe (datum, witness) -> Maybe datum
coverageDecodedDatum Nothing = Nothing
coverageDecodedDatum (Just (datum, _)) = Just datum

-- | An exact region image returns the original source datum.
-- ALIGN: ATLAS-COVERAGE-PULLBACK-INVERSE.
{-@ coveragePullbackInverse :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> region:{PageElement s regionObject | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner}
      -> regionDatum:{d regionObject | atlasAcceptsDatum owner region regionDatum
           && atlasOriginImageRank owner region regionDatum == atlasOriginImageRank owner source datum}
      -> {coverageDecodedDatum (coveragePullback owner source region regionDatum) == Just datum} @-}
coveragePullbackInverse
  :: Atlas a s d o f -> PageElement s object -> d object
  -> PageElement s regionObject -> d regionObject -> ()
coveragePullbackInverse owner source datum _region _regionDatum =
  cellTraceHasOrigin owner source `seq`
    insertionLeftInverse (atlasCellOriginRankInsertion owner source) datum

-- | Local decoding matches a given datum exactly at its origin image.
{-@ coveragePullbackMatches :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> region:{PageElement s other | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner}
      -> regionDatum:{d other | atlasAcceptsDatum owner region regionDatum}
      -> {coverageValueMatches (atlasDataAt owner source) datum
           (coverageDecodedDatum (coveragePullback owner source region regionDatum))
           == (atlasOriginImageRank owner source datum == atlasOriginImageRank owner region regionDatum)} @-}
coveragePullbackMatches
  :: Atlas a s d o f -> PageElement s object -> d object
  -> PageElement s other -> d other -> ()
coveragePullbackMatches owner source datum region regionDatum =
  cellTraceHasOrigin owner source `seq`
  coverageValueMatchesExact (atlasDataAt owner source) datum
    (coverageDecodedDatum (coveragePullback owner source region regionDatum)) `seq`
  if atlasOriginImageRank owner source datum == atlasOriginImageRank owner region regionDatum
    then coveragePullbackInverse owner source datum region regionDatum
    else case preimage (atlasCellOriginRankInsertion owner source) (atlasOriginImageRank owner region regionDatum) of
      Nothing -> ()
      Just _ -> ()

-- | Unranking the retained region rank and pulling it back recovers the source.
-- ALIGN: ATLAS-COVERAGE-REGION-INVERSE.
{-@ coverageAtRegionInverse :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> region:{PageElement s regionObject | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner}
      -> regionDatum:{d regionObject | atlasAcceptsDatum owner region regionDatum
           && atlasOriginImageRank owner region regionDatum == atlasOriginImageRank owner source datum}
      -> {coverageDecodedDatum
           (coverageAtRegion owner source (rank (atlasDataAt owner region) regionDatum) region) == Just datum} @-}
coverageAtRegionInverse
  :: Atlas a s d o f -> PageElement s object -> d object
  -> PageElement s regionObject -> d regionObject -> ()
coverageAtRegionInverse owner source datum region regionDatum =
  dominionCoherence (atlasDataAt owner region) regionDatum `seq`
    coveragePullbackInverse owner source datum region regionDatum

-- | Combine the position codec with the selected region's checked inverse.
-- ALIGN: ATLAS-COVERAGE-SELECTED-INDEX-INVERSE.
{-@ coverageSelectedIndexInverse :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> index:{ChainIndex f |
           chainPosition (atlasTerritoryChain owner) (chainObjectAt index) == chainIndexPosition index
           && chainIndex (atlasTerritoryChain owner) (chainIndexPosition index) == Just index}
      -> region:{PageElement s other | cellTraceValid owner region
           && coveragePage region == coverageFinalPage owner
           && SomePageElement region == atlasTerritoryElement owner index}
      -> regionDatum:{d other | atlasAcceptsDatum owner region regionDatum
           && atlasOriginImageRank owner region regionDatum == atlasOriginImageRank owner source datum}
      -> {coverageRankCandidate owner source datum
           (pairNatural (encodeNaturalList (ordinalCoefficients (chainIndexPosition index)))
             (rank (atlasDataAt owner region) regionDatum))} @-}
coverageSelectedIndexInverse
  :: Atlas a s d o f -> PageElement s object -> d object
  -> ChainIndex f -> PageElement s other -> d other -> ()
coverageSelectedIndexInverse owner source datum index region regionDatum =
  let datumRank = rank (atlasDataAt owner region) regionDatum
  in coverageIndexEncode owner source index datumRank `seq`
     coverageAtIndexSelected owner source index datumRank region `seq`
     coverageAtRegionInverse owner source datum region regionDatum

{-@ reflect coveragePair @-}
{-@ coveragePair :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> witness:{CoverageWitness a s d |
           coverageWitnessCovers owner source datum witness}
      -> {result:({value:d object | atlasAcceptsDatum owner source value}, CoverageWitness a s d) |
           coverageResultCovers owner source result} @-}
coveragePair
  :: Atlas a s d o f -> PageElement s object -> d object
  -> CoverageWitness a s d
  -> (d object, CoverageWitness a s d)
coveragePair _owner _source datum witness = (datum, witness)

-- | The decoder retains coverage for the exact datum returned alongside it.
{-@ reflect coverageResultCovers @-}
coverageResultCovers
  :: Atlas a s d o f -> PageElement s object
  -> (d object, CoverageWitness a s d) -> Bool
coverageResultCovers owner source (datum, witness) =
  coverageWitnessCovers owner source datum witness
