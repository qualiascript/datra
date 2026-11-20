{-# LANGUAGE CPP #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
-- GHC does not count imports referenced only by refinement signatures.
{-# OPTIONS_GHC -Wno-unused-top-binds -Wno-unused-imports #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
{-@ qualif ChartedAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | Charted data with a canonical finite coverage code and checked carrier laws.
module Charter.LiquidInternal
  ( ChartedCellData
  , ChartedDatum
  , chartCellData
  , chartCounitInsertion
  , chartMapInsertion
  , chartedCellData
  , chartedCellDataValue
  , chartedDatumValid
  , chartedCellDataRank
  , chartedCellCoverage
  , chartedCellDataEqual
  , chartedDataMap
  , charterIdentityValue
  , charterCompositionValue
  , chartHomToValue
  , chartHomFromValue
  , chartHomLeftInverseValue
  , chartHomRightInverseValue
  , chartHomNaturalityLeftValue
  , chartHomNaturalityRightValue
  ) where

import Atlas (Atlas, AtlasObject, AtlasObjectCellData, AtlasObjectAtlasScope, AtlasObjectPaginationScope, atlasAcceptsDatum, mapAtlasData)
import AtlasExtent (cellTraceValid)
import AtlasCoveredPageElement
  ( CoverageWitness, coverageWitnessCovers, atlasCoverageRank, coverageRankCandidate
  , coverageRankCanonical, coverageRankCanonicalUnique, coverageRankWitness, coverageRankAlongArrow )
import Numeric.Natural (Natural)
import DomanialInsertion.Core
  ( DomanialInsertion (..), domanialInsertion )
import PageElements.Structure (PageElement, PageElementArrow, arrowSource, arrowTarget)
import Data.Kind (Type)

-- | A covered datum and the unique least code of its final-region enumeration.
-- The constructor is hidden; public introduction checks coverage before ranking.
type ChartedCellData atlasObject =
  ChartedDatum (AtlasObjectAtlasScope atlasObject) (AtlasObjectPaginationScope atlasObject)
    (AtlasObjectCellData atlasObject)

type role ChartedDatum nominal nominal nominal nominal
data ChartedDatum (atlasScope :: Type) (scope :: Type) (cellData :: Type -> Type) (object :: Type) =
  ChartedCellData (cellData object) Natural

{-@ reflect chartedCellDataValue @-}
chartedCellDataValue :: ChartedDatum a s d object -> d object
chartedCellDataValue (ChartedCellData value _) = value

{-@ reflect chartedCellDataRank @-}
chartedCellDataRank :: ChartedDatum a s d object -> Natural
chartedCellDataRank (ChartedCellData _ code) = code

{-@ reflect chartedCellData @-}
chartedCellData :: d object -> Natural -> ChartedDatum a s d object
chartedCellData = ChartedCellData

-- | Membership of the charted carrier checks both the datum and its cache.
-- ALIGN: CHARTER-CELL-MEMBERSHIP.
{-@ reflect chartedDatumValid @-}
chartedDatumValid :: Atlas a s d o f -> PageElement s object -> ChartedDatum a s d object -> Bool
chartedDatumValid owner occurrence value =
  if cellTraceValid owner occurrence then
    if atlasAcceptsDatum owner occurrence (chartedCellDataValue value) then
      coverageRankCandidate owner occurrence (chartedCellDataValue value) (chartedCellDataRank value)
        && coverageRankCanonical owner occurrence (chartedCellDataValue value) (chartedCellDataRank value)
    else False
  else False

-- | Introduce a charted datum from checked coverage and retain its canonical code.
-- ALIGN: CHARTER-CELL-CONSTRUCTOR.
{-@ chartCellData :: owner:Atlas a s d o f -> occurrence:PageElement s object -> datum:d object
      -> witness:CoverageWitness a s d -> {proof:() | coverageWitnessCovers owner occurrence datum witness}
      -> {value:ChartedDatum a s d object |
           chartedCellDataValue value == datum
           && chartedDatumValid owner occurrence value
           && coverageRankCandidate owner occurrence datum (chartedCellDataRank value)
           && coverageRankCanonical owner occurrence datum (chartedCellDataRank value)} @-}
chartCellData
  :: Atlas a s d o f -> PageElement s object -> d object -> CoverageWitness a s d -> ()
  -> ChartedDatum a s d object
chartCellData owner occurrence datum witness proof =
  proof `seq` chartedCellData datum (atlasCoverageRank owner occurrence datum witness)

-- | Recover evidence from the stored successful code, with no witness search.
-- ALIGN: CHARTER-CELL-COVERAGE-CACHE.
{-@ chartedCellCoverage :: owner:Atlas a s d o f
      -> occurrence:{PageElement s object | cellTraceValid owner occurrence}
      -> value:{ChartedDatum a s d object |
           atlasAcceptsDatum owner occurrence (chartedCellDataValue value)
           && coverageRankCandidate owner occurrence (chartedCellDataValue value) (chartedCellDataRank value)}
      -> {witness:CoverageWitness a s d | coverageWitnessCovers owner occurrence (chartedCellDataValue value) witness} @-}
chartedCellCoverage
  :: Atlas a s d o f -> PageElement s object -> ChartedDatum a s d object -> CoverageWitness a s d
chartedCellCoverage owner occurrence value =
  case coverageRankWitness owner occurrence (chartedCellDataValue value) (chartedCellDataRank value) of
    Just witness -> witness
    Nothing -> error "chartedCellCoverage: invalid certified code"

-- | Canonical codes make equality depend only on the accepted datum.
-- ALIGN: CHARTER-CELL-CACHE-EXTENSIONALITY.
{-@ chartedCellDataEqual :: owner:Atlas a s d o f
      -> occurrence:{PageElement s object | cellTraceValid owner occurrence}
      -> left:{ChartedDatum a s d object |
           atlasAcceptsDatum owner occurrence (chartedCellDataValue left)
           && coverageRankCanonical owner occurrence (chartedCellDataValue left) (chartedCellDataRank left)}
      -> right:{ChartedDatum a s d object |
           chartedCellDataValue right == chartedCellDataValue left
           && coverageRankCanonical owner occurrence (chartedCellDataValue right) (chartedCellDataRank right)}
      -> {left == right} @-}
chartedCellDataEqual
  :: Atlas a s d o f -> PageElement s object -> ChartedDatum a s d object
  -> ChartedDatum a s d object -> ()
chartedCellDataEqual owner occurrence (ChartedCellData left leftCode) (ChartedCellData _ rightCode) =
  coverageRankCanonicalUnique owner occurrence left leftCode rightCode

-- | Retain carrier predicates while packaging higher-kinded callbacks.
{-@ insertionOn :: acceptsSource:(a -> Bool) -> acceptsTarget:(b -> Bool)
      -> forward:({x:a | acceptsSource x} -> {y:b | acceptsTarget y})
      -> backward:({y:b | acceptsTarget y} -> Maybe ({x:a | acceptsSource x}))
      -> (x:{a | acceptsSource x} -> {backward (forward x) == Just x})
      -> DomanialInsertion ({x:a | acceptsSource x}) ({y:b | acceptsTarget y}) @-}
insertionOn :: (a -> Bool) -> (b -> Bool) -> (a -> b) -> (b -> Maybe a) -> (a -> ())
  -> DomanialInsertion a b
insertionOn _ _ = domanialInsertion

{-@ reflect chartedAcceptedValue @-}
{-@ chartedAcceptedValue :: owner:Atlas a s d o f -> occurrence:PageElement s object
      -> value:{ChartedDatum a s d object | chartedDatumValid owner occurrence value}
      -> {datum:d object | datum == chartedCellDataValue value && atlasAcceptsDatum owner occurrence datum} @-}
chartedAcceptedValue :: Atlas a s d o f -> PageElement s object -> ChartedDatum a s d object -> d object
chartedAcceptedValue _ _ value = chartedCellDataValue value

-- | The inverse is total on original accepted data and recovers every member
-- of the canonical charted carrier. Uncovered inputs may return Nothing.
-- ALIGN: CHARTER-COUNIT-INSERTION.
-- ALIGN: CHARTER-COUNIT-INTERPRETATION.
{-@ chartCounitInsertion
      :: owner:Atlas a s d o f
      -> occurrence:{PageElement s object | cellTraceValid owner occurrence}
      -> backward:({datum:d object | atlasAcceptsDatum owner occurrence datum}
           -> Maybe ({value:ChartedDatum a s d object | chartedDatumValid owner occurrence value}))
      -> (value:{ChartedDatum a s d object | chartedDatumValid owner occurrence value}
           -> {backward (chartedCellDataValue value) == Just value})
      -> DomanialInsertion
           ({value:ChartedDatum a s d object | chartedDatumValid owner occurrence value})
           ({datum:d object | atlasAcceptsDatum owner occurrence datum}) @-}
chartCounitInsertion
  :: Atlas a s d o f -> PageElement s object
  -> (d object -> Maybe (ChartedDatum a s d object))
  -> (ChartedDatum a s d object -> ())
  -> DomanialInsertion (ChartedDatum a s d object) (d object)
chartCounitInsertion owner occurrence backward leftInverse =
  insertionOn (chartedDatumValid owner occurrence) (atlasAcceptsDatum owner occurrence)
    (chartedAcceptedValue owner occurrence) backward
    (\value -> chartedAcceptedValue owner occurrence value `seq` leftInverse value)

-- | Restrict a complete component to the canonical covered carriers.
-- ALIGN: CHARTER-MAP-INSERTION.
-- ALIGN: CHARTER-MAP-INVERSE.
{-@ chartMapInsertion
      :: sourceAtlas:Atlas sa ss sd so sf
      -> source:{PageElement ss sourceObject | cellTraceValid sourceAtlas source}
      -> targetAtlas:Atlas ta ts td to tf
      -> target:{PageElement ts targetObject | cellTraceValid targetAtlas target}
      -> original:DomanialInsertion
           ({datum:sd sourceObject | atlasAcceptsDatum sourceAtlas source datum})
           ({datum:td targetObject | atlasAcceptsDatum targetAtlas target datum})
      -> forward:(value:{ChartedDatum sa ss sd sourceObject | chartedDatumValid sourceAtlas source value} ->
           {result:ChartedDatum ta ts td targetObject | chartedDatumValid targetAtlas target result
             && chartedCellDataValue result == applyInsertion original (chartedCellDataValue value)})
      -> backward:({datum:sd sourceObject | atlasAcceptsDatum sourceAtlas source datum}
           -> Maybe ({value:ChartedDatum sa ss sd sourceObject | chartedDatumValid sourceAtlas source value}))
      -> (value:{ChartedDatum sa ss sd sourceObject | chartedDatumValid sourceAtlas source value}
           -> {backward (chartedCellDataValue value) == Just value})
      -> DomanialInsertion
           ({value:ChartedDatum sa ss sd sourceObject | chartedDatumValid sourceAtlas source value})
           ({value:ChartedDatum ta ts td targetObject | chartedDatumValid targetAtlas target value}) @-}
chartMapInsertion
  :: Atlas sa ss sd so sf -> PageElement ss sourceObject
  -> Atlas ta ts td to tf -> PageElement ts targetObject
  -> DomanialInsertion (sd sourceObject) (td targetObject)
  -> (ChartedDatum sa ss sd sourceObject -> ChartedDatum ta ts td targetObject)
  -> (sd sourceObject -> Maybe (ChartedDatum sa ss sd sourceObject))
  -> (ChartedDatum sa ss sd sourceObject -> ())
  -> DomanialInsertion (ChartedDatum sa ss sd sourceObject) (ChartedDatum ta ts td targetObject)
chartMapInsertion sourceAtlas source targetAtlas target original forward backward leftInverse =
  insertionOn (chartedDatumValid sourceAtlas source) (chartedDatumValid targetAtlas target) forward
    (chartMapPreimage sourceAtlas source targetAtlas target original backward)
    (chartMapRoundTrip sourceAtlas source targetAtlas target original forward backward leftInverse)

{-@ reflect chartMapPreimage @-}
{-@ chartMapPreimage
      :: sourceAtlas:Atlas sa ss sd so sf
      -> source:{PageElement ss sourceObject | cellTraceValid sourceAtlas source}
      -> targetAtlas:Atlas ta ts td to tf
      -> target:{PageElement ts targetObject | cellTraceValid targetAtlas target}
      -> original:DomanialInsertion
           ({datum:sd sourceObject | atlasAcceptsDatum sourceAtlas source datum})
           ({datum:td targetObject | atlasAcceptsDatum targetAtlas target datum})
      -> backward:({datum:sd sourceObject | atlasAcceptsDatum sourceAtlas source datum}
           -> Maybe ({value:ChartedDatum sa ss sd sourceObject | chartedDatumValid sourceAtlas source value}))
      -> value:{ChartedDatum ta ts td targetObject | chartedDatumValid targetAtlas target value}
      -> Maybe ({result:ChartedDatum sa ss sd sourceObject | chartedDatumValid sourceAtlas source result}) @-}
chartMapPreimage
  :: Atlas sa ss sd so sf -> PageElement ss sourceObject
  -> Atlas ta ts td to tf -> PageElement ts targetObject
  -> DomanialInsertion (sd sourceObject) (td targetObject)
  -> (sd sourceObject -> Maybe (ChartedDatum sa ss sd sourceObject))
  -> ChartedDatum ta ts td targetObject -> Maybe (ChartedDatum sa ss sd sourceObject)
chartMapPreimage _ _ _ _ original backward value =
  case preimage original (chartedCellDataValue value) of
    Nothing -> Nothing
    Just candidate -> backward candidate

{-@ chartMapRoundTrip
      :: sourceAtlas:Atlas sa ss sd so sf
      -> source:{PageElement ss sourceObject | cellTraceValid sourceAtlas source}
      -> targetAtlas:Atlas ta ts td to tf
      -> target:{PageElement ts targetObject | cellTraceValid targetAtlas target}
      -> original:DomanialInsertion
           ({datum:sd sourceObject | atlasAcceptsDatum sourceAtlas source datum})
           ({datum:td targetObject | atlasAcceptsDatum targetAtlas target datum})
      -> forward:(value:{ChartedDatum sa ss sd sourceObject | chartedDatumValid sourceAtlas source value} ->
           {result:ChartedDatum ta ts td targetObject | chartedDatumValid targetAtlas target result
             && chartedCellDataValue result == applyInsertion original (chartedCellDataValue value)})
      -> backward:({datum:sd sourceObject | atlasAcceptsDatum sourceAtlas source datum}
           -> Maybe ({value:ChartedDatum sa ss sd sourceObject | chartedDatumValid sourceAtlas source value}))
      -> (value:{ChartedDatum sa ss sd sourceObject | chartedDatumValid sourceAtlas source value}
           -> {backward (chartedCellDataValue value) == Just value})
      -> value:{ChartedDatum sa ss sd sourceObject | chartedDatumValid sourceAtlas source value}
      -> {chartMapPreimage sourceAtlas source targetAtlas target original backward (forward value) == Just value} @-}
chartMapRoundTrip
  :: Atlas sa ss sd so sf -> PageElement ss sourceObject
  -> Atlas ta ts td to tf -> PageElement ts targetObject
  -> DomanialInsertion (sd sourceObject) (td targetObject)
  -> (ChartedDatum sa ss sd sourceObject -> ChartedDatum ta ts td targetObject)
  -> (sd sourceObject -> Maybe (ChartedDatum sa ss sd sourceObject))
  -> (ChartedDatum sa ss sd sourceObject -> ())
  -> ChartedDatum sa ss sd sourceObject -> ()
chartMapRoundTrip _ _ _ _ original forward _ leftInverse value =
  forward value `seq`
    insertionLeftInverse original (chartedCellDataValue value) `seq` leftInverse value

-- | Transport an accepted charted datum and its certified code together.
-- ALIGN: CHARTER-CELL-CACHE-TRANSPORT.
{-@ chartedDataMap :: owner:Atlas a s d o f
      -> arrow:{PageElementArrow s source target |
           cellTraceValid owner (arrowSource arrow) && cellTraceValid owner (arrowTarget arrow)}
      -> value:{ChartedDatum a s d source |
           atlasAcceptsDatum owner (arrowSource arrow) (chartedCellDataValue value)
           && coverageRankCandidate owner (arrowSource arrow) (chartedCellDataValue value) (chartedCellDataRank value)
           && coverageRankCanonical owner (arrowSource arrow) (chartedCellDataValue value) (chartedCellDataRank value)}
      -> {result:ChartedDatum a s d target |
           chartedCellDataValue result == applyInsertion (mapAtlasData owner arrow) (chartedCellDataValue value)
           && chartedCellDataRank result == chartedCellDataRank value
           && atlasAcceptsDatum owner (arrowTarget arrow) (chartedCellDataValue result)
           && coverageRankCandidate owner (arrowTarget arrow) (chartedCellDataValue result) (chartedCellDataRank result)
           && coverageRankCanonical owner (arrowTarget arrow) (chartedCellDataValue result) (chartedCellDataRank result)} @-}
chartedDataMap :: Atlas a s d o f -> PageElementArrow s source target
  -> ChartedDatum a s d source -> ChartedDatum a s d target
chartedDataMap owner arrow (ChartedCellData value code) =
  coverageRankAlongArrow owner arrow value code `seq`
    ChartedCellData (applyInsertion (mapAtlasData owner arrow) value) code

{-@ reflect composeValues @-}
composeValues :: (b -> c) -> (a -> b) -> a -> c
composeValues after before value = after (before value)

{-@ reflect identityValue @-}
identityValue :: a -> a
identityValue value = value

-- | Across Atlas objects, the target supplies its own canonical rank function.
{-@ reflect recodeChartedCellData @-}
recodeChartedCellData
  :: (sd sourceObject -> td targetObject)
  -> (td targetObject -> Natural)
  -> ChartedDatum sa ss sd sourceObject -> ChartedDatum ta ts td targetObject
recodeChartedCellData function code value =
  let target = function (chartedCellDataValue value)
  in ChartedCellData target (code target)

-- ALIGN: CHARTER-FUNCTOR-IDENTITY.
{-@ charterIdentityValue :: code:(d object -> Natural)
      -> value:{ChartedDatum a p d object | code (chartedCellDataValue value) == chartedCellDataRank value}
      -> {recodeChartedCellData identityValue code value == value} @-}
charterIdentityValue
  :: (d object -> Natural) -> ChartedDatum a p d object -> ()
charterIdentityValue _ (ChartedCellData _ _) = ()

-- ALIGN: CHARTER-FUNCTOR-COMPOSITION.
{-@ charterCompositionValue
      :: first:(sd sourceObject -> md middleObject)
      -> second:(md middleObject -> td targetObject)
      -> middleCode:(md middleObject -> Natural)
      -> targetCode:(td targetObject -> Natural)
      -> value:ChartedDatum sa ss sd sourceObject
      -> {recodeChartedCellData second targetCode (recodeChartedCellData first middleCode value)
           == recodeChartedCellData (composeValues second first) targetCode value} @-}
charterCompositionValue
  :: forall sa ss sd sourceObject ma ms md middleObject ta ts td targetObject.
     (sd sourceObject -> md middleObject)
  -> (md middleObject -> td targetObject)
  -> (md middleObject -> Natural)
  -> (td targetObject -> Natural)
  -> ChartedDatum sa ss sd sourceObject -> ()
charterCompositionValue _ _ _ _ _ = ()

-- | Data component of @chartLift@: apply the original component and retain
-- its covered result in the charted target.
{-@ reflect chartHomToValue @-}
chartHomToValue
  :: (sourceValue -> td targetObject)
  -> (td targetObject -> Natural)
  -> sourceValue
  -> ChartedDatum ta ts td targetObject
chartHomToValue function code value = ChartedCellData (function value) (code (function value))

-- | Data component of composition with the chart counit.
{-@ reflect chartHomFromValue @-}
chartHomFromValue
  :: (sourceValue -> ChartedDatum ta ts td targetObject)
  -> sourceValue
  -> td targetObject
chartHomFromValue function value =
  chartedCellDataValue (function value)

-- | Forgetting a lifted value recovers the original datum.
-- ALIGN: CHARTER-HOM-LEFT-INVERSE.
{-@ chartHomLeftInverseValue
      :: function:(sourceValue -> td targetObject)
      -> code:(td targetObject -> Natural) -> value:sourceValue
      -> {chartHomFromValue (chartHomToValue function code) value == function value} @-}
chartHomLeftInverseValue
  :: forall sourceValue ta ts td targetObject.
     (sourceValue -> td targetObject)
  -> (td targetObject -> Natural) -> sourceValue -> ()
chartHomLeftInverseValue _ _ _ = ()

-- | Reconstructing a canonical code recovers the complete charted value.
-- ALIGN: CHARTER-HOM-RIGHT-INVERSE.
{-@ chartHomRightInverseValue
      :: function:(sourceValue -> ChartedDatum ta ts td targetObject)
      -> code:(td targetObject -> Natural)
      -> (value:sourceValue -> {code (chartedCellDataValue (function value)) == chartedCellDataRank (function value)})
      -> value:sourceValue
      -> {chartHomToValue (chartHomFromValue function) code value == function value} @-}
chartHomRightInverseValue
  :: forall sourceValue ta ts td targetObject.
     (sourceValue -> ChartedDatum ta ts td targetObject)
  -> (td targetObject -> Natural) -> (sourceValue -> ()) -> sourceValue -> ()
chartHomRightInverseValue function _ canonical value =
  canonical value `seq` case function value of ChartedCellData _ _ -> ()

-- ALIGN: CHARTER-HOM-NATURALITY-LEFT.
{-@ chartHomNaturalityLeftValue
      :: before:(firstValue -> secondValue)
      -> function:(secondValue -> td targetObject)
      -> code:(td targetObject -> Natural) -> value:firstValue
      -> {chartHomToValue (composeValues function before) code value == chartHomToValue function code (before value)} @-}
chartHomNaturalityLeftValue
  :: forall firstValue secondValue ta ts td targetObject.
     (firstValue -> secondValue) -> (secondValue -> td targetObject)
  -> (td targetObject -> Natural) -> firstValue -> ()
chartHomNaturalityLeftValue _ _ _ _ = ()

-- | Recoding in the target makes naturality independent of intermediate codes.
-- ALIGN: CHARTER-HOM-NATURALITY-RIGHT.
{-@ chartHomNaturalityRightValue
      :: function:(sourceValue -> md middleObject)
      -> after:(md middleObject -> td targetObject)
      -> middleCode:(md middleObject -> Natural)
      -> targetCode:(td targetObject -> Natural)
      -> value:sourceValue
      -> {chartHomToValue (composeValues after function) targetCode value
           == recodeChartedCellData after targetCode (chartHomToValue function middleCode value)} @-}
chartHomNaturalityRightValue
  :: forall sourceValue ma ms md middleObject ta ts td targetObject.
     (sourceValue -> md middleObject)
  -> (md middleObject -> td targetObject)
  -> (md middleObject -> Natural)
  -> (td targetObject -> Natural)
  -> sourceValue -> ()
chartHomNaturalityRightValue _ _ _ _ _ = ()
