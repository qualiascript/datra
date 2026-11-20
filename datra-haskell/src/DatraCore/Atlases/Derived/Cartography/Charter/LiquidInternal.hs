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

-- | Charted data with a canonical finite coverage code and checked carrier laws.
module Charter.LiquidInternal
  ( ChartedCellData
  , ChartedDatum
  , chartCellData
  , chartCounitInsertion
  , chartMapInsertion
  , chartedCellData
  , chartedCellDataValue
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
  ( DomanialInsertion, domanialInsertion, applyInsertion, preimage, insertionLeftInverse )
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

-- | Introduce a charted datum from checked coverage and retain its canonical code.
-- ALIGN: CHARTER-CELL-CONSTRUCTOR.
{-@ chartCellData :: owner:Atlas a s d o f -> occurrence:PageElement s object -> datum:d object
      -> witness:CoverageWitness a s d -> {proof:() | coverageWitnessCovers owner occurrence datum witness}
      -> {value:ChartedDatum a s d object |
           chartedCellDataValue value == datum
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

-- | The counit needs a partial inverse on every original datum. Searching for
-- coverage cannot supply that operation on uncovered data.
{-@
chartCounitInsertion
  :: backward:(d object -> Maybe (ChartedDatum a p d object))
  -> (charted:ChartedDatum a p d object ->
       {backward (chartedCellDataValue charted) == Just charted})
  -> DomanialInsertion (ChartedDatum a p d object) (d object)
@-}
-- ALIGN: CHARTER-COUNIT-INSERTION.
-- ALIGN: CHARTER-COUNIT-INTERPRETATION.
chartCounitInsertion
  :: (d object -> Maybe (ChartedDatum a p d object))
  -> (ChartedDatum a p d object -> ())
  -> DomanialInsertion (ChartedDatum a p d object) (d object)
chartCounitInsertion backward leftInverse =
  domanialInsertion chartedCellDataValue backward leftInverse

-- | Restrict a complete component to covered data. The source inverse checks
-- coverage of every candidate, including candidates outside the original image.
{-@
chartMapInsertion
  :: original:DomanialInsertion (sd sourceObject)
       (td targetObject)
  -> forward:(value:ChartedDatum sa ss sd sourceObject ->
       {result:ChartedDatum ta ts td targetObject |
         chartedCellDataValue result == applyInsertion original (chartedCellDataValue value)})
  -> backward:(sd sourceObject -> Maybe (ChartedDatum sa ss sd sourceObject))
  -> (charted:ChartedDatum sa ss sd sourceObject ->
       {backward (chartedCellDataValue charted) == Just charted})
  -> DomanialInsertion (ChartedDatum sa ss sd sourceObject) (ChartedDatum ta ts td targetObject)
@-}
-- ALIGN: CHARTER-MAP-INSERTION.
-- ALIGN: CHARTER-MAP-INVERSE.
chartMapInsertion
  :: forall sa ss sd sourceObject ta ts td targetObject.
     DomanialInsertion (sd sourceObject) (td targetObject)
  -> (ChartedDatum sa ss sd sourceObject -> ChartedDatum ta ts td targetObject)
  -> (sd sourceObject -> Maybe (ChartedDatum sa ss sd sourceObject))
  -> (ChartedDatum sa ss sd sourceObject -> ())
  -> DomanialInsertion (ChartedDatum sa ss sd sourceObject) (ChartedDatum ta ts td targetObject)
chartMapInsertion original forward backward leftInverse =
  domanialInsertion
    forward
    (chartMapPreimage @sa @ss @sd @sourceObject @ta @ts @td @targetObject original backward)
    (chartMapRoundTrip @sa @ss @sd @sourceObject @ta @ts @td @targetObject original forward backward leftInverse)

{-@ reflect chartMapPreimage @-}
chartMapPreimage
  :: forall sa ss sd sourceObject ta ts td targetObject. DomanialInsertion (sd sourceObject) (td targetObject)
  -> (sd sourceObject -> Maybe (ChartedDatum sa ss sd sourceObject))
  -> ChartedDatum ta ts td targetObject -> Maybe (ChartedDatum sa ss sd sourceObject)
chartMapPreimage original backward value =
  case preimage original (chartedCellDataValue value) of
    Nothing -> Nothing
    Just candidate -> backward candidate

{-@ chartMapRoundTrip
      :: original:DomanialInsertion (sd sourceObject) (td targetObject)
      -> forward:(value:ChartedDatum sa ss sd sourceObject ->
           {result:ChartedDatum ta ts td targetObject |
             chartedCellDataValue result == applyInsertion original (chartedCellDataValue value)})
      -> backward:(sd sourceObject -> Maybe (ChartedDatum sa ss sd sourceObject))
      -> (charted:ChartedDatum sa ss sd sourceObject -> {backward (chartedCellDataValue charted) == Just charted})
      -> value:ChartedDatum sa ss sd sourceObject
      -> {chartMapPreimage original backward (forward value) == Just value} @-}
chartMapRoundTrip
  :: forall sa ss sd sourceObject ta ts td targetObject.
     DomanialInsertion (sd sourceObject) (td targetObject)
  -> (ChartedDatum sa ss sd sourceObject -> ChartedDatum ta ts td targetObject)
  -> (sd sourceObject -> Maybe (ChartedDatum sa ss sd sourceObject))
  -> (ChartedDatum sa ss sd sourceObject -> ())
  -> ChartedDatum sa ss sd sourceObject -> ()
chartMapRoundTrip original forward _ leftInverse value =
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
