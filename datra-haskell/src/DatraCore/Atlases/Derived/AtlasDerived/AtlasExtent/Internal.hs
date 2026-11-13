{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Hidden implementation of Atlas extents and dependent cell dominions.
module AtlasExtent.Internal
  ( AtlasCellDominion (..)
  , AtlasCellDominionHandler
  , atlasExtent
  , withAtlasCellDominion
  , atlasCellOriginRankInsertion
  , cellHasOrigin
  , cellTraceValid
  , extentContainsRank
  , cellContainsRank
  , cellContainsRankImage
  , cellOriginRankPreimageSound
  , cellOriginRankMap
  , cellContainsRankPreserved
  , cellContainsRankDisjoint
  , cellContainsRankInExtent
  , withAtlasCellAt
  ) where

import Atlas.Internal
  ( Atlas
  , atlasDataAt
  , atlasAcceptsDatum
  , atlasPageElements
  , atlasPageCell
  , atlasCompositionWitness
  , mapAtlasData
  )
import qualified Atlas.Internal as Atlas
import Data.Kind (Type)
import DatraOrdinal (Ordinal)
import Dominion.Internal (MembershipDominion (..), dominionCoherence)
import DomanialInsertion.LiquidInternal
  ( DomanialInsertion (..)
  , rankImageInsertion
  , rankImagePreimageSound
  )
import Numeric.Natural (Natural)
import PageElements
  ( PageElementArrow
  , pageElementArrow
  )
import PageElements.LiquidInternal
  ( PageElement (..)
  , SomePageElement (..)
  , arrowSource
  , arrowTarget
  , pageElementTransportedReflexive
  , somePageElementPrecedes
  , somePageElementTransported
  )
import qualified PageElements.Internal as Elements
import qualified PageElements.LiquidInternal as Trace

-- | A dependent Atlas dominion whose page-element identity is hidden. This
-- is the Haskell presentation of Lean values such as @extent A@ and
-- @territory A k@, whose carrier types depend on the selected cell.
type role AtlasCellDominion nominal nominal
data AtlasCellDominion
  (scope :: Type)
  (cellData :: Type -> Type) where
  AtlasCellDominion
    :: (PageElement scope object, MembershipDominion (cellData object))
    -> AtlasCellDominion scope cellData

{-@ reflect atlasCellDominionElement @-}
atlasCellDominionElement :: AtlasCellDominion scope cellData -> SomePageElement scope
atlasCellDominionElement (AtlasCellDominion (occurrence, _)) = SomePageElement occurrence

-- | A named continuation for consuming a dependent Atlas dominion.
type AtlasCellDominionHandler scope cellData result =
  forall object.
    PageElement scope object
    -> MembershipDominion (cellData object)
    -> result

-- | Eliminate the hidden page-element identity of an extent or territory.
withAtlasCellDominion
  :: AtlasCellDominion scope cellData
  -> AtlasCellDominionHandler scope cellData result
  -> result
withAtlasCellDominion
  (AtlasCellDominion (occurrence, valueDominion))
  useDominion = useDominion occurrence valueDominion

-- | The Atlas extent: the dominion attached to its origin cell.
-- ALIGN: ATLAS-EXTENT-INTERPRETATION.
{-@ reflect atlasExtent @-}
{-@ atlasExtent :: owner:Atlas atlasScope scope cellData origin final
      -> {result:AtlasCellDominion scope cellData |
           atlasCellDominionElement result == Elements.originPageElement (atlasPageElements owner)
           && Elements.somePageElementTraceValid (atlasPageElements owner) (atlasCellDominionElement result)} @-}
atlasExtent
  :: Atlas atlasScope scope cellData origin final
  -> AtlasCellDominion scope cellData
atlasExtent valueAtlas =
  case Elements.originPageElement (atlasPageElements valueAtlas) of
    SomePageElement origin ->
      AtlasCellDominion (origin, MembershipDominion
        (atlasAcceptsDatum valueAtlas origin) (atlasDataAt valueAtlas origin))

-- | The page-element evidence needed by the origin action. Valid folio
-- occurrences satisfy it; arbitrary raw traces do not.
-- ALIGN: ATLAS-CELL-HAS-ORIGIN.
{-@ reflect cellHasOrigin @-}
cellHasOrigin
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> Bool
cellHasOrigin valueAtlas source =
  let origin = Elements.originPageElement (atlasPageElements valueAtlas)
  in somePageElementPrecedes (SomePageElement source) origin
      && somePageElementTransported (SomePageElement source) origin

-- | The occurrence's entire trace agrees with lookup in its owning folio.
-- ALIGN: ATLAS-CELL-TRACE-VALIDITY.
{-@ reflect cellTraceValid @-}
cellTraceValid :: Atlas atlasScope scope cellData origin final -> PageElement scope object -> Bool
cellTraceValid valueAtlas source =
  Elements.pageElementTraceValid (atlasPageElements valueAtlas) source

-- | Resolve a dynamic page position and retain its checked origin arrow
-- while the caller consumes the existential cell identity.
-- ALIGN: ATLAS-CELL-LOOKUP-ORIGIN.
{-@ withAtlasCellAt
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> page:Natural -> position:Ordinal
      -> (forall object. source:{PageElement scope object | cellHasOrigin valueAtlas source
             && cellTraceValid valueAtlas source
             && pageElementPage source == page
             && pageElementPosition source == position
             && len (pageElementTrace source) == page + 1
             && Trace.traceStartsWith position (pageElementTrace source)}
            -> result)
      -> Maybe result @-}
withAtlasCellAt
  :: Atlas atlasScope scope cellData origin final
  -> Natural -> Ordinal
  -> (forall object. PageElement scope object -> result)
  -> Maybe result
withAtlasCellAt valueAtlas page position useCell =
  case Elements.pageElementIndex (atlasPageElements valueAtlas) page position of
    Nothing -> Nothing
    Just index ->
      Elements.withPageElement (atlasPageCell valueAtlas index) $ \source ->
        Just (useCell source)

-- | Use the extent's ranking for a cell's image, with a checked inverse on
-- all natural ranks, including ranks outside the cell's image.
-- ALIGN: ATLAS-CELL-ORIGIN-RANK-INSERTION.
{-@ reflect atlasCellOriginRankInsertion @-}
{-@ atlasCellOriginRankInsertion
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> source:{PageElement scope object | cellHasOrigin valueAtlas source && cellTraceValid valueAtlas source}
      -> DomanialInsertion ({datum:cellData object | atlasAcceptsDatum valueAtlas source datum}) Natural @-}
atlasCellOriginRankInsertion
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> DomanialInsertion (cellData object) Natural
atlasCellOriginRankInsertion valueAtlas source =
  case atlasExtent valueAtlas of
    AtlasCellDominion (origin, MembershipDominion _ originDominion) ->
      rankImageInsertion originDominion
        (mapAtlasData valueAtlas (pageElementArrow source origin))

-- ALIGN: ATLAS-CELL-CONTAINS-RANK.
{-@ reflect cellContainsRank @-}
{-@ cellContainsRank
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> source:{PageElement scope object | cellHasOrigin valueAtlas source && cellTraceValid valueAtlas source}
      -> Natural -> Bool @-}
cellContainsRank
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> Natural
  -> Bool
cellContainsRank valueAtlas source valueRank =
  case preimage (atlasCellOriginRankInsertion valueAtlas source) valueRank of
    Nothing -> False
    Just _ -> True

-- ALIGN: ATLAS-EXTENT-CONTAINS-RANK.
{-@ reflect extentContainsRank @-}
extentContainsRank
  :: Atlas atlasScope scope cellData origin final
  -> Natural
  -> Bool
extentContainsRank valueAtlas valueRank =
  case atlasExtent valueAtlas of
    AtlasCellDominion (origin, _) ->
      pageElementTransportedReflexive origin `seq`
        cellContainsRank valueAtlas origin valueRank

-- | The origin rank of every source datum is accepted by its cell.
-- ALIGN: ATLAS-CELL-CONTAINS-IMAGE.
{-@ cellContainsRankImage
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> source:{PageElement scope object | cellHasOrigin valueAtlas source && cellTraceValid valueAtlas source}
      -> datum:{cellData object | atlasAcceptsDatum valueAtlas source datum}
      -> {cellContainsRank valueAtlas source
            (applyInsertion (atlasCellOriginRankInsertion valueAtlas source) datum)} @-}
cellContainsRankImage
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object -> cellData object -> ()
cellContainsRankImage valueAtlas source datum =
  insertionLeftInverse (atlasCellOriginRankInsertion valueAtlas source) datum

-- | A successful optional inverse actually has the requested origin rank,
-- including when the queried rank lies outside the source cell's image.
-- ALIGN: ATLAS-CELL-RANK-PREIMAGE-SOUND.
{-@ cellOriginRankPreimageSound
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> source:{PageElement scope object | cellHasOrigin valueAtlas source && cellTraceValid valueAtlas source}
      -> valueRank:Natural
      -> datum:{cellData object |
           preimage (atlasCellOriginRankInsertion valueAtlas source) valueRank == Just datum
           && atlasAcceptsDatum valueAtlas source datum}
      -> {applyInsertion (atlasCellOriginRankInsertion valueAtlas source) datum == valueRank} @-}
cellOriginRankPreimageSound
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object -> Natural -> cellData object -> ()
cellOriginRankPreimageSound valueAtlas source valueRank datum =
  case atlasExtent valueAtlas of
    AtlasCellDominion (origin, MembershipDominion _ originDominion) ->
      rankImagePreimageSound originDominion
        (mapAtlasData valueAtlas (pageElementArrow source origin)) valueRank datum

-- | Acting on a page arrow does not change a datum's image in the origin.
-- ALIGN: ATLAS-CELL-RANK-MAP.
{-@ cellOriginRankMap
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> arrow:{PageElementArrow scope source target |
           cellHasOrigin valueAtlas (arrowSource arrow)
           && cellTraceValid valueAtlas (arrowSource arrow)
           && cellHasOrigin valueAtlas (arrowTarget arrow)
           && cellTraceValid valueAtlas (arrowTarget arrow)}
      -> datum:{cellData source | atlasAcceptsDatum valueAtlas (arrowSource arrow) datum}
      -> {applyInsertion (atlasCellOriginRankInsertion valueAtlas (arrowTarget arrow))
            (applyInsertion (mapAtlasData valueAtlas arrow) datum)
           == applyInsertion (atlasCellOriginRankInsertion valueAtlas (arrowSource arrow)) datum} @-}
cellOriginRankMap
  :: Atlas atlasScope scope cellData origin final
  -> PageElementArrow scope source target -> cellData source -> ()
cellOriginRankMap valueAtlas arrow datum =
  case atlasExtent valueAtlas of
    AtlasCellDominion (origin, _) ->
      atlasCompositionWitness valueAtlas
        (pageElementArrow (arrowTarget arrow) origin) arrow datum

-- | Every accepted source rank remains accepted after transport.
-- ALIGN: ATLAS-CELL-MEMBERSHIP-PRESERVED.
{-@ cellContainsRankPreserved
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> arrow:{PageElementArrow scope source target |
           cellHasOrigin valueAtlas (arrowSource arrow)
           && cellTraceValid valueAtlas (arrowSource arrow)
           && cellHasOrigin valueAtlas (arrowTarget arrow)
           && cellTraceValid valueAtlas (arrowTarget arrow)}
      -> valueRank:{Natural | cellContainsRank valueAtlas (arrowSource arrow) valueRank}
      -> {cellContainsRank valueAtlas (arrowTarget arrow) valueRank} @-}
cellContainsRankPreserved
  :: Atlas atlasScope scope cellData origin final
  -> PageElementArrow scope source target -> Natural -> ()
cellContainsRankPreserved valueAtlas arrow valueRank =
  case preimage (atlasCellOriginRankInsertion valueAtlas (arrowSource arrow)) valueRank of
    Nothing -> ()
    Just datum ->
      cellOriginRankPreimageSound valueAtlas (arrowSource arrow) valueRank datum `seq`
        cellOriginRankMap valueAtlas arrow datum `seq`
          cellContainsRankImage valueAtlas (arrowTarget arrow)
            (applyInsertion (mapAtlasData valueAtlas arrow) datum)

-- | Distinct cells on a genuine page cannot accept the same origin rank.
-- Successful inverses recover source data; the origin Dominion's coherence
-- turns equality of their ranks into equality of their origin images, which
-- contradicts the Atlas's stored disjointness law.
-- ALIGN: ATLAS-CELL-MEMBERSHIP-DISJOINT.
{-@ cellContainsRankDisjoint
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> left:{PageElement scope leftObject | cellHasOrigin valueAtlas left && cellTraceValid valueAtlas left
           && pageElementPage left < Atlas.atlasCardinality valueAtlas}
      -> right:{PageElement scope rightObject | cellHasOrigin valueAtlas right && cellTraceValid valueAtlas right
           && pageElementPage right == pageElementPage left
           && pageElementPosition right /= pageElementPosition left}
      -> valueRank:{Natural | cellContainsRank valueAtlas left valueRank}
      -> {not (cellContainsRank valueAtlas right valueRank)} @-}
cellContainsRankDisjoint
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope leftObject -> PageElement scope rightObject
  -> Natural -> ()
cellContainsRankDisjoint valueAtlas left right valueRank =
  case preimage (atlasCellOriginRankInsertion valueAtlas left) valueRank of
    Nothing -> ()
    Just leftDatum ->
      case preimage (atlasCellOriginRankInsertion valueAtlas right) valueRank of
        Nothing -> ()
        Just rightDatum ->
          case atlasExtent valueAtlas of
            AtlasCellDominion (origin, MembershipDominion _ originDominion) ->
              let leftArrow = pageElementArrow left origin
                  rightArrow = pageElementArrow right origin
              in cellOriginRankPreimageSound valueAtlas left valueRank leftDatum `seq`
                cellOriginRankPreimageSound valueAtlas right valueRank rightDatum `seq`
                dominionCoherence originDominion
                  (applyInsertion (mapAtlasData valueAtlas leftArrow) leftDatum) `seq`
                dominionCoherence originDominion
                  (applyInsertion (mapAtlasData valueAtlas rightArrow) rightDatum) `seq`
                Atlas.atlasDisjointWitness valueAtlas left right leftArrow rightArrow leftDatum rightDatum

-- | Every accepted cell rank belongs to the Atlas extent. This is the
-- component-to-origin branch of merge and sequence membership transport.
-- ALIGN: ATLAS-CELL-MEMBERSHIP-EXTENT.
{-@ cellContainsRankInExtent
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> source:{PageElement scope object | cellHasOrigin valueAtlas source && cellTraceValid valueAtlas source}
      -> valueRank:{Natural | cellContainsRank valueAtlas source valueRank}
      -> {extentContainsRank valueAtlas valueRank} @-}
cellContainsRankInExtent
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object -> Natural -> ()
cellContainsRankInExtent valueAtlas source valueRank =
  case atlasExtent valueAtlas of
    AtlasCellDominion (origin, _) ->
      pageElementTransportedReflexive origin `seq`
        cellContainsRankPreserved valueAtlas (pageElementArrow source origin) valueRank
