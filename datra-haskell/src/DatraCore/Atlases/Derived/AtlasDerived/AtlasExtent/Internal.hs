{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--higherorder" @-}

-- | Hidden implementation of Atlas extents and dependent cell dominions.
module AtlasExtent.Internal
  ( AtlasCellDominion (..)
  , AtlasCellDominionHandler
  , atlasExtent
  , atlasCellDominion
  , atlasCellDominionElement
  , withAtlasCellDominion
  , atlasCellOriginRankInsertion
  , atlasCellOriginRankAt
  , cellHasOrigin
  , cellTraceHasOrigin
  , cellTraceValid
  , cellNativeTrace
  , extentContainsRank
  , cellContainsRank
  , cellContainsRankImage
  , cellOriginRankPreimageSound
  , cellOriginRankMap
  , cellContainsRankPreserved
  , cellContainsRankDisjoint
  , cellContainsRankInExtent
  , withAtlasCellAt
  , withAtlasCellTrace
  , atlasCellAt
  , cellLookupTrace
  ) where

import Atlas
  ( Atlas
  , atlasDataAt
  , atlasAcceptsDatum
  , atlasPageElements
  , atlasPageCell
  , atlasCompositionWitness
  , mapAtlasData
  )
import qualified Atlas as Atlas
import Data.Kind (Type)
import DatraOrdinal (Ordinal)
import Dominion (MembershipDominion, membershipDominion, dominionCoherence, rank)
import DomanialInsertion.Core
  ( DomanialInsertion (..)
  , rankImageInsertion
  , rankImage
  , rankImagePreimageSound
  )
import Numeric.Natural (Natural)
import PageElements.Structure
  ( PageElementArrow
  , pageElementArrow
  )
import PageElements.Structure
  ( PageElement (..)
  , SomePageElement (..)
  , arrowSource
  , arrowTarget
  , pageElementTransportedReflexive
  , somePageElementPrecedes
  , somePageElementTransported
  )
import PageElements.TraceChain (pageTraceContains, traceHead, traceHeadMatches)
import qualified PageElements as Elements
import qualified PageElements.Structure as Trace

{-@ opaque-reflect rank @-}

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
{-@ ple atlasCellDominionElement @-}
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

-- | Package the actual dominion of a certified cell in its owning Atlas.
{-@ atlasCellDominion :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> {result:AtlasCellDominion s d |
           atlasCellDominionElement result == SomePageElement source
           && Elements.somePageElementTraceValid (atlasPageElements owner) (atlasCellDominionElement result)} @-}
{-@ ple atlasCellDominion @-}
atlasCellDominion :: Atlas a s d o f -> PageElement s object -> AtlasCellDominion s d
atlasCellDominion owner source =
  AtlasCellDominion (source, membershipDominion
    (atlasAcceptsDatum owner source) (atlasDataAt owner source))

-- | The Atlas extent: the dominion attached to its origin cell.
-- ALIGN: ATLAS-EXTENT-INTERPRETATION.
{-@ reflect atlasExtent @-}
{-@ atlasExtent :: owner:Atlas atlasScope scope cellData origin final
      -> {result:AtlasCellDominion scope cellData |
           atlasCellDominionElement result == Elements.originPageElement (atlasPageElements owner)
           && Elements.somePageElementTraceValid (atlasPageElements owner) (atlasCellDominionElement result)} @-}
{-@ ple atlasExtent @-}
atlasExtent
  :: Atlas atlasScope scope cellData origin final
  -> AtlasCellDominion scope cellData
atlasExtent valueAtlas =
  case Elements.originPageElement (atlasPageElements valueAtlas) of
    SomePageElement origin ->
      AtlasCellDominion (origin, membershipDominion
        (atlasAcceptsDatum valueAtlas origin) (atlasDataAt valueAtlas origin))

-- | The page-element evidence needed by the origin action. Valid folio
-- occurrences satisfy it; arbitrary raw traces do not.
-- ALIGN: ATLAS-CELL-HAS-ORIGIN.
{-@ reflect cellHasOrigin @-}
{-@ ple cellHasOrigin @-}
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
{-@ ple cellTraceValid @-}
cellTraceValid :: Atlas atlasScope scope cellData origin final -> PageElement scope object -> Bool
cellTraceValid valueAtlas source =
  Elements.pageElementTraceValid (atlasPageElements valueAtlas) source

-- | Valid owning traces carry the arrow needed by the origin insertion.
-- ALIGN: ATLAS-CELL-TRACE-HAS-ORIGIN.
{-@ cellTraceHasOrigin :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> {cellHasOrigin owner source} @-}
{-@ ple cellTraceHasOrigin @-}
cellTraceHasOrigin :: Atlas a s d o f -> PageElement s object -> ()
cellTraceHasOrigin owner source =
  Elements.pageElementTraceValidOrigin (atlasPageElements owner) source `seq`
    cellHasOrigin owner source `seq` ()

-- ALIGN: ATLAS-CELL-NATIVE-TRACE.
{-@ cellNativeTrace :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellTraceValid owner source}
      -> {pageTraceContains (Elements.pageElementsFolio (atlasPageElements owner))
           (pageElementPage source) (pageElementTrace source)} @-}
{-@ ple cellNativeTrace @-}
cellNativeTrace :: Atlas a s d o f -> PageElement s object -> ()
cellNativeTrace owner source =
  Elements.pageElementTraceValidShape (atlasPageElements owner) source `seq`
    traceHeadMatches (pageElementPosition source) (pageElementTrace source)

-- | Observe the entire optional trace without exposing the cell's phantom.
{-@ reflect cellLookupTrace @-}
{-@ ple cellLookupTrace @-}
cellLookupTrace :: Maybe (SomePageElement scope) -> Maybe [Ordinal]
cellLookupTrace Nothing = Nothing
cellLookupTrace (Just source) = Just (Trace.somePageElementTrace source)

-- | A first-order lookup value shared by the callbacks and membership proofs.
-- ALIGN: ATLAS-CELL-LOOKUP-VALUE.
-- ALIGN: ATLAS-CELL-LOOKUP-VALUE-TRACE.
{-@ opaque-reflect atlasCellAt @-}
{-@ atlasCellAt :: owner:Atlas atlasScope scope cellData origin final
      -> page:Natural -> position:Ordinal
      -> {resolved:Maybe ({source:SomePageElement scope |
           somePageElementPrecedes source (Elements.originPageElement (atlasPageElements owner))
           && somePageElementTransported source (Elements.originPageElement (atlasPageElements owner))
           && Elements.somePageElementTraceValid (atlasPageElements owner) source
           && Trace.somePageElementPage source == page
           && Trace.somePageElementPosition source == position
           && Elements.folioTraceLookup (Elements.pageElementsFolio (atlasPageElements owner)) page position
                == Just (Trace.somePageElementTrace source)
           && len (Trace.somePageElementTrace source) == page + 1
           && Trace.traceStartsWith position (Trace.somePageElementTrace source)}) |
             cellLookupTrace resolved
               == Elements.folioTraceLookup (Elements.pageElementsFolio (atlasPageElements owner)) page position
             && Elements.traceLookupPresent resolved == Elements.traceLookupPresent
                  (Elements.folioTraceLookup (Elements.pageElementsFolio (atlasPageElements owner)) page position)} @-}
{-@ ple atlasCellAt @-}
atlasCellAt :: Atlas atlasScope scope cellData origin final -> Natural -> Ordinal
  -> Maybe (SomePageElement scope)
atlasCellAt owner page position =
  case Elements.pageElementIndex (atlasPageElements owner) page position of
    Nothing -> Nothing
    Just index -> Just (atlasPageCell owner index)

-- | Recover the cell predicates without unfolding the owning Atlas in a callback.
{-@ cellEvidenceFromSome :: owner:Atlas a s d o f -> source:PageElement s object
      -> {cellHasOrigin owner source ==
            (somePageElementPrecedes (SomePageElement source) (Elements.originPageElement (atlasPageElements owner))
             && somePageElementTransported (SomePageElement source) (Elements.originPageElement (atlasPageElements owner)))
           && cellTraceValid owner source ==
                Elements.somePageElementTraceValid (atlasPageElements owner) (SomePageElement source)} @-}
{-@ ple cellEvidenceFromSome @-}
cellEvidenceFromSome :: Atlas a s d o f -> PageElement s object -> ()
cellEvidenceFromSome _ _ = ()

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
             && Trace.traceStartsWith position (pageElementTrace source)
             && Elements.folioTraceLookup (Elements.pageElementsFolio (atlasPageElements valueAtlas)) page position == Just (pageElementTrace source)}
            -> result)
      -> {resolved:Maybe result | Elements.traceLookupPresent resolved
           == Elements.traceLookupPresent (Elements.folioTraceLookup (Elements.pageElementsFolio (atlasPageElements valueAtlas)) page position)} @-}
withAtlasCellAt
  :: Atlas atlasScope scope cellData origin final
  -> Natural -> Ordinal
  -> (forall object. PageElement scope object -> result)
  -> Maybe result
withAtlasCellAt valueAtlas page position useCell =
  let resolved = atlasCellAt valueAtlas page position
  in case resolved of
    Nothing -> Elements.traceLookupPresent resolved `seq`
      Elements.traceLookupPresent (Nothing :: Maybe ()) `seq` Nothing
    Just selected -> Elements.withPageElement selected $ \source ->
      cellEvidenceFromSome valueAtlas source `seq`
      Elements.traceLookupPresent resolved `seq`
      let result = Just (useCell source)
      in Elements.traceLookupPresent result `seq` result

-- | Consume an accepted native trace without losing its exact cell evidence.
-- ALIGN: ATLAS-CELL-TRACE-RESOLUTION.
{-@ withAtlasCellTrace
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> page:Natural -> positions:{[Ordinal] | pageTraceContains (Elements.pageElementsFolio (atlasPageElements valueAtlas)) page positions}
      -> (forall object. source:{PageElement scope object | cellHasOrigin valueAtlas source
             && cellTraceValid valueAtlas source
             && pageElementPage source == page
             && pageElementPosition source == traceHead positions
             && pageElementTrace source == positions}
            -> result)
      -> {resolved:Maybe result | Elements.traceLookupPresent resolved} @-}
{-@ ple withAtlasCellTrace @-}
withAtlasCellTrace
  :: Atlas atlasScope scope cellData origin final -> Natural -> [Ordinal]
  -> (forall object. PageElement scope object -> result) -> Maybe result
withAtlasCellTrace valueAtlas page positions useCell =
  withAtlasCellAt valueAtlas page (traceHead positions) useCell

-- | Use the extent's ranking for a cell's image, with a checked inverse on
-- all natural ranks, including ranks outside the cell's image.
-- ALIGN: ATLAS-CELL-ORIGIN-RANK-INSERTION.
{-@ reflect atlasCellOriginRankInsertion @-}
{-@ atlasCellOriginRankInsertion
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> source:{PageElement scope object | cellHasOrigin valueAtlas source && cellTraceValid valueAtlas source}
      -> DomanialInsertion ({datum:cellData object | atlasAcceptsDatum valueAtlas source datum}) Natural @-}
{-@ ple atlasCellOriginRankInsertion @-}
atlasCellOriginRankInsertion
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> DomanialInsertion (cellData object) Natural
atlasCellOriginRankInsertion valueAtlas source =
  case Elements.originPageElement (atlasPageElements valueAtlas) of
    SomePageElement origin ->
      rankImageInsertion (atlasDataAt valueAtlas origin)
        (mapAtlasData valueAtlas (pageElementArrow source origin))

-- | Observe the origin encoding without exposing its existential implementation.
-- ALIGN: ATLAS-CELL-ORIGIN-RANK-AT.
{-@ ple atlasCellOriginRankAt @-}
{-@ atlasCellOriginRankAt :: owner:Atlas a s d o f
      -> source:{PageElement s object | cellHasOrigin owner source && cellTraceValid owner source}
      -> origin:{PageElement s originObject | cellTraceValid owner origin
           && SomePageElement origin == Elements.originPageElement (atlasPageElements owner)}
      -> datum:{d object | atlasAcceptsDatum owner source datum}
      -> {applyInsertion (atlasCellOriginRankInsertion owner source) datum
           == rank (atlasDataAt owner origin)
                (applyInsertion (mapAtlasData owner (pageElementArrow source origin)) datum)} @-}
atlasCellOriginRankAt :: Atlas a s d o f -> PageElement s object
  -> PageElement s originObject -> d object -> ()
atlasCellOriginRankAt owner source origin datum =
  rank (atlasDataAt owner origin)
    (applyInsertion (mapAtlasData owner (pageElementArrow source origin)) datum) `seq`
  atlasCellOriginRankInsertion owner source `seq` ()

-- ALIGN: ATLAS-CELL-CONTAINS-RANK.
{-@ reflect cellContainsRank @-}
{-@ cellContainsRank
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> source:{PageElement scope object | cellHasOrigin valueAtlas source && cellTraceValid valueAtlas source}
      -> Natural -> Bool @-}
{-@ ple cellContainsRank @-}
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
{-@ ple extentContainsRank @-}
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
{-@ ple cellContainsRankImage @-}
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
{-@ ple cellOriginRankPreimageSound @-}
cellOriginRankPreimageSound
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object -> Natural -> cellData object -> ()
cellOriginRankPreimageSound valueAtlas source valueRank datum =
  case Elements.originPageElement (atlasPageElements valueAtlas) of
    SomePageElement origin ->
      rankImagePreimageSound (atlasDataAt valueAtlas origin)
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
{-@ ple cellOriginRankMap @-}
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
{-@ ple cellContainsRankPreserved @-}
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

-- | Distinct cells on any full-spine page cannot accept the same origin rank.
-- Successful inverses recover source data; the origin Dominion's coherence
-- turns equality of their ranks into equality of their origin images, which
-- contradicts the Atlas's stored disjointness law.
-- ALIGN: ATLAS-CELL-MEMBERSHIP-DISJOINT.
{-@ cellContainsRankDisjoint
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> left:{PageElement scope leftObject | cellHasOrigin valueAtlas left && cellTraceValid valueAtlas left}
      -> right:{PageElement scope rightObject | cellHasOrigin valueAtlas right && cellTraceValid valueAtlas right
           && pageElementPage right == pageElementPage left
           && pageElementPosition right /= pageElementPosition left}
      -> valueRank:{Natural | cellContainsRank valueAtlas left valueRank}
      -> {not (cellContainsRank valueAtlas right valueRank)} @-}
{-@ ple cellContainsRankDisjoint @-}
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
          case Elements.originPageElement (atlasPageElements valueAtlas) of
            SomePageElement origin ->
              let originDominion = atlasDataAt valueAtlas origin
                  leftArrow = pageElementArrow left origin
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
{-@ ple cellContainsRankInExtent @-}
cellContainsRankInExtent
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object -> Natural -> ()
cellContainsRankInExtent valueAtlas source valueRank =
  case atlasExtent valueAtlas of
    AtlasCellDominion (origin, _) ->
      pageElementTransportedReflexive origin `seq`
        cellContainsRankPreserved valueAtlas (pageElementArrow source origin) valueRank
