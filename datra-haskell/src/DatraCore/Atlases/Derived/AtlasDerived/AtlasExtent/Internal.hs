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
  , extentContainsRank
  , cellContainsRank
  , cellContainsRankImage
  , cellOriginRankPreimageSound
  , cellOriginRankMap
  , cellContainsRankPreserved
  , withAtlasCellAt
  ) where

import Atlas.Internal
  ( Atlas
  , atlasDataAt
  , atlasPageElements
  , atlasPageCell
  , atlasCompositionWitness
  , mapAtlasData
  )
import Data.Kind (Type)
import DatraOrdinal (Ordinal)
import Dominion (Dominion)
import DomanialInsertion.LiquidInternal
  ( DomanialInsertion (..)
  , rankImageInsertion
  , rankImagePreimageSound
  )
import Numeric.Natural (Natural)
import PageElements
  ( PageElement
  , PageElementArrow
  , pageElementArrow
  )
import PageElements.LiquidInternal
  ( SomePageElement (..)
  , arrowSource
  , arrowTarget
  , pageElementTransportedReflexive
  , somePageElementPrecedes
  , somePageElementTransported
  )
import qualified PageElements.Internal as Elements

-- | A dependent Atlas dominion whose page-element identity is hidden. This
-- is the Haskell presentation of Lean values such as @extent A@ and
-- @territory A k@, whose carrier types depend on the selected cell.
type role AtlasCellDominion nominal nominal
data AtlasCellDominion
  (scope :: Type)
  (cellData :: Type -> Type) where
  AtlasCellDominion
    :: (PageElement scope object, Dominion (cellData object))
    -> AtlasCellDominion scope cellData

-- | A named continuation for consuming a dependent Atlas dominion.
type AtlasCellDominionHandler scope cellData result =
  forall object.
    PageElement scope object
    -> Dominion (cellData object)
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
atlasExtent
  :: Atlas atlasScope scope cellData origin final
  -> AtlasCellDominion scope cellData
atlasExtent valueAtlas =
  case Elements.originPageElement (atlasPageElements valueAtlas) of
    SomePageElement origin ->
      AtlasCellDominion (origin, atlasDataAt valueAtlas origin)

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

-- | Resolve a dynamic page position and retain its checked origin arrow
-- while the caller consumes the existential cell identity.
-- ALIGN: ATLAS-CELL-LOOKUP-ORIGIN.
{-@ withAtlasCellAt
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> Natural -> Ordinal
      -> (forall object. source:{PageElement scope object | cellHasOrigin valueAtlas source}
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
      -> source:{PageElement scope object | cellHasOrigin valueAtlas source}
      -> DomanialInsertion (cellData object) Natural @-}
atlasCellOriginRankInsertion
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> DomanialInsertion (cellData object) Natural
atlasCellOriginRankInsertion valueAtlas source =
  case atlasExtent valueAtlas of
    AtlasCellDominion (origin, originDominion) ->
      rankImageInsertion originDominion
        (mapAtlasData valueAtlas (pageElementArrow source origin))

-- ALIGN: ATLAS-CELL-CONTAINS-RANK.
{-@ reflect cellContainsRank @-}
{-@ cellContainsRank
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> source:{PageElement scope object | cellHasOrigin valueAtlas source}
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
      -> source:{PageElement scope object | cellHasOrigin valueAtlas source}
      -> datum:cellData object
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
      -> source:{PageElement scope object | cellHasOrigin valueAtlas source}
      -> valueRank:Natural
      -> datum:{cellData object |
           preimage (atlasCellOriginRankInsertion valueAtlas source) valueRank == Just datum}
      -> {applyInsertion (atlasCellOriginRankInsertion valueAtlas source) datum == valueRank} @-}
cellOriginRankPreimageSound
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object -> Natural -> cellData object -> ()
cellOriginRankPreimageSound valueAtlas source valueRank datum =
  case atlasExtent valueAtlas of
    AtlasCellDominion (origin, originDominion) ->
      rankImagePreimageSound originDominion
        (mapAtlasData valueAtlas (pageElementArrow source origin)) valueRank datum

-- | Acting on a page arrow does not change a datum's image in the origin.
-- ALIGN: ATLAS-CELL-RANK-MAP.
{-@ cellOriginRankMap
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> arrow:{PageElementArrow scope source target |
           cellHasOrigin valueAtlas (arrowSource arrow)
           && cellHasOrigin valueAtlas (arrowTarget arrow)}
      -> datum:cellData source
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
           && cellHasOrigin valueAtlas (arrowTarget arrow)}
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
