-- | The ellipsis stable-confederal datum and its representing Atlas map.
module Ellipsis
  ( Ellipsis
  , EllipsisTerminal (Terminal)
  , terminalRank
  , ellipsis
  , ellipsisDominion
  , EllipsisAtlasObject
  , ellipsisAtlas
  , ellipsisAtlasMap
  , ellipsisCoalitionElement
  ) where

import Atlas
  ( Atlas
  , AtlasObject
  , atlasOriginCell
  , atlasPageElements
  )
import Atlas.Internal (atlasDataAction, atlasWithScope)
import AtlasCoveredPageElement (AtlasCoverageWitness, atlasCoverageWitness)
import AtlasMap (AtlasMap, atlasMap)
import Chain (chainIndexOf, spine)
import Coalition (CoalitionElement)
import Coalition.Internal (coalitionElement)
import Consolidation (consolidation, op)
import DatraOrdinal (naturalAtOrdinal)
import DomanialInclusion (singletonChain)
import DomanialInsertion (DomanialInsertion, domanialInsertion)
import Dominion (Dominion, dominion)
import Folio (Folio, appendPage, singletonFolio)
import Numeric.Natural (Natural)
import PageElements
  ( PageElement
  , PageElementArrow
  , arrowSource
  , arrowTarget
  , pageElementPage
  , pageElementPosition
  , withPageElement
  )
import PageElements.Internal (lastPageElement)
import Pagination (Pagination)
import Pagination.Internal (paginationWithScope)
import StableConfederalData
  ( EmbeddedAtlasMap
  , StableConfederalData
  , embedAtlasMap
  )

-- | A terminal region of Ellipsis, uniquely identified by its absolute rank.
newtype EllipsisTerminal = Terminal
  { terminalRank :: Natural
  }
  deriving (Eq, Show)

-- | Cell data in the representing Atlas. The extent carries the natural-rank
-- token, while every final region carries the very same singleton value. The
-- phantom parameter is the dependent identity of the cell occurrence.
data EllipsisCellData object
  = EllipsisExtentDatum EllipsisTerminal
  | EllipsisRegionDatum
  deriving (Eq, Show)

data EllipsisAtlasScope
data EllipsisPaginationScope

-- | The object name of the two-page Atlas representing Ellipsis.
type EllipsisAtlasObject =
  AtlasObject
    EllipsisAtlasScope
    EllipsisPaginationScope
    EllipsisCellData

-- | Ellipsis is the Yoneda embedding into @StaConfDa@ of its representing
-- Atlas map, regarded as a singleton stable Atlas confederation.
type Ellipsis = EmbeddedAtlasMap EllipsisAtlasObject

ellipsisFolio :: Folio () Natural
ellipsisFolio =
  appendPage
    (singletonFolio singletonChain)
    spine
    (op collapseSpine)
  where
    collapseSpine =
      consolidation
        (const ())
        (const 0)
        (\_ _ _ -> ())
        (const ())

ellipsisPagination :: Pagination EllipsisPaginationScope () Natural
ellipsisPagination = paginationWithScope ellipsisFolio

-- | The rank presentation is the extent dominion of the representing Atlas,
-- rather than Ellipsis itself.
ellipsisDominion :: Dominion EllipsisTerminal
ellipsisDominion = dominion terminalRank (Just . Terminal) (const ())

ellipsisCellDominion
  :: PageElement EllipsisPaginationScope object
  -> Dominion (EllipsisCellData object)
ellipsisCellDominion occurrence
  | pageElementPage occurrence == 0 =
      dominion
        extentDatumRank
        (Just . EllipsisExtentDatum . Terminal)
        (const ())
  | otherwise =
      dominion
        (const 0)
        (\valueRank ->
          if valueRank == 0 then Just EllipsisRegionDatum else Nothing)
        (const ())
  where
    extentDatumRank (EllipsisExtentDatum terminal) = terminalRank terminal
    extentDatumRank EllipsisRegionDatum = 0

ellipsisMapData
  :: PageElementArrow EllipsisPaginationScope source target
  -> DomanialInsertion
       (EllipsisCellData source)
       (EllipsisCellData target)
ellipsisMapData pageArrow
  | pageElementPage (arrowSource pageArrow) == 0 =
      domanialInsertion coerceCell (Just . coerceCell) (const ())
  | pageElementPage (arrowTarget pageArrow) == 0 =
      domanialInsertion regionToExtent extentToRegion (const ())
  | otherwise =
      domanialInsertion coerceCell (Just . coerceCell) (const ())
  where
    coerceCell (EllipsisExtentDatum terminal) = EllipsisExtentDatum terminal
    coerceCell EllipsisRegionDatum = EllipsisRegionDatum

    sourceRank =
      case naturalAtOrdinal (pageElementPosition (arrowSource pageArrow)) of
        Just value -> value
        Nothing -> error "Ellipsis region has a non-finite position"

    regionToExtent EllipsisRegionDatum =
      EllipsisExtentDatum (Terminal sourceRank)
    regionToExtent (EllipsisExtentDatum terminal) =
      EllipsisExtentDatum terminal

    extentToRegion (EllipsisExtentDatum (Terminal valueRank))
      | valueRank == sourceRank = Just EllipsisRegionDatum
      | otherwise = Nothing
    extentToRegion EllipsisRegionDatum = Just EllipsisRegionDatum

-- | The cardinality-two Atlas whose origin is the omega dominion and whose
-- final page is the omega chain of singleton (terminal) regions.
ellipsisAtlas
  :: Atlas
       EllipsisAtlasScope
       EllipsisPaginationScope
       EllipsisCellData
       ()
       Natural
ellipsisAtlas =
  atlasWithScope
    ellipsisPagination
    (atlasDataAction ellipsisCellDominion ellipsisMapData)
    (\_ _ -> ())
    (\_ _ _ _ -> ())
    (\_ _ _ _ -> ())
    (\_ _ _ _ _ _ _ -> ())

ellipsisCoverage
  :: PageElement EllipsisPaginationScope object
  -> EllipsisCellData object
  -> AtlasCoverageWitness EllipsisAtlasObject
ellipsisCoverage source datum =
  withPageElement
    (lastPageElement
      (atlasPageElements ellipsisAtlas)
      (chainIndexOf spine valueRank)) $ \region ->
        atlasCoverageWitness
          ellipsisAtlas source datum region EllipsisRegionDatum ()
  where
    valueRank =
      case datum of
        EllipsisExtentDatum terminal -> terminalRank terminal
        EllipsisRegionDatum ->
          case naturalAtOrdinal (pageElementPosition source) of
            Just value -> value
            Nothing -> error "Ellipsis region has a non-finite position"

-- | The representing Atlas restricted as an Atlas map: every origin datum is
-- covered by the singleton region at the same natural rank.
ellipsisAtlasMap :: AtlasMap EllipsisAtlasObject
ellipsisAtlasMap = atlasMap ellipsisAtlas ellipsisCoverage

-- | The canonical covered origin element at a rank. This identifies the
-- coalition of the representing Atlas with 'ellipsisDominion'.
ellipsisCoalitionElement
  :: EllipsisTerminal
  -> CoalitionElement EllipsisAtlasObject
ellipsisCoalitionElement terminal =
  withPageElement (atlasOriginCell ellipsisAtlas) $ \origin ->
    let datum = EllipsisExtentDatum terminal
    in coalitionElement origin datum (ellipsisCoverage origin datum)

-- | Ellipsis is the representable stable-confederal datum obtained by first
-- embedding its Atlas map as a singleton confederation and then applying
-- Yoneda.
ellipsis :: StableConfederalData Ellipsis
ellipsis = embedAtlasMap ellipsisAtlasMap
