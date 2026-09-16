{-# LANGUAGE TypeFamilies #-}

-- | The canonical two-page Atlas map that separates a dominion by rank.
--
-- The extent carries the supplied dominion.  Final page position @n@ carries
-- the singleton datum whose dominion rank is @n@ (or no datum when that rank
-- is absent).  This is the reusable DatraCore construction underlying
-- Ellipsis-like ranked maps.
module RankedDominionAtlas
  ( RankedDominionCellData
  , RankedDominionAtlasObject
  , rankedDominionAtlas
  , rankedDominionAtlasMap
  , rankedDominionCoalitionElement
  , rankedDominionInsertionTraversal
  ) where

import Atlas
  ( Atlas
  , AtlasObject
  , atlasOriginCell
  , atlasPageElements
  , atlasWitness
  )
import Atlas.Internal (atlasDataAction, atlasWithScope)
import AtlasCoveredPageElement
  ( AtlasCoverageWitness
  , atlasCoverageWitness
  )
import AtlasMap (AtlasMap, atlasMap)
import Chain (chainIndexOf, spine)
import Coalition (CoalitionElement, coalitionElementRank)
import Coalition.Internal (coalitionElement)
import Consolidation (consolidation, op)
import DatraOrdinal (Ordinal, naturalAtOrdinal)
import DomanialInclusion
  ( DominionAtlasObject
  , coaToDomInc
  , singletonChain
  )
import DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , domanialInsertion
  , insertionLeftInverse
  , preimage
  , pullbackDominion
  )
import Dominion (Dominion, dominion, rank, unrank)
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
import StableAtlasTransversal (StableAtlasTransversal)

-- | Data carried by the extent or by one rank-selected final region.
data RankedDominionCellData value object
  = RankedDominionExtentDatum value
  | RankedDominionRegionDatum value
  deriving (Eq, Show)

data RankedDominionAtlasScope value
data RankedDominionPaginationScope value

type RankedDominionAtlasObject value =
  AtlasObject
    (RankedDominionAtlasScope value)
    (RankedDominionPaginationScope value)
    (RankedDominionCellData value)

rankedDominionFolio :: Folio () Natural
rankedDominionFolio =
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

rankedDominionPagination
  :: Pagination (RankedDominionPaginationScope value) () Natural
rankedDominionPagination = paginationWithScope rankedDominionFolio

rankedDominionAt
  :: Dominion value
  -> PageElement (RankedDominionPaginationScope value) object
  -> Dominion (RankedDominionCellData value object)
rankedDominionAt valueDominion occurrence
  | pageElementPage occurrence == 0 =
      dominion
        (rank valueDominion . cellValue)
        (fmap RankedDominionExtentDatum . unrank valueDominion)
        (const ())
  | otherwise =
      dominion
        (const 0)
        (\valueRank ->
          if valueRank == 0
            then RankedDominionRegionDatum
              <$> unrank valueDominion occurrenceRank
            else Nothing)
        (const ())
  where
    cellValue (RankedDominionExtentDatum value) = value
    cellValue (RankedDominionRegionDatum value) = value

    occurrenceRank =
      spineRank (pageElementPosition occurrence)

rankedDominionDataMap
  :: Dominion value
  -> PageElementArrow
       (RankedDominionPaginationScope value) source target
  -> DomanialInsertion
       (RankedDominionCellData value source)
       (RankedDominionCellData value target)
rankedDominionDataMap valueDominion pageArrow
  | pageElementPage (arrowSource pageArrow) == 0 =
      domanialInsertion coerceCell (Just . coerceCell) (const ())
  | pageElementPage (arrowTarget pageArrow) == 0 =
      domanialInsertion regionToExtent extentToRegion (const ())
  | otherwise =
      domanialInsertion coerceCell (Just . coerceCell) (const ())
  where
    coerceCell (RankedDominionExtentDatum value) =
      RankedDominionExtentDatum value
    coerceCell (RankedDominionRegionDatum value) =
      RankedDominionRegionDatum value

    sourceRank =
      spineRank (pageElementPosition (arrowSource pageArrow))

    regionToExtent (RankedDominionRegionDatum value) =
      RankedDominionExtentDatum value
    regionToExtent (RankedDominionExtentDatum value) =
      RankedDominionExtentDatum value

    extentToRegion (RankedDominionExtentDatum value)
      | rank valueDominion value == sourceRank =
          Just (RankedDominionRegionDatum value)
      | otherwise = Nothing
    extentToRegion (RankedDominionRegionDatum value)
      | rank valueDominion value == sourceRank =
          Just (RankedDominionRegionDatum value)
      | otherwise = Nothing

-- | Read a position on the natural spine.  Public page-element constructors
-- guarantee a finite ordinal here; the zero case totalizes the private Atlas
-- callback even if that invariant is erased by ordinary GHC compilation.
spineRank :: Ordinal -> Natural
spineRank position =
  case naturalAtOrdinal position of
    Just valueRank -> valueRank
    Nothing -> 0

-- | Split a dominion into an extent and one final region per occupied rank.
rankedDominionAtlas
  :: Dominion value
  -> Atlas
       (RankedDominionAtlasScope value)
       (RankedDominionPaginationScope value)
       (RankedDominionCellData value)
       ()
       Natural
rankedDominionAtlas valueDominion =
  atlasWithScope
    rankedDominionPagination
    (atlasDataAction
      (rankedDominionAt valueDominion)
      (rankedDominionDataMap valueDominion))
    (\_ _ -> ())
    (\_ _ _ _ -> ())
    (\_ _ _ _ -> ())
    (\_ _ _ _ _ _ _ -> ())

rankedDominionCoverage
  :: Dominion value
  -> PageElement (RankedDominionPaginationScope value) object
  -> RankedDominionCellData value object
  -> AtlasCoverageWitness (RankedDominionAtlasObject value)
rankedDominionCoverage valueDominion source datum =
  withPageElement
    (lastPageElement
      (atlasPageElements valueAtlas)
      (chainIndexOf spine (rank valueDominion (cellValue datum)))) $
        \region ->
          atlasCoverageWitness
            valueAtlas
            source
            datum
            region
            (RankedDominionRegionDatum (cellValue datum))
            ()
  where
    valueAtlas = rankedDominionAtlas valueDominion

    cellValue (RankedDominionExtentDatum value) = value
    cellValue (RankedDominionRegionDatum value) = value

-- | Restrict the ranked Atlas to the map whose every extent datum is covered
-- by the final region at its dominion rank.
rankedDominionAtlasMap
  :: Dominion value
  -> AtlasMap (RankedDominionAtlasObject value)
rankedDominionAtlasMap valueDominion =
  atlasMap
    (rankedDominionAtlas valueDominion)
    (rankedDominionCoverage valueDominion)

-- | The canonical covered extent element corresponding to one dominion
-- value.
rankedDominionCoalitionElement
  :: Dominion value
  -> value
  -> CoalitionElement (RankedDominionAtlasObject value)
rankedDominionCoalitionElement valueDominion value =
  withPageElement (atlasOriginCell valueAtlas) $ \origin ->
    let datum = RankedDominionExtentDatum value
    in coalitionElement
        origin
        datum
        (rankedDominionCoverage valueDominion origin datum)
  where
    valueAtlas = rankedDominionAtlas valueDominion

-- | Lift an insertion between dominions to the stable Atlas traversal into
-- the target's ranked Atlas map.  This packages the standard passage through
-- the target coalition, including recovery of a source from a selected rank.
rankedDominionInsertionTraversal
  :: Dominion target
  -> DomanialInsertion source target
  -> StableAtlasTransversal
       (DominionAtlasObject source)
       (RankedDominionAtlasObject target)
rankedDominionInsertionTraversal targetDominion insertion =
  coaToDomInc
    (pullbackDominion targetDominion insertion)
    (atlasWitness (rankedDominionAtlas targetDominion))
    coalitionInsertion
  where
    coalitionInsertion =
      domanialInsertion
        (rankedDominionCoalitionElement targetDominion
          . applyInsertion insertion)
        (\element ->
          unrank targetDominion (coalitionElementRank element)
            >>= preimage insertion)
        (insertionLeftInverse insertion)
