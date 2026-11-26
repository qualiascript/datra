{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | The canonical two-page Atlas map that separates a dominion by rank.
--
-- The extent carries the supplied dominion.  Final page position @n@ carries
-- the singleton datum whose dominion rank is @n@ (or no datum when that rank
-- is absent).  This is the reusable DatraCore construction underlying
-- Ellipsis-like ranked maps.
module RankedDominionAtlas
  ( RankedDominionCellData
  , RankedDominionAtlas
  , RankedDominionAtlasObject
  , withRankedDominionAtlas
  , rankedDominionAtlas
  , rankedDominionAtlasMap
  , rankedDominionCoalitionElement
  , rankedDominionInsertionTraversal
  ) where

import qualified Pagination
import Atlas
  ( Atlas
  , AtlasObject
  , atlasForPredicate
  , atlasOriginCell
  , atlasPredicateDataAction
  , atlasPageElements
  , atlasWitness
  )
import AtlasCoveredPageElement
  ( AtlasCoverageWitness
  , atlasCoverageWitness
  )
import AtlasMap (AtlasMap, atlasMap)
import Chain (chainIndexOf, spine)
import Coalition (CoalitionElement, coalitionElementRank)
import Coalition.Element (coalitionElement)
import Consolidation (consolidation, op)
import DatraOrdinal (Ordinal, naturalAtOrdinal)
import DomanialInclusion
  ( DominionAtlas
  , DominionAtlasObject
  , coaToDomInc
  , singletonChain
  )
import DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , domanialInsertion
  , insertionLeftInverse
  , preimage
  )
import Dominion (Dominion, rank, unrank)
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
  , lastPageElement
  )
import Pagination (Pagination)
import Data.Proxy (Proxy (..))
import PageElements.Construction
  ( PageElementsConstruction (..), ConstructedPageElementsScope, constructPageElements )
import StableAtlasTransversal (StableAtlasTransversal)
import RankedDominionAtlas.Data (RankedDominionCellData (..), cellValue)
import qualified RankedDominionAtlas.Data as Ranked

data RankedDominionPaginationRecipe value
type RankedDominionPaginationScope value =
  ConstructedPageElementsScope (RankedDominionPaginationRecipe value) () Natural

instance PageElementsConstruction (RankedDominionPaginationRecipe value) () Natural where
  pageElementsRecipe _ = rankedDominionFolio

type RankedDominionAtlasObject owner value =
  AtlasObject
    owner
    (RankedDominionPaginationScope value)
    (RankedDominionCellData value)

-- ALIGN: RANKED-TWO-PAGE-FOLIO.
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

-- ALIGN: RANKED-PAGINATION.
rankedDominionPagination
  :: forall value. Pagination (RankedDominionPaginationScope value) () Natural
rankedDominionPagination = Pagination.paginationFromPageElements
  (constructPageElements (Proxy :: Proxy (RankedDominionPaginationRecipe value)))

-- | The extent accepts extent-tagged data; a region accepts only its own rank.
-- ALIGN: RANKED-PRESENTATION-MEMBERSHIP.
rankedDominionAccepts :: Dominion value
  -> PageElement (RankedDominionPaginationScope value) object
  -> RankedDominionCellData value object -> Bool
rankedDominionAccepts owner occurrence datum
  | pageElementPage occurrence == 0 = Ranked.extentAccepts datum
  | otherwise = Ranked.regionAccepts owner (spineRank (pageElementPosition occurrence)) datum

-- ALIGN: RANKED-CELL-RANK.
-- ALIGN: RANKED-CELL-DECODE.
rankedDominionAt
  :: Dominion value
  -> PageElement (RankedDominionPaginationScope value) object
  -> Dominion (RankedDominionCellData value object)
rankedDominionAt valueDominion occurrence
  | pageElementPage occurrence == 0 = Ranked.extentDominion valueDominion
  | otherwise = Ranked.regionDominion valueDominion (spineRank (pageElementPosition occurrence))

-- ALIGN: RANKED-CELL-FORWARD.
-- ALIGN: RANKED-CELL-INVERSE.
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
-- ALIGN: RANKED-SPINE-RANK.
spineRank :: Ordinal -> Natural
spineRank position =
  case naturalAtOrdinal position of
    Just valueRank -> valueRank
    Nothing -> 0

-- | A ranked construction retains its Dominion and the freshly allocated
-- Atlas together. All maps and coverage witnesses reuse that exact owner.
type role RankedDominionAtlas nominal nominal
data RankedDominionAtlas owner value = RankedDominionAtlas
  (Dominion value)
  (Atlas owner (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural)

-- ALIGN: RANKED-OWNER-ATLAS.
rankedDominionAtlas :: RankedDominionAtlas owner value
  -> Atlas owner (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural
rankedDominionAtlas (RankedDominionAtlas _ valueAtlas) = valueAtlas

-- | Split a dominion into an extent and one final region per occupied rank.
-- ALIGN: RANKED-OWNER-ALLOCATION.
withRankedDominionAtlas :: Dominion value
  -> (forall owner. RankedDominionAtlas owner value -> result) -> result
withRankedDominionAtlas valueDominion useAtlas =
  atlasForPredicate
    rankedDominionPagination
    (rankedDominionAccepts valueDominion)
    (atlasPredicateDataAction (Pagination.paginationPageElements rankedDominionPagination)
      (rankedDominionAccepts valueDominion)
      (rankedDominionAt valueDominion)
      (rankedDominionDataMap valueDominion))
    (\_ _ -> ())
    (\_ _ _ _ -> ())
    (\_ _ _ _ -> ())
    (\_ _ _ _ _ _ _ -> ())
    (\valueAtlas -> useAtlas (RankedDominionAtlas valueDominion valueAtlas))

-- ALIGN: RANKED-OWNER-COVERAGE.
rankedDominionCoverage
  :: RankedDominionAtlas owner value
  -> PageElement (RankedDominionPaginationScope value) object
  -> RankedDominionCellData value object
  -> AtlasCoverageWitness (RankedDominionAtlasObject owner value)
rankedDominionCoverage (RankedDominionAtlas valueDominion valueAtlas) source datum =
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

-- | Restrict the ranked Atlas to the map whose every extent datum is covered
-- by the final region at its dominion rank.
-- ALIGN: RANKED-OWNER-COVERAGE-MAP.
rankedDominionAtlasMap
  :: RankedDominionAtlas owner value
  -> AtlasMap (RankedDominionAtlasObject owner value)
rankedDominionAtlasMap owner =
  atlasMap (rankedDominionAtlas owner) (rankedDominionCoverage owner)

-- | The canonical covered extent element corresponding to one dominion
-- value.
-- ALIGN: RANKED-OWNER-COALITION.
rankedDominionCoalitionElement
  :: RankedDominionAtlas owner value
  -> value
  -> CoalitionElement (RankedDominionAtlasObject owner value)
rankedDominionCoalitionElement owner value =
  withPageElement (atlasOriginCell valueAtlas) $ \origin ->
    let datum = RankedDominionExtentDatum value
    in coalitionElement
        valueAtlas
        origin
        datum
        (rankedDominionCoverage owner origin datum)
  where
    valueAtlas = rankedDominionAtlas owner

-- | Preserve the target coalition's cached-rank decoder in the partial inverse.
-- ALIGN: RANKED-COALITION-INSERTION.
rankedCoalitionInsertion
  :: RankedDominionAtlas owner target
  -> DomanialInsertion source target
  -> DomanialInsertion source (CoalitionElement (RankedDominionAtlasObject owner target))
rankedCoalitionInsertion owner@(RankedDominionAtlas targetDominion _) insertion =
  domanialInsertion
    (rankedDominionCoalitionElement owner . applyInsertion insertion)
    (\element -> unrank targetDominion (coalitionElementRank element) >>= preimage insertion)
    (insertionLeftInverse insertion)

-- | Lift an insertion between dominions to the stable Atlas traversal into
-- the target's ranked Atlas map.  This packages the standard passage through
-- the target coalition, including recovery of a source from a selected rank.
-- ALIGN: RANKED-INSERTION-TRAVERSAL.
rankedDominionInsertionTraversal
  :: DominionAtlas sourceOwner source
  -> RankedDominionAtlas owner target
  -> DomanialInsertion source target
  -> StableAtlasTransversal
       (DominionAtlasObject sourceOwner source)
       (RankedDominionAtlasObject owner target)
rankedDominionInsertionTraversal sourceOwner owner insertion =
  coaToDomInc
    sourceOwner
    (atlasWitness (rankedDominionAtlas owner))
    (rankedCoalitionInsertion owner insertion)
    (\_ datum -> preimage insertion (cellValue datum))
    (\_ -> insertionLeftInverse insertion)
