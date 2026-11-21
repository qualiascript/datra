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
  , atlas
  , atlasOriginCell
  , atlasDataAction
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
import Dominion (Dominion, dominion, rank, unrank, lookupRank)
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

-- | Data carried by the extent or by one rank-selected final region.
data RankedDominionCellData value object
  = RankedDominionExtentDatum value
  | RankedDominionRegionDatum value
  deriving (Eq, Show)

cellValue :: RankedDominionCellData value object -> value
cellValue (RankedDominionExtentDatum value) = value
cellValue (RankedDominionRegionDatum value) = value

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
  :: forall value. Pagination (RankedDominionPaginationScope value) () Natural
rankedDominionPagination = Pagination.paginationFromPageElements
  (constructPageElements (Proxy :: Proxy (RankedDominionPaginationRecipe value)))

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
              <$> lookupRank valueDominion occurrenceRank
            else Nothing)
        (const ())
  where
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

-- | A ranked construction retains its Dominion and the freshly allocated
-- Atlas together. All maps and coverage witnesses reuse that exact owner.
type role RankedDominionAtlas nominal nominal
data RankedDominionAtlas owner value = RankedDominionAtlas
  (Dominion value)
  (Atlas owner (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural)

rankedDominionAtlas :: RankedDominionAtlas owner value
  -> Atlas owner (RankedDominionPaginationScope value) (RankedDominionCellData value) () Natural
rankedDominionAtlas (RankedDominionAtlas _ valueAtlas) = valueAtlas

-- | Split a dominion into an extent and one final region per occupied rank.
withRankedDominionAtlas :: Dominion value
  -> (forall owner. RankedDominionAtlas owner value -> result) -> result
withRankedDominionAtlas valueDominion useAtlas =
  atlas
    rankedDominionPagination
    (atlasDataAction (Pagination.paginationPageElements rankedDominionPagination)
      (rankedDominionAt valueDominion)
      (rankedDominionDataMap valueDominion))
    (\_ _ -> ())
    (\_ _ _ _ -> ())
    (\_ _ _ _ -> ())
    (\_ _ _ _ _ _ _ -> ())
    (\valueAtlas -> useAtlas (RankedDominionAtlas valueDominion valueAtlas))

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
rankedDominionAtlasMap
  :: RankedDominionAtlas owner value
  -> AtlasMap (RankedDominionAtlasObject owner value)
rankedDominionAtlasMap owner =
  atlasMap (rankedDominionAtlas owner) (rankedDominionCoverage owner)

-- | The canonical covered extent element corresponding to one dominion
-- value.
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

-- | Lift an insertion between dominions to the stable Atlas traversal into
-- the target's ranked Atlas map.  This packages the standard passage through
-- the target coalition, including recovery of a source from a selected rank.
rankedDominionInsertionTraversal
  :: DominionAtlas sourceOwner source
  -> RankedDominionAtlas owner target
  -> DomanialInsertion source target
  -> StableAtlasTransversal
       (DominionAtlasObject sourceOwner source)
       (RankedDominionAtlasObject owner target)
rankedDominionInsertionTraversal sourceOwner owner@(RankedDominionAtlas targetDominion targetAtlas) insertion =
  coaToDomInc
    sourceOwner
    (atlasWitness targetAtlas)
    coalitionInsertion
    (\_ datum -> preimage insertion (cellValue datum))
    (\_ -> insertionLeftInverse insertion)
  where
    coalitionInsertion =
      domanialInsertion
        (rankedDominionCoalitionElement owner
          . applyInsertion insertion)
        (\element ->
          unrank targetDominion (coalitionElementRank element)
            >>= preimage insertion)
        (insertionLeftInverse insertion)
