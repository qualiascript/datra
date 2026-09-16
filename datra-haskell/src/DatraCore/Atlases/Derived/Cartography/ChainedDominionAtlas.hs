{-# LANGUAGE TypeFamilies #-}

-- | A two-page Atlas map presenting a dominion along a supplied chain.
--
-- The extent carries the entire dominion. Each final-chain cell carries the
-- singleton datum selected by that chain value. Unlike a ranked dominion
-- Atlas, the final order type is exactly the supplied chain's order type.
module ChainedDominionAtlas
  ( ChainedDominionCellData
  , ChainedDominionAtlas
  , ChainedDominionAtlasObject
  , chainedDominionAtlas
  , chainedDominionAtlasMap
  , chainedDominionCoalitionElement
  , chainedDominionInsertionTraversal
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
import Chain
  ( Chain
  , chainIndex
  , chainIndexOf
  , chainObjectAt
  , chainPosition
  )
import Consolidation (consolidation, op)
import Coalition (CoalitionElement, coalitionElementRank)
import Coalition.Internal (coalitionElement)
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

-- | Data carried by the extent or by one selected final-chain region.
data ChainedDominionCellData value object
  = ChainedDominionExtentDatum value
  | ChainedDominionRegionDatum value
  deriving (Eq, Show)

data ChainedDominionAtlasScope value
data ChainedDominionPaginationScope value

type ChainedDominionAtlasObject value =
  AtlasObject
    (ChainedDominionAtlasScope value)
    (ChainedDominionPaginationScope value)
    (ChainedDominionCellData value)

type ChainedDominionAtlas value =
  Atlas
    (ChainedDominionAtlasScope value)
    (ChainedDominionPaginationScope value)
    (ChainedDominionCellData value)
    ()
    value

chainedDominionFolio
  :: value
  -> Chain value
  -> Folio () value
chainedDominionFolio firstValue valueChain =
  appendPage
    (singletonFolio singletonChain)
    valueChain
    (op collapseChain)
  where
    collapseChain =
      consolidation
        (const ())
        (const firstValue)
        (\_ _ _ -> ())
        (const ())

chainedDominionPagination
  :: value
  -> Chain value
  -> Pagination (ChainedDominionPaginationScope value) () value
chainedDominionPagination firstValue =
  paginationWithScope . chainedDominionFolio firstValue

chainValueAt
  :: value
  -> Chain value
  -> PageElement scope object
  -> value
chainValueAt firstValue valueChain occurrence =
  maybe
    firstValue
    chainObjectAt
    (chainIndex valueChain (pageElementPosition occurrence))

chainedDominionAt
  :: value
  -> Chain value
  -> Dominion value
  -> PageElement (ChainedDominionPaginationScope value) object
  -> Dominion (ChainedDominionCellData value object)
chainedDominionAt firstValue valueChain valueDominion occurrence
  | pageElementPage occurrence == 0 =
      dominion
        (rank valueDominion . cellValue)
        (fmap ChainedDominionExtentDatum . unrank valueDominion)
        (const ())
  | otherwise =
      dominion
        (const 0)
        (\valueRank ->
          if valueRank == 0
            then Just (ChainedDominionRegionDatum selectedValue)
            else Nothing)
        (const ())
  where
    selectedValue = chainValueAt firstValue valueChain occurrence

    cellValue (ChainedDominionExtentDatum value) = value
    cellValue (ChainedDominionRegionDatum value) = value

chainedDominionDataMap
  :: value
  -> Chain value
  -> PageElementArrow
       (ChainedDominionPaginationScope value) source target
  -> DomanialInsertion
       (ChainedDominionCellData value source)
       (ChainedDominionCellData value target)
chainedDominionDataMap firstValue valueChain pageArrow
  | pageElementPage (arrowSource pageArrow) == 0 =
      domanialInsertion coerceCell (Just . coerceCell) (const ())
  | pageElementPage (arrowTarget pageArrow) == 0 =
      domanialInsertion regionToExtent extentToRegion (const ())
  | otherwise =
      domanialInsertion coerceCell (Just . coerceCell) (const ())
  where
    selectedValue =
      chainValueAt firstValue valueChain (arrowSource pageArrow)

    coerceCell (ChainedDominionExtentDatum value) =
      ChainedDominionExtentDatum value
    coerceCell (ChainedDominionRegionDatum value) =
      ChainedDominionRegionDatum value

    regionToExtent (ChainedDominionRegionDatum value) =
      ChainedDominionExtentDatum value
    regionToExtent (ChainedDominionExtentDatum value) =
      ChainedDominionExtentDatum value

    extentToRegion (ChainedDominionExtentDatum value)
      | sameChainPosition value selectedValue =
          Just (ChainedDominionRegionDatum value)
      | otherwise = Nothing
    extentToRegion (ChainedDominionRegionDatum value)
      | sameChainPosition value selectedValue =
          Just (ChainedDominionRegionDatum value)
      | otherwise = Nothing

    sameChainPosition left right =
      chainPosition valueChain left == chainPosition valueChain right

-- | Present every member of a dominion as one region in the supplied chain.
-- The first value is the chain's nonempty witness and total fallback after
-- ordinary GHC erases the certified page-index invariant.
chainedDominionAtlas
  :: value
  -> Chain value
  -> Dominion value
  -> ChainedDominionAtlas value
chainedDominionAtlas firstValue valueChain valueDominion =
  atlasWithScope
    (chainedDominionPagination firstValue valueChain)
    (atlasDataAction
      (chainedDominionAt firstValue valueChain valueDominion)
      (chainedDominionDataMap firstValue valueChain))
    (\_ _ -> ())
    (\_ _ _ _ -> ())
    (\_ _ _ _ -> ())
    (\_ _ _ _ _ _ _ -> ())

chainedDominionCoverage
  :: value
  -> Chain value
  -> Dominion value
  -> PageElement (ChainedDominionPaginationScope value) object
  -> ChainedDominionCellData value object
  -> AtlasCoverageWitness (ChainedDominionAtlasObject value)
chainedDominionCoverage firstValue valueChain valueDominion source datum =
  withPageElement
    (lastPageElement
      (atlasPageElements valueAtlas)
      (chainIndexOf valueChain (cellValue datum))) $
        \region ->
          atlasCoverageWitness
            valueAtlas
            source
            datum
            region
            (ChainedDominionRegionDatum (cellValue datum))
            ()
  where
    valueAtlas =
      chainedDominionAtlas firstValue valueChain valueDominion

    cellValue (ChainedDominionExtentDatum value) = value
    cellValue (ChainedDominionRegionDatum value) = value

-- | Restrict a chained dominion Atlas to its canonical coverage map.
chainedDominionAtlasMap
  :: value
  -> Chain value
  -> Dominion value
  -> AtlasMap (ChainedDominionAtlasObject value)
chainedDominionAtlasMap firstValue valueChain valueDominion =
  atlasMap
    (chainedDominionAtlas firstValue valueChain valueDominion)
    (chainedDominionCoverage firstValue valueChain valueDominion)

-- | The canonical covered extent element corresponding to one chained
-- dominion value.
chainedDominionCoalitionElement
  :: value
  -> Chain value
  -> Dominion value
  -> value
  -> CoalitionElement (ChainedDominionAtlasObject value)
chainedDominionCoalitionElement firstValue valueChain valueDominion value =
  withPageElement (atlasOriginCell valueAtlas) $ \origin ->
    let datum = ChainedDominionExtentDatum value
    in coalitionElement
        origin
        datum
        (chainedDominionCoverage
          firstValue valueChain valueDominion origin datum)
  where
    valueAtlas = chainedDominionAtlas firstValue valueChain valueDominion

-- | Lift an insertion between dominions to the stable traversal into a
-- chained Atlas map.
chainedDominionInsertionTraversal
  :: value
  -> Chain value
  -> Dominion value
  -> DomanialInsertion source value
  -> StableAtlasTransversal
       (DominionAtlasObject source)
       (ChainedDominionAtlasObject value)
chainedDominionInsertionTraversal
    firstValue valueChain targetDominion insertion =
  coaToDomInc
    (pullbackDominion targetDominion insertion)
    (atlasWitness
      (chainedDominionAtlas firstValue valueChain targetDominion))
    coalitionInsertion
  where
    coalitionInsertion =
      domanialInsertion
        (chainedDominionCoalitionElement
          firstValue valueChain targetDominion
          . applyInsertion insertion)
        (\element ->
          unrank targetDominion (coalitionElementRank element)
            >>= preimage insertion)
        (insertionLeftInverse insertion)
