{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RoleAnnotations #-}

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
  , withChainedDominionAtlas
  , CanonicalChainedDominion (..)
  , CanonicalChainedAtlasScope
  , CanonicalChainedPaginationScope
  , canonicalChainedDominionAtlas
  , chainedDominionAtlasMap
  , chainedDominionCoalitionElement
  , chainedDominionInsertionTraversal
  ) where

import qualified Pagination
import Atlas
  ( Atlas
  , AtlasObject
  , AtlasPresentation
  , atlasPresentationForPredicate
  , withAtlasPresentation
  , atlasOriginCell
  , atlasPredicateDataAction
  , atlasPageElements
  , atlasWitness
  )
import Atlas.Construction (AtlasConstruction (..), FixedAtlasScope, constructAtlas)
import Data.Proxy (Proxy (..))
import PageElements.Construction
  ( PageElementsConstruction (..), ConstructedPageElementsScope, constructPageElements )
import AtlasCoveredPageElement
  ( AtlasCoverageWitness
  , atlasCoverageWitness
  )
import AtlasMap (AtlasMap, atlasMap)
import Chain
  ( Chain
  , chainIndexOf
  )
import Consolidation (consolidation, op)
import Coalition (CoalitionElement, coalitionElementRank)
import Coalition.Element (coalitionElement)
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
import Dominion (Dominion, unrank)
import ChainedDominionAtlas.Data
  ( ChainedDominionCellData (..)
  , cellValue, extentDominion, regionDominion
  )
import ChainedDominionAtlas.Action
  ( ChainedDominionCell (..), chainedDominionCell, cellAccepts, cellInsertion )
import Folio (Folio, appendPage, singletonFolio)
import PageElements
  ( PageElement
  , PageElementArrow
  , arrowSource
  , arrowTarget
  , withPageElement
  , lastPageElement
  )
import Pagination (Pagination)
import StableAtlasTransversal (StableAtlasTransversal)

type ChainedDominionAtlasObject owner scope value =
  AtlasObject owner scope (ChainedDominionCellData value)

type role ChainedDominionAtlas nominal nominal nominal
data ChainedDominionAtlas owner scope value = ChainedDominionAtlas
  (Chain value) (Dominion value)
  (Atlas owner scope (ChainedDominionCellData value) () value)

chainedDominionAtlas :: ChainedDominionAtlas owner scope value
  -> Atlas owner scope (ChainedDominionCellData value) () value
chainedDominionAtlas (ChainedDominionAtlas _ _ valueAtlas) = valueAtlas

-- | An instance fixes the first value, complete chain, and Dominion together.
class CanonicalChainedDominion value where
  canonicalChainedDominion :: Proxy value -> (value, Chain value, Dominion value)

data CanonicalChainedRecipe value
type CanonicalChainedPaginationScope value =
  ConstructedPageElementsScope (CanonicalChainedRecipe value) () value
type CanonicalChainedAtlasScope value =
  FixedAtlasScope (CanonicalChainedRecipe value) (CanonicalChainedPaginationScope value)
    (ChainedDominionCellData value) () value

instance CanonicalChainedDominion value => PageElementsConstruction (CanonicalChainedRecipe value) () value where
  pageElementsRecipe _ =
    let (first, valueChain, _) = canonicalChainedDominion (Proxy :: Proxy value)
    in chainedDominionFolio first valueChain

instance CanonicalChainedDominion value => AtlasConstruction (CanonicalChainedRecipe value)
    (ConstructedPageElementsScope (CanonicalChainedRecipe value) () value) (ChainedDominionCellData value) () value where
  atlasConstructionPresentation _ =
    let (first, valueChain, valueDominion) = canonicalChainedDominion (Proxy :: Proxy value)
        pages = Pagination.paginationFromPageElements
          (constructPageElements (Proxy :: Proxy (CanonicalChainedRecipe value)))
    in chainedDominionPresentation pages first valueChain valueDominion

canonicalChainedDominionAtlas :: forall value. CanonicalChainedDominion value
  => ChainedDominionAtlas (CanonicalChainedAtlasScope value) (CanonicalChainedPaginationScope value) value
canonicalChainedDominionAtlas =
  let (_, valueChain, valueDominion) = canonicalChainedDominion (Proxy :: Proxy value)
  in ChainedDominionAtlas valueChain valueDominion
       (constructAtlas (Proxy :: Proxy (CanonicalChainedRecipe value)))

-- | Allocate the runtime folio and its data action once and retain both owners.
withChainedDominionAtlas :: value -> Chain value -> Dominion value
  -> (forall owner scope. ChainedDominionAtlas owner scope value -> result) -> result
withChainedDominionAtlas first valueChain valueDominion useOwner =
  Pagination.pagination (chainedDominionFolio first valueChain) $ \pages ->
    withAtlasPresentation (chainedDominionPresentation pages first valueChain valueDominion) $
      useOwner . ChainedDominionAtlas valueChain valueDominion

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

chainedDominionAt
  :: value
  -> Chain value
  -> Dominion value
  -> PageElement scope object
  -> Dominion (ChainedDominionCellData value object)
chainedDominionAt firstValue valueChain valueDominion occurrence =
  case chainedDominionCell firstValue valueChain occurrence of
    ExtentCell -> extentDominion valueDominion
    RegionCell selected -> regionDominion valueChain selected

chainedDominionAccepts
  :: value -> Chain value -> PageElement scope object
  -> ChainedDominionCellData value object -> Bool
chainedDominionAccepts firstValue valueChain occurrence =
  cellAccepts valueChain (chainedDominionCell firstValue valueChain occurrence)

chainedDominionDataMap
  :: value -> Chain value -> PageElementArrow scope source target
  -> DomanialInsertion (ChainedDominionCellData value source) (ChainedDominionCellData value target)
chainedDominionDataMap firstValue valueChain pageArrow =
  cellInsertion valueChain
    (chainedDominionCell firstValue valueChain (arrowSource pageArrow))
    (chainedDominionCell firstValue valueChain (arrowTarget pageArrow))

-- | Certify the data action on an already owned two-page pagination.
chainedDominionPresentation
  :: Pagination scope () value -> value -> Chain value -> Dominion value
  -> AtlasPresentation scope (ChainedDominionCellData value) () value
chainedDominionPresentation pages firstValue valueChain valueDominion =
  atlasPresentationForPredicate pages (chainedDominionAccepts firstValue valueChain)
    (atlasPredicateDataAction (Pagination.paginationPageElements pages)
      (chainedDominionAccepts firstValue valueChain)
      (chainedDominionAt firstValue valueChain valueDominion)
      (chainedDominionDataMap firstValue valueChain))
    (\_ _ -> ())
    (\_ _ _ _ -> ())
    (\_ _ _ _ -> ())
    (\_ _ _ _ _ _ _ -> ())

chainedDominionCoverage
  :: ChainedDominionAtlas owner scope value
  -> PageElement scope object
  -> ChainedDominionCellData value object
  -> AtlasCoverageWitness (ChainedDominionAtlasObject owner scope value)
chainedDominionCoverage (ChainedDominionAtlas valueChain _ valueAtlas) source datum =
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

-- | Restrict a chained dominion Atlas to its canonical coverage map.
chainedDominionAtlasMap
  :: ChainedDominionAtlas owner scope value
  -> AtlasMap (ChainedDominionAtlasObject owner scope value)
chainedDominionAtlasMap owner =
  atlasMap
    (chainedDominionAtlas owner)
    (chainedDominionCoverage owner)

-- | The canonical covered extent element corresponding to one chained
-- dominion value.
chainedDominionCoalitionElement
  :: ChainedDominionAtlas owner scope value
  -> value
  -> CoalitionElement (ChainedDominionAtlasObject owner scope value)
chainedDominionCoalitionElement owner value =
  withPageElement (atlasOriginCell valueAtlas) $ \origin ->
    let datum = ChainedDominionExtentDatum value
    in coalitionElement
        valueAtlas
        origin
        datum
        (chainedDominionCoverage owner origin datum)
  where
    valueAtlas = chainedDominionAtlas owner

-- | Lift an insertion between dominions to the stable traversal into a
-- chained Atlas map.
chainedDominionInsertionTraversal
  :: ChainedDominionAtlas owner scope value
  -> DomanialInsertion source value
  -> DominionAtlas sourceOwner source
  -> StableAtlasTransversal
       (DominionAtlasObject sourceOwner source)
       (ChainedDominionAtlasObject owner scope value)
chainedDominionInsertionTraversal
    owner@(ChainedDominionAtlas _ targetDominion targetAtlas) insertion sourceOwner =
  coaToDomInc
    sourceOwner
    (atlasWitness targetAtlas)
    coalitionInsertion
    (\_ datum -> preimage insertion (cellValue datum))
    (\_ -> insertionLeftInverse insertion)
  where
    coalitionInsertion =
      domanialInsertion
        (chainedDominionCoalitionElement owner
          . applyInsertion insertion)
        (\element ->
          unrank targetDominion (coalitionElementRank element)
            >>= preimage insertion)
        (insertionLeftInverse insertion)
