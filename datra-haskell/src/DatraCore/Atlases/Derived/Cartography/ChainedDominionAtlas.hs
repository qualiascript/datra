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

import Atlas (atlasWitness)
import Coalition (coalitionElementRank)
import DomanialInclusion
  ( DominionAtlas
  , DominionAtlasObject
  , coaToDomInc
  )
import DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , domanialInsertion
  , insertionLeftInverse
  , preimage
  )
import Dominion (unrank)
import ChainedDominionAtlas.Canonical
  ( CanonicalChainedDominion (..), CanonicalChainedAtlasScope, CanonicalChainedPaginationScope
  , canonicalChainedDominionAtlas )
import ChainedDominionAtlas.Coverage (chainedDominionAtlasMap)
import ChainedDominionAtlas.Coalition (chainedDominionCoalitionElement)
import ChainedDominionAtlas.Data
  ( ChainedDominionCellData
  , cellValue
  )
import ChainedDominionAtlas.Owner
  ( ChainedDominionAtlas, ChainedDominionAtlasObject, chainedDominionAtlas, withChainedDominionAtlas
  , chainedDominionValueDominion )
import StableAtlasTransversal (StableAtlasTransversal)

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
    owner insertion sourceOwner =
  coaToDomInc
    sourceOwner
    (atlasWitness targetAtlas)
    coalitionInsertion
    (\_ datum -> preimage insertion (cellValue datum))
    (\_ -> insertionLeftInverse insertion)
  where
    targetDominion = chainedDominionValueDominion owner
    targetAtlas = chainedDominionAtlas owner
    coalitionInsertion =
      domanialInsertion
        (chainedDominionCoalitionElement owner
          . applyInsertion insertion)
        (\element ->
          unrank targetDominion (coalitionElementRank element)
            >>= preimage insertion)
        (insertionLeftInverse insertion)
