{-# LANGUAGE TypeFamilies #-}

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

import Atlas (atlasWitness)
import DomanialInclusion
  ( DominionAtlas, DominionAtlasObject, coaToDomInc )
import DomanialInsertion (DomanialInsertion)
import StableAtlasTransversal (StableAtlasTransversal)
import RankedDominionAtlas.Data (RankedDominionCellData)
import RankedDominionAtlas.Coalition
  ( rankedDominionCoalitionElement, rankedCoalitionInsertion
  , rankedComponentBackward, rankedComponentLeftInverse )
import RankedDominionAtlas.Coverage (rankedDominionAtlasMap)
import RankedDominionAtlas.Owner
  ( RankedDominionAtlas, RankedDominionAtlasObject, withRankedDominionAtlas, rankedDominionAtlas )

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
    (\_ -> rankedComponentBackward insertion)
    (rankedComponentLeftInverse owner insertion)
