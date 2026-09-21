{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden implementation of Atlas federations.
module AtlasFederation.Internal
  ( AtlasFederationSeparation (..)
  , AtlasFederation
  , atlasFederation
  , atlasFederationConfederation
  , atlasFederationIndexDominion
  , atlasFederationComponent
  , atlasFederationPresentation
  , atlasFederationSeparation
  , withAtlasFederationResultingAtlas
  , forgetAtlasFederationTags
  ) where

import Atlas (Atlas)
import AtlasConfederation
  ( AtlasConfederation
  , AtlasConfederationComponent
  , AtlasMergePresentation
  , atlasConfederationComponent
  , atlasConfederationIndexDominion
  , atlasConfederationPresentation
  , withAtlasConfederationResultingAtlas
  )
import DatraOrdinal (Ordinal)
import Dominion (Dominion, rank)
import Numeric.Natural (Natural)

-- | Evidence for the disjunction in Lean's @IsAtlasFederation@ predicate.
-- The page is measured on the full padded spine. Equal-order pages also carry
-- the ordinal position of corresponding page elements for which the caller
-- has established that no common element exists.
data AtlasFederationSeparation
  = DifferentPageOrderTypes Natural
  | SeparatedCorrespondingPageElements Natural Ordinal
  deriving (Eq, Show)

-- | An Atlas confederation equipped with a separation witness for every pair
-- of distinct tags. The witness function is only observed for distinct tags.
type role AtlasFederation nominal nominal
data AtlasFederation confederationScope index = AtlasFederation
  (AtlasConfederation confederationScope index)
  (index -> index -> AtlasFederationSeparation)

-- | Refine an Atlas confederation to a federation. The supplied function must
-- witness the federation condition whenever its two arguments are distinct.
atlasFederation
  :: AtlasConfederation confederationScope index
  -> (index -> index -> AtlasFederationSeparation)
  -> AtlasFederation confederationScope index
atlasFederation = AtlasFederation

-- | Forget the federation proof and retain the underlying confederation.
atlasFederationConfederation
  :: AtlasFederation confederationScope index
  -> AtlasConfederation confederationScope index
atlasFederationConfederation (AtlasFederation confederation _) =
  confederation

atlasFederationIndexDominion
  :: AtlasFederation confederationScope index
  -> Dominion index
atlasFederationIndexDominion =
  atlasConfederationIndexDominion . atlasFederationConfederation

atlasFederationComponent
  :: AtlasFederation confederationScope index
  -> index
  -> AtlasConfederationComponent
atlasFederationComponent =
  atlasConfederationComponent . atlasFederationConfederation

atlasFederationPresentation
  :: AtlasFederation confederationScope index
  -> AtlasMergePresentation
atlasFederationPresentation =
  atlasConfederationPresentation . atlasFederationConfederation

-- | Retrieve the separation witness for two distinct tags. Equal ranks imply
-- equal tags by the underlying dominion law, so equal tags return 'Nothing'.
atlasFederationSeparation
  :: AtlasFederation confederationScope index
  -> index
  -> index
  -> Maybe AtlasFederationSeparation
atlasFederationSeparation
  federation@(AtlasFederation _ separation) left right
  | rank (atlasFederationIndexDominion federation) left
      == rank (atlasFederationIndexDominion federation) right = Nothing
  | otherwise = Just (separation left right)

withAtlasFederationResultingAtlas
  :: AtlasFederation confederationScope index
  -> (forall atlasScope paginationScope cellData origin final.
       Atlas atlasScope paginationScope cellData origin final
       -> result)
  -> result
withAtlasFederationResultingAtlas federation = withAtlasConfederationResultingAtlas
    (atlasFederationConfederation federation)

-- | Discard both component tags and their separation witnesses.
forgetAtlasFederationTags
  :: AtlasFederation confederationScope index
  -> (forall atlasScope paginationScope cellData origin final.
       Atlas atlasScope paginationScope cellData origin final
       -> result)
  -> result
forgetAtlasFederationTags = withAtlasFederationResultingAtlas
