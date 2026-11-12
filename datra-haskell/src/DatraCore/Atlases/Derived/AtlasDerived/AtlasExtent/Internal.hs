{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden implementation of Atlas extents and dependent cell dominions.
module AtlasExtent.Internal
  ( AtlasCellDominion (..)
  , AtlasCellDominionHandler
  , atlasExtent
  , withAtlasCellDominion
  , atlasCellOriginRankInsertion
  , extentContainsRank
  , cellContainsRank
  ) where

import Atlas.Internal
  ( Atlas
  , atlasDataAt
  , atlasPageElements
  , mapAtlasData
  )
import Data.Kind (Type)
import Dominion (Dominion)
import DomanialInsertion (DomanialInsertion, preimage)
import DomanialInsertion.LiquidInternal (rankImageInsertion)
import Data.Maybe (isJust)
import Numeric.Natural (Natural)
import PageElements
  ( PageElement
  , pageElementArrow
  )
import PageElements.LiquidInternal
  ( SomePageElement (..)
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
    :: PageElement scope object
    -> Dominion (cellData object)
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
  (AtlasCellDominion occurrence valueDominion)
  useDominion = useDominion occurrence valueDominion

-- | The Atlas extent: the dominion attached to its origin cell.
-- ALIGN: ATLAS-EXTENT-INTERPRETATION.
atlasExtent
  :: Atlas atlasScope scope cellData origin final
  -> AtlasCellDominion scope cellData
atlasExtent valueAtlas =
  case Elements.originPageElement (atlasPageElements valueAtlas) of
    SomePageElement origin ->
      AtlasCellDominion origin (atlasDataAt valueAtlas origin)

-- | Use the extent's ranking for a cell's image, with a checked inverse on
-- all natural ranks, including ranks outside the cell's image.
-- ALIGN: ATLAS-CELL-ORIGIN-RANK-INSERTION.
atlasCellOriginRankInsertion
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> DomanialInsertion (cellData object) Natural
atlasCellOriginRankInsertion valueAtlas source =
  withAtlasCellDominion (atlasExtent valueAtlas) $ \origin originDominion ->
    rankImageInsertion originDominion
      (mapAtlasData valueAtlas (pageElementArrow source origin))

-- ALIGN: ATLAS-CELL-CONTAINS-RANK.
cellContainsRank
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> Natural
  -> Bool
cellContainsRank valueAtlas source valueRank =
  isJust (preimage (atlasCellOriginRankInsertion valueAtlas source) valueRank)

-- ALIGN: ATLAS-EXTENT-CONTAINS-RANK.
extentContainsRank
  :: Atlas atlasScope scope cellData origin final
  -> Natural
  -> Bool
extentContainsRank valueAtlas valueRank =
  withAtlasCellDominion (atlasExtent valueAtlas) $ \origin _ ->
    cellContainsRank valueAtlas origin valueRank
