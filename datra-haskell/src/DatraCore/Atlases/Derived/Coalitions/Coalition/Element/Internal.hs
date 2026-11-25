{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

-- | Private representation of coalition carriers and dependent views.
module Coalition.Element.Internal
  ( CoalitionElement
  , CoalitionData (..)
  , CoalitionView (..)
  , viewCoalitionElement
  , coalitionElement
  , coalitionElementRank
  , coalitionElementSource
  , coalitionElementCode
  , withCoalitionElement
  ) where

import Atlas (AtlasObjectAtlasScope, AtlasObjectCellData, AtlasObjectPaginationScope)
import Charter.Data (ChartedDatum, chartedCellDataValue, chartedCellDataRank)
import Numeric.Natural (Natural)
import PageElements (PageElement)
import PageElements.Structure (SomePageElement (..))

-- | A coalition stores the canonical charted origin datum and its origin rank.
-- Coverage witnesses are reconstructed from the canonical code when needed.
type CoalitionElement atlasObject =
  CoalitionData (AtlasObjectAtlasScope atlasObject)
    (AtlasObjectPaginationScope atlasObject) (AtlasObjectCellData atlasObject)

type role CoalitionData nominal nominal nominal
data CoalitionData atlasScope scope cellData where
  CoalitionElement :: forall atlasScope scope cellData object.
    PageElement scope object -> ChartedDatum atlasScope scope cellData object
    -> Natural -> CoalitionData atlasScope scope cellData

-- | A public read-only view: constructing a view cannot construct a coalition.
data CoalitionView scope cellData where
  CoalitionView :: forall scope cellData object.
    PageElement scope object -> cellData object -> CoalitionView scope cellData

viewCoalitionElement :: CoalitionData a s d -> CoalitionView s d
viewCoalitionElement (CoalitionElement source datum _) =
  CoalitionView source (chartedCellDataValue datum)

coalitionElement :: PageElement s object -> ChartedDatum a s d object -> Natural -> CoalitionData a s d
coalitionElement = CoalitionElement

coalitionElementSource :: CoalitionData a s d -> SomePageElement s
coalitionElementSource (CoalitionElement source _ _) = SomePageElement source

-- ALIGN: COALITION-CODE.
-- ALIGN: COALITION-CODE-INTERPRETATION.
coalitionElementCode :: CoalitionData a s d -> Natural
coalitionElementCode (CoalitionElement _ datum _) = chartedCellDataRank datum

instance Eq (CoalitionData a s d) where
  (==) = coalitionElementsEqual

-- ALIGN: COALITION-EQUALITY.
coalitionElementsEqual :: CoalitionData a s d -> CoalitionData a s d -> Bool
coalitionElementsEqual left right = coalitionElementRank left == coalitionElementRank right

instance Show (CoalitionData a s d) where
  showsPrec _ element =
    showString "CoalitionElement " . shows (coalitionElementRank element)

-- | The rank of the underlying datum in the uncharted origin dominion.
-- ALIGN: COALITION-CACHED-RANK.
coalitionElementRank :: CoalitionData a s d -> Natural
coalitionElementRank (CoalitionElement _ _ originRank) = originRank

-- | Eliminate a coalition element at its exact dependent origin cell.
-- ALIGN: COALITION-CONSTRUCTOR-ELIM.
withCoalitionElement
  :: CoalitionData atlasScope scope cellData
  -> (forall object.
       PageElement scope object
       -> cellData object
       -> result)
  -> result
withCoalitionElement element useElement = case viewCoalitionElement element of
  CoalitionView source datum -> useElement source datum
