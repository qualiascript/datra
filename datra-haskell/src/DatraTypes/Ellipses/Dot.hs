-- | The one-point stable-confederal datum.
--
-- @Dot@ is the Yoneda embedding of the domanial inclusion of the singleton
-- dominion.  Its representing Atlas therefore has one page, one cell, and one
-- datum: 'Terminal'.
module Dot
  ( Dot
  , DotTerminal (Terminal)
  , dotTerminal
  , dotTerminalRank
  , dot
  , dotDominion
  , DotAtlasObject
  , dotAtlas
  , dotAtlasMap
  ) where

import Atlas
  ( Atlas
  , AtlasObjectAtlasScope
  , AtlasObjectCellData
  , AtlasObjectPaginationScope
  )
import AtlasCoveredPageElement
  ( AtlasCoverageWitness
  , atlasCoverageWitness
  )
import AtlasMap (AtlasMap, atlasMap)
import DomanialInclusion
  ( DominionAtlasObject
  , dominionAtlas
  )
import Dominion (Dominion, dominion)
import Numeric.Natural (Natural)
import PageElements (PageElement)
import StableConfederalData
  ( EmbeddedAtlasMap
  , StableConfederalData
  , embedAtlasMap
  )

-- | The unique element of 'dotDominion'.
data DotTerminal = Terminal
  deriving (Eq, Show)

-- | The unique terminal value, named separately so clients need not import a
-- potentially ambiguous @Terminal@ constructor.
dotTerminal :: DotTerminal
dotTerminal = Terminal

-- | The unique terminal occupies rank zero.
dotTerminalRank :: DotTerminal -> Natural
dotTerminalRank Terminal = 0

-- | The singleton dominion carried by 'Dot'.
dotDominion :: Dominion DotTerminal
dotDominion =
  dominion
    dotTerminalRank
    (\valueRank ->
      if valueRank == 0 then Just Terminal else Nothing)
    (const ())

-- | The object obtained by applying the domanial inclusion to
-- 'dotDominion'.
type DotAtlasObject = DominionAtlasObject DotTerminal

-- | Dot's one-page, one-cell representing Atlas.
dotAtlas
  :: Atlas
       (AtlasObjectAtlasScope DotAtlasObject)
       (AtlasObjectPaginationScope DotAtlasObject)
       (AtlasObjectCellData DotAtlasObject)
       ()
       ()
dotAtlas = dominionAtlas dotDominion

dotCoverage
  :: PageElement
       (AtlasObjectPaginationScope DotAtlasObject)
       object
  -> AtlasObjectCellData DotAtlasObject object
  -> AtlasCoverageWitness DotAtlasObject
dotCoverage occurrence datum =
  atlasCoverageWitness
    dotAtlas occurrence datum occurrence datum ()

-- | The one-page inclusion is already an Atlas map: its only datum is covered
-- by its only cell, which is both the extent and the final region.
dotAtlasMap :: AtlasMap DotAtlasObject
dotAtlasMap = atlasMap dotAtlas dotCoverage

-- | The stable-confederal value represented by the singleton domanial
-- inclusion.
type Dot = EmbeddedAtlasMap DotAtlasObject

dot :: StableConfederalData Dot
dot = embedAtlasMap dotAtlasMap
