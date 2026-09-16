-- | The recursive ellipsis stable-confederal datum and its concrete Atlas map.
module Ellipsis
  ( Ellipsis
  , EllipsisValue
  , EllipsisTerminal (Terminal)
  , terminalRank
  , ellipsis
  , ellipsisUnfolded
  , ellipsisFold
  , ellipsisUnfold
  , ellipsisValue
  , withEllipsisValue
  , ellipsisDominion
  , EllipsisAtlasObject
  , ellipsisAtlas
  , ellipsisAtlasMap
  , ellipsisCoalitionElement
  ) where

import Atlas
  ( Atlas
  , AtlasObjectAtlasScope
  , AtlasObjectCellData
  , AtlasObjectPaginationScope
  )
import AtlasConfederation
  ( AtlasConfederationObject
  , SingletonAtlasConfederationScope
  , identityAtlasConfederationHom
  , rightAtlasConfederationInclusion
  , singletonAtlasConfederation
  )
import AtlasMap (AtlasMap)
import Coalition (CoalitionElement)
import Dominion (Dominion, dominion)
import Dot (Dot, dot, dotAtlas)
import Numeric.Natural (Natural)
import MapOperators.ConcatOperator
  ( ConcatOperatorValue
  , ConcatOperatorValues
  , concatValue
  )
import RankedDominionAtlas
  ( RankedDominionAtlasObject
  , rankedDominionAtlas
  , rankedDominionAtlasMap
  , rankedDominionCoalitionElement
  )
import StableConfederalData
  ( StableConfederalData
  , StableConfederalDataHom
  , mapStableConfederalData
  )
import SuperEllipsis
  ( SuperEllipsis
  , SuperEllipsisValue
  , rollSuperEllipsisValue
  , superEllipsis
  , superEllipsisFold
  , superEllipsisUnfold
  , superEllipsisUnfolded
  , withSuperEllipsisValue
  )

-- | A terminal region of Ellipsis, uniquely identified by its absolute rank.
newtype EllipsisTerminal = Terminal
  { terminalRank :: Natural
  }
  deriving (Eq, Show)

-- | The object name of the generic ranked-dominion Atlas specialized to
-- Ellipsis terminals.
type EllipsisAtlasObject = RankedDominionAtlasObject EllipsisTerminal

-- | The first super ellipsis: level zero is 'Dot', and this successor solves
-- @Ellipsis = Dot <.> Ellipsis@.
type Ellipsis = SuperEllipsis Dot

-- | One observable @Dot <.> Ellipsis@ layer.
type EllipsisValue =
  SuperEllipsisValue Dot

-- | The rank presentation is the extent dominion of the representing Atlas,
-- rather than Ellipsis itself.
ellipsisDominion :: Dominion EllipsisTerminal
ellipsisDominion = dominion terminalRank (Just . Terminal) (const ())

-- | The cardinality-two Atlas whose origin is the omega dominion and whose
-- final page is the omega chain of singleton (terminal) regions.
ellipsisAtlas
  :: Atlas
       (AtlasObjectAtlasScope EllipsisAtlasObject)
       (AtlasObjectPaginationScope EllipsisAtlasObject)
       (AtlasObjectCellData EllipsisAtlasObject)
       ()
       Natural
ellipsisAtlas = rankedDominionAtlas ellipsisDominion

-- | The concrete omega Atlas map solving the recursive presentation. Every
-- origin datum is covered by the singleton region at the same natural rank.
ellipsisAtlasMap :: AtlasMap EllipsisAtlasObject
ellipsisAtlasMap = rankedDominionAtlasMap ellipsisDominion

-- | The canonical covered origin element at a rank. This identifies the
-- coalition of the representing Atlas with 'ellipsisDominion'.
ellipsisCoalitionElement
  :: EllipsisTerminal
  -> CoalitionElement EllipsisAtlasObject
ellipsisCoalitionElement =
  rankedDominionCoalitionElement ellipsisDominion

-- | Eliminate exactly one recursive layer.
withEllipsisValue
  :: EllipsisValue object
  -> (ConcatOperatorValue Dot Ellipsis object -> result)
  -> result
withEllipsisValue = withSuperEllipsisValue

-- | The recursive equation itself. Haskell's lazy binding makes this a
-- guarded fixed point: the concat node is available before its Ellipsis tail
-- is demanded.
ellipsisUnfolded
  :: StableConfederalData (ConcatOperatorValues Dot Ellipsis)
ellipsisUnfolded = superEllipsisUnfolded dot

-- | The stable-confederal action of the fixed point, transported through its
-- single concat layer.
ellipsis :: StableConfederalData Ellipsis
ellipsis = superEllipsis dot

-- | Fold one @Dot <.> Ellipsis@ layer into the fixed point.
ellipsisFold
  :: StableConfederalDataHom
       (ConcatOperatorValues Dot Ellipsis)
       Ellipsis
ellipsisFold =
  superEllipsisFold dot

-- | Unfold the fixed point into @Dot <.> Ellipsis@.
ellipsisUnfold
  :: StableConfederalDataHom
       Ellipsis
       (ConcatOperatorValues Dot Ellipsis)
ellipsisUnfold =
  superEllipsisUnfold dot

type EllipsisConfederationScope =
  SingletonAtlasConfederationScope EllipsisAtlasObject

type EllipsisConfederationObject =
  AtlasConfederationObject EllipsisConfederationScope ()

-- | The canonical recursive value at the concrete Ellipsis confederation.
-- Its represented arrow selects the recursive tail of @Dot + Ellipsis@; the
-- left generator supplies the new leading Dot.
ellipsisValue :: EllipsisValue EllipsisConfederationObject
ellipsisValue = rollSuperEllipsisValue
  (mapStableConfederalData
    ellipsisUnfolded
    tailInclusion
    (concatValue
      dotConfederation
      ellipsisConfederation
      identityAtlasConfederationHom
      ellipsisValue))
  where
    dotConfederation = singletonAtlasConfederation dotAtlas
    ellipsisConfederation = singletonAtlasConfederation ellipsisAtlas
    tailInclusion = rightAtlasConfederationInclusion
      dotConfederation ellipsisConfederation
