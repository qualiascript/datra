{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | The rank-one super ellipsis and its concrete Atlas map.
module Ellipsis
  ( Ellipsis
  , EllipsisValue
  , EllipsisTerminal
  , pattern Terminal
  , terminalRank
  , ellipsisRank
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
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import Dominion (Dominion)
import Dot (Dot, dot, dotAtlas)
import Numeric.Natural (Natural)
import MapOperators.ConcatOperator
  ( ConcatOperatorValue
  , ConcatOperatorValues
  , concatValue
  )
import StableConfederalData
  ( StableConfederalData
  , StableConfederalDataHom
  , mapStableConfederalData
  )
import SuperEllipsis
  ( SuperEllipsis
  , SuperEllipsisAtlasObject
  , SuperEllipsisLayer
  , SuperEllipsisRank
  , SuperEllipsisTerminal
  , dotSuperEllipsisRank
  , nextSuperEllipsisRank
  , rollSuperEllipsisLayer
  , superEllipsis
  , superEllipsisFold
  , superEllipsisUnfold
  , superEllipsisUnfolded
  , superEllipsisAtlas
  , superEllipsisAtlasMap
  , superEllipsisCoalitionElement
  , superEllipsisDominion
  , superEllipsisTerminal
  , superEllipsisTerminalPosition
  , superEllipsisZeroTerminal
  , withSuperEllipsisLayer
  )

-- | A terminal region of the rank-one super ellipsis.
type EllipsisTerminal = SuperEllipsisTerminal Ellipsis

-- | Backward-compatible natural presentation of a rank-one terminal.
pattern Terminal :: Natural -> EllipsisTerminal
pattern Terminal value <- (terminalRank -> value)
  where
    Terminal value =
      case superEllipsisTerminal ellipsisRank (finiteOrdinal value) of
        Just terminal -> terminal
        Nothing -> superEllipsisZeroTerminal ellipsisRank

{-# COMPLETE Terminal #-}

terminalRank :: EllipsisTerminal -> Natural
terminalRank terminal =
  case naturalAtOrdinal (superEllipsisTerminalPosition terminal) of
    Just value -> value
    Nothing -> 0

-- | The object name of the generic super-ellipsis Atlas specialized to rank
-- one.
type EllipsisAtlasObject = SuperEllipsisAtlasObject Ellipsis

-- | The first super ellipsis: level zero is 'Dot', and this successor solves
-- @Ellipsis = Dot <.> Ellipsis@.
type Ellipsis = SuperEllipsis Dot

-- | Runtime rank evidence for @Ellipsis = SuperEllipsis Dot@.
ellipsisRank :: SuperEllipsisRank Ellipsis
ellipsisRank = nextSuperEllipsisRank dotSuperEllipsisRank

-- | One observable @Dot <.> Ellipsis@ layer.
type EllipsisValue =
  SuperEllipsisLayer Dot

-- | The rank presentation is the extent dominion of the representing Atlas,
-- rather than Ellipsis itself.
ellipsisDominion :: Dominion EllipsisTerminal
ellipsisDominion = superEllipsisDominion ellipsisRank

-- | The cardinality-two Atlas whose origin is the omega dominion and whose
-- final page is the omega chain of singleton (terminal) regions.
ellipsisAtlas
  :: Atlas
       (AtlasObjectAtlasScope EllipsisAtlasObject)
       (AtlasObjectPaginationScope EllipsisAtlasObject)
       (AtlasObjectCellData EllipsisAtlasObject)
       ()
       EllipsisTerminal
ellipsisAtlas = superEllipsisAtlas ellipsisRank

-- | The concrete omega Atlas map solving the recursive presentation. Every
-- origin datum is covered by the singleton region at the same natural rank.
ellipsisAtlasMap :: AtlasMap EllipsisAtlasObject
ellipsisAtlasMap = superEllipsisAtlasMap ellipsisRank

-- | The canonical covered origin element at a rank. This identifies the
-- coalition of the representing Atlas with 'ellipsisDominion'.
ellipsisCoalitionElement
  :: EllipsisTerminal
  -> CoalitionElement EllipsisAtlasObject
ellipsisCoalitionElement =
  superEllipsisCoalitionElement ellipsisRank

-- | Eliminate exactly one recursive layer.
withEllipsisValue
  :: EllipsisValue object
  -> (ConcatOperatorValue Dot Ellipsis object -> result)
  -> result
withEllipsisValue = withSuperEllipsisLayer

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
ellipsisValue = rollSuperEllipsisLayer
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
