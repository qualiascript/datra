{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

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
import MapMakingOperators.ConcatOperator
  ( ConcatOperatorValue
  , ConcatOperatorValues
  , concatValue
  , (<.>)
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
  , StableConfederalDataValue
  , mapStableConfederalData
  , stableConfederalData
  , stableConfederalDataComposition
  , stableConfederalDataHom
  , stableConfederalDataIdentity
  )

-- | A terminal region of Ellipsis, uniquely identified by its absolute rank.
newtype EllipsisTerminal = Terminal
  { terminalRank :: Natural
  }
  deriving (Eq, Show)

-- | The object name of the generic ranked-dominion Atlas specialized to
-- Ellipsis terminals.
type EllipsisAtlasObject = RankedDominionAtlasObject EllipsisTerminal

-- | The nominal fixed point of concatenating one 'Dot' in front of another
-- Ellipsis.
data Ellipsis

-- | One layer of the fixed point.  The constructor remains private so every
-- value is observed through the equation @Ellipsis = Dot <.> Ellipsis@.
type role EllipsisValue nominal
newtype EllipsisValue object = EllipsisValue
  (ConcatOperatorValue Dot Ellipsis object)

type instance StableConfederalDataValue Ellipsis object =
  EllipsisValue object

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
withEllipsisValue (EllipsisValue value) useValue = useValue value

-- | The recursive equation itself. Haskell's lazy binding makes this a
-- guarded fixed point: the concat node is available before its Ellipsis tail
-- is demanded.
ellipsisUnfolded
  :: StableConfederalData (ConcatOperatorValues Dot Ellipsis)
ellipsisUnfolded = dot <.> ellipsis

-- | The stable-confederal action of the fixed point, transported through its
-- single concat layer.
ellipsis :: StableConfederalData Ellipsis
ellipsis =
  stableConfederalData
    (\arrow (EllipsisValue value) ->
      EllipsisValue
        (mapStableConfederalData ellipsisUnfolded arrow value))
    (\(EllipsisValue value) ->
      stableConfederalDataIdentity ellipsisUnfolded value)
    (\second first (EllipsisValue value) ->
      stableConfederalDataComposition
        ellipsisUnfolded second first value)

-- | Fold one @Dot <.> Ellipsis@ layer into the fixed point.
ellipsisFold
  :: StableConfederalDataHom
       (ConcatOperatorValues Dot Ellipsis)
       Ellipsis
ellipsisFold =
  stableConfederalDataHom
    ellipsisUnfolded
    ellipsis
    EllipsisValue
    (\_ _ -> ())

-- | Unfold the fixed point into @Dot <.> Ellipsis@.
ellipsisUnfold
  :: StableConfederalDataHom
       Ellipsis
       (ConcatOperatorValues Dot Ellipsis)
ellipsisUnfold =
  stableConfederalDataHom
    ellipsis
    ellipsisUnfolded
    (\(EllipsisValue value) -> value)
    (\_ _ -> ())

type EllipsisConfederationScope =
  SingletonAtlasConfederationScope EllipsisAtlasObject

type EllipsisConfederationObject =
  AtlasConfederationObject EllipsisConfederationScope ()

-- | The canonical recursive value at the concrete Ellipsis confederation.
-- Its represented arrow selects the recursive tail of @Dot + Ellipsis@; the
-- left generator supplies the new leading Dot.
ellipsisValue :: EllipsisValue EllipsisConfederationObject
ellipsisValue = EllipsisValue
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
