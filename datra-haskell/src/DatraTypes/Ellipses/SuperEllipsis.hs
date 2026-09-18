{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | The inductive hierarchy of recursive ellipses.
--
-- @Dot@ is the zeroth level.  Given the preceding level @S(n-1)@,
-- @SuperEllipsis S(n-1)@ is the guarded fixed point
--
-- @
-- S(n) = S(n-1) <.> S(n).
-- @
--
-- Consequently @SuperEllipsis Dot@ has order type omega,
-- @SuperEllipsis (SuperEllipsis Dot)@ has order type omega squared, and
-- finite iteration reaches every power below omega to the omega.
module SuperEllipsis
  ( SuperEllipsis
  , SuperEllipsisLayer
  , SuperEllipsisRank
  , SuperEllipsisLevel (..)
  , SuperEllipsisAt
  , KnownSuperEllipsisLevel
  , knownSuperEllipsisRank
  , knownSuperEllipsisLevelNatural
  , SuperEllipsisTarget
  , SuperEllipsisTargetLevel
  , superEllipsisTargetRank
  , superEllipsisTargetLevelNatural
  , dotSuperEllipsisRank
  , nextSuperEllipsisRank
  , superEllipsisRankOrderType
  , SuperEllipsisTerminal
  , superEllipsisTerminal
  , superEllipsisZeroTerminal
  , superEllipsisTerminalPosition
  , superEllipsisDominion
  , superEllipsisChain
  , SuperEllipsisAtlasObject
  , superEllipsisAtlas
  , superEllipsisAtlasMap
  , superEllipsisCoalitionElement
  , superEllipsis
  , superEllipsisUnfolded
  , superEllipsisFold
  , superEllipsisUnfold
  , rollSuperEllipsisLayer
  , unrollSuperEllipsisLayer
  , withSuperEllipsisLayer
  ) where

import AtlasMap (AtlasMap)
import Chain (Chain, chain)
import ChainedDominionAtlas
  ( ChainedDominionAtlas
  , ChainedDominionAtlasObject
  , chainedDominionAtlas
  , chainedDominionAtlasMap
  , chainedDominionCoalitionElement
  )
import Coalition (CoalitionElement)
import DatraOrdinal
  ( Ordinal
  , finiteOrdinal
  , naturalRankOfOrdinal
  , omegaPower
  , ordinalAtNaturalRank
  , ordinalLT
  )
import Dominion (Dominion, dominion)
import Dot (Dot)
import FixedPoint
  ( FixedPoint
  , FixedPointValue
  , fixedPoint
  , fixedPointLayer
  , rollFixedPoint
  , rollFixedPointValue
  , unrollFixedPoint
  , unrollFixedPointValue
  , withFixedPointValue
  )
import MapOperators.ConcatOperator
  ( ConcatOperatorValue
  , ConcatOperatorValues
  )
import MapOperators.Syntax.ConcatOperatorSyntax ((<.>))
import MapOperators.SequentialOperator (SequentialPresentation)
import Numeric.Natural (Natural)
import StableConfederalData
  ( StableConfederalData
  , StableConfederalDataHom
  )

-- | The nominal tag is derived from the preceding level.  This keeps every
-- level distinct while leaving clients with only the inductive predecessor
-- parameter to supply.
data SuperEllipsisTag predecessor

-- | The successor of one level in the super-ellipsis hierarchy.
--
-- The base of the induction is @Dot@.  This module remains below @Ellipsis@
-- in the dependency graph, so higher levels cannot cycle through their
-- rank-one specialization.
type SuperEllipsis predecessor =
  FixedPoint
    (SuperEllipsisTag predecessor)
    (ConcatOperatorValues predecessor)

-- | One observable @predecessor <.> SuperEllipsis predecessor@ layer.
type SuperEllipsisLayer predecessor =
  FixedPointValue
    (SuperEllipsisTag predecessor)
    (ConcatOperatorValues predecessor)

-- | A type-level index for the finite super-ellipsis hierarchy.
data SuperEllipsisLevel
  = DotLevel
  | NextLevel SuperEllipsisLevel

-- | Recover the stable-confederal carrier at a type-level hierarchy index.
type family SuperEllipsisAt (level :: SuperEllipsisLevel) where
  SuperEllipsisAt 'DotLevel = Dot
  SuperEllipsisAt ('NextLevel level) =
    SuperEllipsis (SuperEllipsisAt level)

-- | Runtime evidence for one member of the inductive hierarchy.  The type
-- parameter identifies the corresponding stable-confederal carrier, while
-- the hidden natural records its finite exponent.
type role SuperEllipsisRank nominal
newtype SuperEllipsisRank target = SuperEllipsisRank Natural

-- | Runtime rank evidence for every target in the inductive hierarchy.
class SuperEllipsisTarget target where
  type SuperEllipsisTargetLevel target :: SuperEllipsisLevel
  superEllipsisTargetRank :: SuperEllipsisRank target
  superEllipsisTargetLevelNatural :: Natural

instance SuperEllipsisTarget Dot where
  type SuperEllipsisTargetLevel Dot = 'DotLevel
  superEllipsisTargetRank = dotSuperEllipsisRank
  superEllipsisTargetLevelNatural = 0

instance SuperEllipsisTarget predecessor =>
    SuperEllipsisTarget (SuperEllipsis predecessor) where
  type SuperEllipsisTargetLevel (SuperEllipsis predecessor) =
    'NextLevel (SuperEllipsisTargetLevel predecessor)
  superEllipsisTargetRank =
    nextSuperEllipsisRank superEllipsisTargetRank
  superEllipsisTargetLevelNatural =
    1 + superEllipsisTargetLevelNatural @predecessor

-- | Runtime rank evidence for a level produced by type-level arithmetic.
class KnownSuperEllipsisLevel level where
  knownSuperEllipsisRank :: SuperEllipsisRank (SuperEllipsisAt level)
  knownSuperEllipsisLevelNatural :: Natural

instance KnownSuperEllipsisLevel 'DotLevel where
  knownSuperEllipsisRank = dotSuperEllipsisRank
  knownSuperEllipsisLevelNatural = 0

instance KnownSuperEllipsisLevel level =>
    KnownSuperEllipsisLevel ('NextLevel level) where
  knownSuperEllipsisRank =
    nextSuperEllipsisRank (knownSuperEllipsisRank @level)
  knownSuperEllipsisLevelNatural =
    1 + knownSuperEllipsisLevelNatural @level

-- | Rank zero: the singleton 'Dot', whose order type is one.
dotSuperEllipsisRank :: SuperEllipsisRank Dot
dotSuperEllipsisRank = SuperEllipsisRank 0

-- | Advance from rank @n@ to rank @n+1@.
nextSuperEllipsisRank
  :: SuperEllipsisRank target
  -> SuperEllipsisRank (SuperEllipsis target)
nextSuperEllipsisRank (SuperEllipsisRank value) =
  SuperEllipsisRank (value + 1)

-- | The ordinal order type represented at a rank: one at rank zero and
-- @omega^n@ at every positive finite rank.
superEllipsisRankOrderType :: SuperEllipsisRank target -> Ordinal
superEllipsisRankOrderType (SuperEllipsisRank value) = omegaPower value

-- | A position certified to lie below one super-ellipsis rank.
type role SuperEllipsisTerminal nominal
newtype SuperEllipsisTerminal target = SuperEllipsisTerminal
  { superEllipsisTerminalPosition :: Ordinal
  }
  deriving (Eq, Show)

-- | Refine an ordinal to a position at the selected rank.
superEllipsisTerminal
  :: SuperEllipsisRank target
  -> Ordinal
  -> Maybe (SuperEllipsisTerminal target)
superEllipsisTerminal valueRank position
  | ordinalLT position (superEllipsisRankOrderType valueRank) =
      Just (SuperEllipsisTerminal position)
  | otherwise = Nothing

-- | Zero belongs to every rank in the hierarchy.
superEllipsisZeroTerminal
  :: SuperEllipsisRank target
  -> SuperEllipsisTerminal target
superEllipsisZeroTerminal _ = SuperEllipsisTerminal (finiteOrdinal 0)

-- | The countable dominion of all positions below a rank.  Fixed-length
-- coefficient vectors give a duplicate-free enumeration of @omega^n@.
superEllipsisDominion
  :: SuperEllipsisRank target
  -> Dominion (SuperEllipsisTerminal target)
superEllipsisDominion valueRank@(SuperEllipsisRank level) =
  dominion terminalCode terminalAt (const ())
  where
    terminalAt code =
      ordinalAtNaturalRank level code
        >>= superEllipsisTerminal valueRank

    terminalCode terminal =
      case naturalRankOfOrdinal
        level (superEllipsisTerminalPosition terminal) of
          Just code -> code
          Nothing -> 0

-- | The canonical chain of all terminals in ordinal order.
superEllipsisChain
  :: SuperEllipsisRank target
  -> Chain (SuperEllipsisTerminal target)
superEllipsisChain valueRank =
  chain
    (superEllipsisRankOrderType valueRank)
    superEllipsisTerminalPosition
    (superEllipsisTerminal valueRank)
    (const ())
    (\_ _ -> ())
    (const ())

-- | Concrete chained-Atlas presentation associated with a rank.
type SuperEllipsisAtlasObject target =
  ChainedDominionAtlasObject (SuperEllipsisTerminal target)

superEllipsisAtlas
  :: SuperEllipsisRank target
  -> ChainedDominionAtlas (SuperEllipsisTerminal target)
superEllipsisAtlas valueRank =
  chainedDominionAtlas
    zero
    (superEllipsisChain valueRank)
    (superEllipsisDominion valueRank)
  where
    zero = superEllipsisZeroTerminal valueRank

superEllipsisAtlasMap
  :: SuperEllipsisRank target
  -> AtlasMap (SuperEllipsisAtlasObject target)
superEllipsisAtlasMap valueRank =
  chainedDominionAtlasMap
    zero
    (superEllipsisChain valueRank)
    (superEllipsisDominion valueRank)
  where
    zero = superEllipsisZeroTerminal valueRank

superEllipsisCoalitionElement
  :: SuperEllipsisRank target
  -> SuperEllipsisTerminal target
  -> CoalitionElement (SuperEllipsisAtlasObject target)
superEllipsisCoalitionElement valueRank =
  chainedDominionCoalitionElement
    (superEllipsisZeroTerminal valueRank)
    (superEllipsisChain valueRank)
    (superEllipsisDominion valueRank)

-- | Tie the guarded recursive equation for the successor of @predecessor@.
superEllipsis
  :: SequentialPresentation predecessor
  => StableConfederalData predecessor
  -> StableConfederalData (SuperEllipsis predecessor)
superEllipsis predecessor = fixedPoint (predecessor <.>)

-- | Expose one layer of the recursive equation.
superEllipsisUnfolded
  :: SequentialPresentation predecessor
  => StableConfederalData predecessor
  -> StableConfederalData
       (ConcatOperatorValues predecessor (SuperEllipsis predecessor))
superEllipsisUnfolded predecessor = fixedPointLayer (predecessor <.>)

-- | Fold one recursive layer into its super ellipsis.
superEllipsisFold
  :: SequentialPresentation predecessor
  => StableConfederalData predecessor
  -> StableConfederalDataHom
       (ConcatOperatorValues predecessor (SuperEllipsis predecessor))
       (SuperEllipsis predecessor)
superEllipsisFold predecessor = rollFixedPoint (predecessor <.>)

-- | Unfold a super ellipsis into one recursive layer.
superEllipsisUnfold
  :: SequentialPresentation predecessor
  => StableConfederalData predecessor
  -> StableConfederalDataHom
       (SuperEllipsis predecessor)
       (ConcatOperatorValues predecessor (SuperEllipsis predecessor))
superEllipsisUnfold predecessor = unrollFixedPoint (predecessor <.>)

-- | Introduce one recursive value layer.
rollSuperEllipsisLayer
  :: ConcatOperatorValue
       predecessor
       (SuperEllipsis predecessor)
       object
  -> SuperEllipsisLayer predecessor object
rollSuperEllipsisLayer = rollFixedPointValue

-- | Observe one recursive value layer.
unrollSuperEllipsisLayer
  :: SuperEllipsisLayer predecessor object
  -> ConcatOperatorValue
       predecessor
       (SuperEllipsis predecessor)
       object
unrollSuperEllipsisLayer = unrollFixedPointValue

-- | Observe one recursive layer without exposing its representation.
withSuperEllipsisLayer
  :: SuperEllipsisLayer predecessor object
  -> (ConcatOperatorValue
        predecessor
        (SuperEllipsis predecessor)
        object
      -> result)
  -> result
withSuperEllipsisLayer = withFixedPointValue
