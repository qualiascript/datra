{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Values and stable data that denote ordinals for numerical operators.
module NumericalOperators.NumericalOperand
  ( NumericalOperand
  , NumericalForm (..)
  , NumericalOperandForm
  , numericalOperandOrdinal
  , NumericalOperandLevel
  , NumericalOperandTarget
  , BinaryNumericalLevel
  , BinaryNumericalTarget
  , NumericalResult
  , MultiplicationNumericalLevel
  , MultiplicationNumericalTarget
  , MultiplicationResult
  , PreviousSuperEllipsisLevel
  , SuperEllipsisLevel (..)
  , SuperEllipsisAt
  , KnownSuperEllipsisLevel
  , knownSuperEllipsisRank
  , knownSuperEllipsisLevelNatural
  , KnownSuperEllipsisData
  , knownSuperEllipsisData
  , SuperEllipsisTarget
  , SuperEllipsisTargetLevel
  , superEllipsisTargetLevelNatural
  , AddSuperEllipsisLevels
  , SomeSuperEllipsis
  , someSuperEllipsisLevel
  , someSuperEllipsis
  , withSomeSuperEllipsis
  ) where

import DatraOrdinal (Ordinal)
import Dot (dot)
import Numeric.Natural (Natural)
import MapOperators.SequentialOperator (SequentialPresentation)
import StableConfederalData (StableConfederalData)
import SuperEllipsis
  ( KnownSuperEllipsisLevel
  , SuperEllipsisAt
  , SuperEllipsisLevel (..)
  , SuperEllipsisTarget
  , SuperEllipsisTargetLevel
  , knownSuperEllipsisRank
  , knownSuperEllipsisLevelNatural
  , superEllipsis
  , superEllipsisRankOrderType
  , superEllipsisTargetLevelNatural
  , superEllipsisTargetRank
  )
import SuperEllipsisValue
  ( SuperEllipsisValue
  , superEllipsisValueOrdinal
  )

class KnownSuperEllipsisData level where
  knownSuperEllipsisData :: StableConfederalData (SuperEllipsisAt level)

instance KnownSuperEllipsisData 'DotLevel where
  knownSuperEllipsisData = dot

instance
    ( KnownSuperEllipsisData level
    , SequentialPresentation (SuperEllipsisAt level)
    ) =>
    KnownSuperEllipsisData ('NextLevel level) where
  knownSuperEllipsisData =
    superEllipsis (knownSuperEllipsisData @level)

-- | Whether an operand is an explicit ordinal or a formulation whose order
-- type supplies the ordinal denotation.
data NumericalForm
  = ExplicitNumerical
  | FormulationNumerical

class NumericalOperand operand where
  type NumericalOperandForm operand :: NumericalForm
  type NumericalOperandLevel operand :: SuperEllipsisLevel
  numericalOperandOrdinal :: operand -> Ordinal

-- Explicit singleton values retain their declared carrier rank.
instance SuperEllipsisTarget target =>
    NumericalOperand (SuperEllipsisValue target scope) where
  type NumericalOperandForm (SuperEllipsisValue target scope) =
    'ExplicitNumerical
  type NumericalOperandLevel (SuperEllipsisValue target scope) =
    SuperEllipsisTargetLevel target
  numericalOperandOrdinal = superEllipsisValueOrdinal

-- A stable datum denotes its order type, embedded in the next rank:
-- Dot = 1, Ellipsis = omega, and so on.
instance SuperEllipsisTarget target =>
    NumericalOperand (StableConfederalData target) where
  type NumericalOperandForm (StableConfederalData target) =
    'FormulationNumerical
  type NumericalOperandLevel (StableConfederalData target) =
    'NextLevel (SuperEllipsisTargetLevel target)
  numericalOperandOrdinal _ =
    superEllipsisRankOrderType (superEllipsisTargetRank @target)

type family MaximumSuperEllipsisLevel left right where
  MaximumSuperEllipsisLevel 'DotLevel right = right
  MaximumSuperEllipsisLevel left 'DotLevel = left
  MaximumSuperEllipsisLevel ('NextLevel left) ('NextLevel right) =
    'NextLevel (MaximumSuperEllipsisLevel left right)

type NumericalOperandTarget operand =
  SuperEllipsisAt (NumericalOperandLevel operand)

type BinaryNumericalLevel left right =
  MaximumSuperEllipsisLevel
    (NumericalOperandLevel left)
    (NumericalOperandLevel right)

type BinaryNumericalTarget left right =
  SuperEllipsisAt (BinaryNumericalLevel left right)

type NumericalResult left right =
  SuperEllipsisValue (BinaryNumericalTarget left right)

type family AddSuperEllipsisLevels left right where
  AddSuperEllipsisLevels 'DotLevel right = right
  AddSuperEllipsisLevels ('NextLevel left) right =
    'NextLevel (AddSuperEllipsisLevels left right)

-- Products below omega^m and omega^n lie below omega^(m+n-1). Rank one is
-- therefore closed under multiplication, while omega times omega promotes
-- from rank two to rank three.
type family MultiplicationSuperEllipsisLevel left right where
  MultiplicationSuperEllipsisLevel 'DotLevel _ = 'DotLevel
  MultiplicationSuperEllipsisLevel _ 'DotLevel = 'DotLevel
  MultiplicationSuperEllipsisLevel
      ('NextLevel left) ('NextLevel right) =
    'NextLevel (AddSuperEllipsisLevels left right)

type MultiplicationNumericalLevel left right =
  MultiplicationSuperEllipsisLevel
    (NumericalOperandLevel left)
    (NumericalOperandLevel right)

type MultiplicationNumericalTarget left right =
  SuperEllipsisAt (MultiplicationNumericalLevel left right)

type MultiplicationResult left right =
  SuperEllipsisValue (MultiplicationNumericalTarget left right)

type family PreviousSuperEllipsisLevel level where
  PreviousSuperEllipsisLevel ('NextLevel level) = level

-- | A formulation whose precise finite level is chosen at runtime.
data SomeSuperEllipsis where
  SomeSuperEllipsis
    :: ( SequentialPresentation target
       , SuperEllipsisTarget target
       )
    => Natural
    -> StableConfederalData target
    -> SomeSuperEllipsis

someSuperEllipsis :: Natural -> SomeSuperEllipsis
someSuperEllipsis 0 = SomeSuperEllipsis 0 dot
someSuperEllipsis level =
  case someSuperEllipsis (level - 1) of
    SomeSuperEllipsis _ predecessor ->
      SomeSuperEllipsis level (superEllipsis predecessor)

someSuperEllipsisLevel :: SomeSuperEllipsis -> Natural
someSuperEllipsisLevel (SomeSuperEllipsis level _) = level

withSomeSuperEllipsis
  :: SomeSuperEllipsis
  -> (forall target.
        ( SequentialPresentation target
        , SuperEllipsisTarget target
        ) =>
        StableConfederalData target -> result)
  -> result
withSomeSuperEllipsis (SomeSuperEllipsis _ value) useValue = useValue value
