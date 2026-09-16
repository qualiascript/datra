{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Values and stable data that denote ordinals for numerical operators.
module NumericalOperators.NumericalOperand
  ( NumericalOperand
  , numericalOperandOrdinal
  , NumericalOperandLevel
  , NumericalOperandTarget
  , BinaryNumericalLevel
  , BinaryNumericalTarget
  , NumericalResult
  , MultiplicationNumericalLevel
  , MultiplicationNumericalTarget
  , MultiplicationResult
  , SuperEllipsisLevel (..)
  , SuperEllipsisAt
  , KnownSuperEllipsisLevel
  , knownSuperEllipsisRank
  ) where

import DatraOrdinal (Ordinal)
import Dot (Dot)
import StableConfederalData (StableConfederalData)
import SuperEllipsis
  ( SuperEllipsis
  , SuperEllipsisRank
  , dotSuperEllipsisRank
  , nextSuperEllipsisRank
  , superEllipsisRankOrderType
  )
import SuperEllipsisRange (SuperEllipsisRange)
import SuperEllipsisValue
  ( SuperEllipsisValue
  , superEllipsisValueOrdinal
  )

data SuperEllipsisLevel
  = DotLevel
  | NextLevel SuperEllipsisLevel

type family SuperEllipsisAt (level :: SuperEllipsisLevel) where
  SuperEllipsisAt 'DotLevel = Dot
  SuperEllipsisAt ('NextLevel level) =
    SuperEllipsis (SuperEllipsisAt level)

class KnownSuperEllipsisLevel level where
  knownSuperEllipsisRank :: SuperEllipsisRank (SuperEllipsisAt level)

instance KnownSuperEllipsisLevel 'DotLevel where
  knownSuperEllipsisRank = dotSuperEllipsisRank

instance KnownSuperEllipsisLevel level =>
    KnownSuperEllipsisLevel ('NextLevel level) where
  knownSuperEllipsisRank =
    nextSuperEllipsisRank (knownSuperEllipsisRank @level)

class SuperEllipsisCarrier target where
  type SuperEllipsisCarrierLevel target :: SuperEllipsisLevel
  superEllipsisCarrierRank :: SuperEllipsisRank target

instance SuperEllipsisCarrier Dot where
  type SuperEllipsisCarrierLevel Dot = 'DotLevel
  superEllipsisCarrierRank = dotSuperEllipsisRank

instance SuperEllipsisCarrier predecessor =>
    SuperEllipsisCarrier (SuperEllipsis predecessor) where
  type SuperEllipsisCarrierLevel (SuperEllipsis predecessor) =
    'NextLevel (SuperEllipsisCarrierLevel predecessor)
  superEllipsisCarrierRank =
    nextSuperEllipsisRank (superEllipsisCarrierRank @predecessor)

class NumericalOperand operand where
  type NumericalOperandLevel operand :: SuperEllipsisLevel
  numericalOperandOrdinal :: operand -> Maybe Ordinal

-- Explicit singleton values retain their declared carrier rank.
instance SuperEllipsisCarrier target =>
    NumericalOperand (SuperEllipsisRange target scope) where
  type NumericalOperandLevel (SuperEllipsisRange target scope) =
    SuperEllipsisCarrierLevel target
  numericalOperandOrdinal = superEllipsisValueOrdinal

-- A stable datum denotes its order type, embedded in the next rank:
-- Dot = 1, Ellipsis = omega, and so on.
instance SuperEllipsisCarrier target =>
    NumericalOperand (StableConfederalData target) where
  type NumericalOperandLevel (StableConfederalData target) =
    'NextLevel (SuperEllipsisCarrierLevel target)
  numericalOperandOrdinal _ =
    Just (superEllipsisRankOrderType (superEllipsisCarrierRank @target))

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
