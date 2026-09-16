{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module NumericalOperators.Internal
  ( applyOrdinalOperator
  , applyOrdinalMultiplication
  , applyOrdinalExponentOperator
  ) where

import DatraOrdinal (Ordinal, naturalAtOrdinal)
import EllipsisNatural (EllipsisNatural)
import Numeric.Natural (Natural)
import NumericalOperators.NumericalOperand
  ( BinaryNumericalLevel
  , KnownSuperEllipsisLevel
  , MultiplicationNumericalLevel
  , MultiplicationResult
  , NumericalOperand
  , NumericalOperandLevel
  , NumericalOperandTarget
  , NumericalResult
  , knownSuperEllipsisRank
  , numericalOperandOrdinal
  )
import SuperEllipsisValue
  ( SuperEllipsisValue
  , superEllipsisValue
  , superEllipsisValueOrdinal
  )

-- | Apply a binary ordinal operation after promoting both operands to their
-- least common super-ellipsis rank.
applyOrdinalOperator
  :: forall left right result.
     ( NumericalOperand left
     , NumericalOperand right
     , KnownSuperEllipsisLevel (BinaryNumericalLevel left right)
     )
  => (Ordinal -> Ordinal -> Ordinal)
  -> left
  -> right
  -> (forall resultScope.
        NumericalResult left right resultScope -> result)
  -> Maybe result
applyOrdinalOperator operator left right useResult = do
  leftValue <- numericalOperandOrdinal left
  rightValue <- numericalOperandOrdinal right
  superEllipsisValue
    (knownSuperEllipsisRank @(BinaryNumericalLevel left right))
    (operator leftValue rightValue)
    useResult

-- | Apply ordinal multiplication at the rank guaranteed to contain the
-- product of the two operand ranks.
applyOrdinalMultiplication
  :: forall left right result.
     ( NumericalOperand left
     , NumericalOperand right
     , KnownSuperEllipsisLevel
         (MultiplicationNumericalLevel left right)
     )
  => (Ordinal -> Ordinal -> Ordinal)
  -> left
  -> right
  -> (forall resultScope.
        MultiplicationResult left right resultScope -> result)
  -> Maybe result
applyOrdinalMultiplication operator left right useResult = do
  leftValue <- numericalOperandOrdinal left
  rightValue <- numericalOperandOrdinal right
  superEllipsisValue
    (knownSuperEllipsisRank
      @(MultiplicationNumericalLevel left right))
    (operator leftValue rightValue)
    useResult

-- | Apply ordinal exponentiation with a finite Ellipsis-natural exponent.
applyOrdinalExponentOperator
  :: forall base exponentScope result.
     ( NumericalOperand base
     , KnownSuperEllipsisLevel (NumericalOperandLevel base)
     )
  => (Ordinal -> Natural -> Ordinal)
  -> base
  -> EllipsisNatural exponentScope
  -> (forall resultScope.
        SuperEllipsisValue
          (NumericalOperandTarget base) resultScope -> result)
  -> Maybe result
applyOrdinalExponentOperator operator base exponentValue useResult = do
  baseValue <- numericalOperandOrdinal base
  exponentOrdinal <- superEllipsisValueOrdinal exponentValue
  power <- naturalAtOrdinal exponentOrdinal
  superEllipsisValue
    (knownSuperEllipsisRank @(NumericalOperandLevel base))
    (operator baseValue power)
    useResult
