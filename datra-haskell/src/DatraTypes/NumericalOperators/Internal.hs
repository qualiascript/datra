{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module NumericalOperators.Internal
  ( applyOrdinalAddition
  , applyOrdinalMultiplication
  , applyOrdinalExponentOperator
  ) where

import DatraOrdinal (naturalAtOrdinal)
import EllipsisNatural (EllipsisNatural)
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
  , numericalOperandDenotation
  )
import NumericalOperators.Semantics
  ( addNumericalDenotations
  , exponentiateNumericalDenotation
  , multiplyNumericalDenotations
  , numericalDenotationOrdinal
  )
import SuperEllipsisValue
  ( SuperEllipsisValue
  , superEllipsisValue
  , superEllipsisValueOrdinal
  )

-- | Apply a binary ordinal operation after promoting both operands to their
-- least common super-ellipsis rank.
applyOrdinalAddition
  :: forall left right result.
     ( NumericalOperand left
     , NumericalOperand right
     , KnownSuperEllipsisLevel (BinaryNumericalLevel left right)
     )
  => left
  -> right
  -> (forall resultScope.
        NumericalResult left right resultScope -> result)
  -> Maybe result
applyOrdinalAddition left right useResult = do
  superEllipsisValue
    (knownSuperEllipsisRank @(BinaryNumericalLevel left right))
    (numericalDenotationOrdinal
      (addNumericalDenotations
        (numericalOperandDenotation left)
        (numericalOperandDenotation right)))
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
  => left
  -> right
  -> (forall resultScope.
        MultiplicationResult left right resultScope -> result)
  -> Maybe result
applyOrdinalMultiplication left right useResult = do
  superEllipsisValue
    (knownSuperEllipsisRank
      @(MultiplicationNumericalLevel left right))
    (numericalDenotationOrdinal
      (multiplyNumericalDenotations
        (numericalOperandDenotation left)
        (numericalOperandDenotation right)))
    useResult

-- | Apply ordinal exponentiation with a finite Ellipsis-natural exponent.
applyOrdinalExponentOperator
  :: forall base exponentScope result.
     ( NumericalOperand base
     , KnownSuperEllipsisLevel (NumericalOperandLevel base)
     )
  => base
  -> EllipsisNatural exponentScope
  -> (forall resultScope.
        SuperEllipsisValue
          (NumericalOperandTarget base) resultScope -> result)
  -> Maybe result
applyOrdinalExponentOperator base exponentValue useResult = do
  power <- naturalAtOrdinal (superEllipsisValueOrdinal exponentValue)
  superEllipsisValue
    (knownSuperEllipsisRank @(NumericalOperandLevel base))
    (numericalDenotationOrdinal
      (exponentiateNumericalDenotation
        (numericalOperandDenotation base) power))
    useResult
