{-# LANGUAGE RankNTypes #-}

module NumericalOperators.Internal
  ( applyOrdinalOperator
  , applyOrdinalExponentOperator
  ) where

import DatraOrdinal (Ordinal, naturalAtOrdinal)
import EllipsisNatural (EllipsisNatural)
import Numeric.Natural (Natural)
import SuperEllipsisRange (superEllipsisRangeRank)
import SuperEllipsisValue
  ( SuperEllipsisValue
  , superEllipsisValue
  , superEllipsisValueOrdinal
  )

-- | Apply a closed binary ordinal operation at one super-ellipsis rank.
-- Construction of the singleton result also checks that it still fits below
-- that rank's order type.
applyOrdinalOperator
  :: (Ordinal -> Ordinal -> Ordinal)
  -> SuperEllipsisValue target leftScope
  -> SuperEllipsisValue target rightScope
  -> (forall resultScope.
        SuperEllipsisValue target resultScope -> result)
  -> Maybe result
applyOrdinalOperator operator left right useResult = do
  leftValue <- superEllipsisValueOrdinal left
  rightValue <- superEllipsisValueOrdinal right
  superEllipsisValue
    (superEllipsisRangeRank left)
    (operator leftValue rightValue)
    useResult

-- | Apply ordinal exponentiation with a finite Ellipsis-natural exponent.
applyOrdinalExponentOperator
  :: (Ordinal -> Natural -> Ordinal)
  -> SuperEllipsisValue target baseScope
  -> EllipsisNatural exponentScope
  -> (forall resultScope.
        SuperEllipsisValue target resultScope -> result)
  -> Maybe result
applyOrdinalExponentOperator operator base exponentValue useResult = do
  baseValue <- superEllipsisValueOrdinal base
  exponentOrdinal <- superEllipsisValueOrdinal exponentValue
  power <- naturalAtOrdinal exponentOrdinal
  superEllipsisValue
    (superEllipsisRangeRank base)
    (operator baseValue power)
    useResult
