{-# LANGUAGE RankNTypes #-}

module NumericalOperators.Internal
  ( applyNaturalOperator
  ) where

import EllipsisNatural (EllipsisNatural, ellipsisNatural)
import EllipsisNaturalRange
  ( ellipsisNaturalRangeLowerBound
  , ellipsisNaturalRangeUpperBound
  )
import Numeric.Natural (Natural)
import Prelude (Maybe (..), (==))

import qualified Prelude

applyNaturalOperator
  :: (Natural -> Natural -> Natural)
  -> EllipsisNatural leftScope
  -> EllipsisNatural rightScope
  -> (forall resultScope. EllipsisNatural resultScope -> result)
  -> Maybe result
applyNaturalOperator operator left right useResult = do
  leftValue <- ellipsisNaturalValue left
  rightValue <- ellipsisNaturalValue right
  ellipsisNatural (operator leftValue rightValue) useResult

-- EllipsisNatural is currently an abstract synonym for EllipsisNaturalRange.
-- Check the singleton invariant here instead of interpreting an arbitrary
-- range as a number.
ellipsisNaturalValue :: EllipsisNatural scope -> Maybe Natural
ellipsisNaturalValue natural = do
  value <- ellipsisNaturalRangeLowerBound natural
  target <- ellipsisNaturalRangeUpperBound natural
  if target == value Prelude.+ 1
    then Just value
    else Nothing
