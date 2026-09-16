{-# LANGUAGE RankNTypes #-}

module NumericalOperators.Internal
  ( applyNaturalOperator
  ) where

import Natural qualified as Datra
import NaturalRange
  ( naturalRangeLowerBound
  , naturalRangeUpperBound
  )
import Numeric.Natural (Natural)
import Prelude (Maybe (..), (==))

import qualified Prelude

applyNaturalOperator
  :: (Natural -> Natural -> Natural)
  -> Datra.Natural leftScope
  -> Datra.Natural rightScope
  -> (forall resultScope. Datra.Natural resultScope -> result)
  -> Maybe result
applyNaturalOperator operator left right useResult = do
  leftValue <- naturalValue left
  rightValue <- naturalValue right
  Datra.natural (operator leftValue rightValue) useResult

-- Check the singleton invariant instead of interpreting an arbitrary range.
naturalValue :: Datra.Natural scope -> Maybe Natural
naturalValue natural = do
  value <- naturalRangeLowerBound natural
  target <- naturalRangeUpperBound natural
  if target == value Prelude.+ 1
    then Just value
    else Nothing
