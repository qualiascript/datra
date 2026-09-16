{-# LANGUAGE RankNTypes #-}

module NumericalOperators.Internal
  ( applyNaturalOperator
  ) where

import EllipsisNatural qualified as Datra
import DatraOrdinal (naturalAtOrdinal)
import SuperEllipsisRange
  ( superEllipsisRangeLowerBound
  , superEllipsisRangeUpperBound
  )
import Numeric.Natural (Natural)
import Prelude (Maybe (..), (==), (>>=))

import qualified Prelude

applyNaturalOperator
  :: (Natural -> Natural -> Natural)
  -> Datra.EllipsisNatural leftScope
  -> Datra.EllipsisNatural rightScope
  -> (forall resultScope. Datra.EllipsisNatural resultScope -> result)
  -> Maybe result
applyNaturalOperator operator left right useResult = do
  leftValue <- naturalValue left
  rightValue <- naturalValue right
  Datra.ellipsisNatural (operator leftValue rightValue) useResult

-- Check the singleton invariant instead of interpreting an arbitrary range.
naturalValue :: Datra.EllipsisNatural scope -> Maybe Natural
naturalValue natural = do
  value <- superEllipsisRangeLowerBound natural >>= naturalAtOrdinal
  target <- superEllipsisRangeUpperBound natural >>= naturalAtOrdinal
  if target == value Prelude.+ 1
    then Just value
    else Nothing
