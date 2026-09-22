-- | Direction-aware inclusive intervals over the naturals.
--
-- Natural-range federations and valued-natural federations differ in their
-- members, but share the same interval geometry.  This module owns that
-- geometry without knowing how either federation is represented.
module NaturalRange.Interval
  ( NaturalRangeTarget (..)
  , NaturalRangeDirection (..)
  , NaturalInterval
  , naturalInterval
  , naturalIntervalStart
  , naturalIntervalTarget
  , naturalIntervalDirection
  , naturalIntervalBounds
  , naturalIntervalContains
  , naturalIntervalOverlapWitness
  , naturalIntervalContainedIn
  , directedSubintervalFits
  , naturalRangeTargetAsSuperEllipsisRangeTarget
  ) where

import DatraOrdinal (finiteOrdinal)
import Numeric.Natural (Natural)
import SuperEllipsisRange.Description
  ( SuperEllipsisRangeTarget (GivenTarget, MinusSign, PlusSign) )

data NaturalRangeTarget
  = FiniteNaturalTarget Natural
  | UpwardsTarget
  deriving (Eq, Show)

data NaturalRangeDirection
  = AscendingNaturalRange
  | DescendingNaturalRange
  deriving (Eq, Show)

data NaturalInterval = NaturalInterval
  { naturalIntervalStart :: Natural
  , naturalIntervalTarget :: NaturalRangeTarget
  }

naturalInterval :: Natural -> NaturalRangeTarget -> NaturalInterval
naturalInterval = NaturalInterval

naturalIntervalDirection :: NaturalInterval -> NaturalRangeDirection
naturalIntervalDirection interval =
  case naturalIntervalTarget interval of
    UpwardsTarget -> AscendingNaturalRange
    FiniteNaturalTarget target
      | naturalIntervalStart interval <= target -> AscendingNaturalRange
      | otherwise -> DescendingNaturalRange

naturalIntervalBounds :: NaturalInterval -> (Natural, Maybe Natural)
naturalIntervalBounds interval =
  case naturalIntervalTarget interval of
    UpwardsTarget -> (naturalIntervalStart interval, Nothing)
    FiniteNaturalTarget target ->
      ( min (naturalIntervalStart interval) target
      , Just (max (naturalIntervalStart interval) target)
      )

naturalIntervalContains :: NaturalInterval -> Natural -> Bool
naturalIntervalContains interval value =
  let (lower, upper) = naturalIntervalBounds interval
  in value >= lower && maybe True (value <=) upper

naturalIntervalOverlapWitness
  :: NaturalInterval
  -> NaturalInterval
  -> Maybe Natural
naturalIntervalOverlapWitness left right =
  let (leftLower, leftUpper) = naturalIntervalBounds left
      (rightLower, rightUpper) = naturalIntervalBounds right
      lower = max leftLower rightLower
  in if withinUpper lower leftUpper && withinUpper lower rightUpper
      then Just lower
      else Nothing

naturalIntervalContainedIn :: NaturalInterval -> NaturalInterval -> Bool
naturalIntervalContainedIn source target =
  let (sourceLower, sourceUpper) = naturalIntervalBounds source
      (targetLower, targetUpper) = naturalIntervalBounds target
  in targetLower <= sourceLower
      && upperBoundContained sourceUpper targetUpper

directedSubintervalFits
  :: NaturalInterval
  -> Natural
  -> Natural
  -> Bool
directedSubintervalFits outer start target =
  case naturalIntervalTarget outer of
    UpwardsTarget ->
      naturalIntervalStart outer <= start && start <= target
    FiniteNaturalTarget outerTarget
      | naturalIntervalStart outer <= outerTarget ->
          naturalIntervalStart outer <= start
            && start <= target
            && target <= outerTarget
      | otherwise ->
          outerTarget <= target
            && target <= start
            && start <= naturalIntervalStart outer

naturalRangeTargetAsSuperEllipsisRangeTarget
  :: Natural
  -> NaturalRangeTarget
  -> SuperEllipsisRangeTarget
naturalRangeTargetAsSuperEllipsisRangeTarget _ UpwardsTarget = PlusSign
naturalRangeTargetAsSuperEllipsisRangeTarget start (FiniteNaturalTarget target)
  | start <= target = GivenTarget (finiteOrdinal (target + 1))
  | target == 0 = MinusSign
  | otherwise = GivenTarget (finiteOrdinal (target - 1))

withinUpper :: Natural -> Maybe Natural -> Bool
withinUpper _ Nothing = True
withinUpper value (Just upper) = value <= upper

upperBoundContained :: Maybe Natural -> Maybe Natural -> Bool
upperBoundContained Nothing Nothing = True
upperBoundContained Nothing (Just _) = False
upperBoundContained (Just _) Nothing = True
upperBoundContained (Just source) (Just target) = source <= target
