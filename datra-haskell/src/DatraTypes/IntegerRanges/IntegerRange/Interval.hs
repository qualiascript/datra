-- | Direction-aware inclusive intervals over the integers.
module IntegerRange.Interval
  ( IntegerRangeTarget (..)
  , IntegerRangeDirection (..)
  , IntegerInterval
  , integerInterval
  , integerIntervalStart
  , integerIntervalTarget
  , integerIntervalDirection
  , integerIntervalBounds
  , integerIntervalContains
  , integerIntervalOverlapWitness
  , integerIntervalContainedIn
  , directedIntegerSubintervalFits
  , integerIntervalWidth
  , integerAtOffset
  , integerOffset
  ) where

import Numeric.Natural (Natural)

data IntegerRangeTarget
  = FiniteIntegerTarget Integer
  | UpwardsIntegerTarget
  | DownwardsIntegerTarget
  | AllIntegersTarget
  deriving (Eq, Show)

data IntegerRangeDirection
  = AscendingIntegerRange
  | DescendingIntegerRange
  | ProductIntegerRange
  deriving (Eq, Show)

data IntegerInterval = IntegerInterval
  { integerIntervalStart :: Integer
  , integerIntervalTarget :: IntegerRangeTarget
  }

integerInterval :: Integer -> IntegerRangeTarget -> IntegerInterval
integerInterval = IntegerInterval

integerIntervalDirection :: IntegerInterval -> IntegerRangeDirection
integerIntervalDirection interval =
  case integerIntervalTarget interval of
    UpwardsIntegerTarget -> AscendingIntegerRange
    DownwardsIntegerTarget -> DescendingIntegerRange
    AllIntegersTarget -> ProductIntegerRange
    FiniteIntegerTarget target
      | integerIntervalStart interval <= target -> AscendingIntegerRange
      | otherwise -> DescendingIntegerRange

integerIntervalBounds
  :: IntegerInterval
  -> (Maybe Integer, Maybe Integer)
integerIntervalBounds interval =
  case integerIntervalTarget interval of
    UpwardsIntegerTarget -> (Just (integerIntervalStart interval), Nothing)
    DownwardsIntegerTarget -> (Nothing, Just (integerIntervalStart interval))
    AllIntegersTarget -> (Nothing, Nothing)
    FiniteIntegerTarget target ->
      ( Just (min (integerIntervalStart interval) target)
      , Just (max (integerIntervalStart interval) target)
      )

integerIntervalContains :: IntegerInterval -> Integer -> Bool
integerIntervalContains interval value =
  let (lower, upper) = integerIntervalBounds interval
  in maybe True (<= value) lower && maybe True (value <=) upper

integerIntervalOverlapWitness
  :: IntegerInterval
  -> IntegerInterval
  -> Maybe Integer
integerIntervalOverlapWitness left right =
  let (leftLower, leftUpper) = integerIntervalBounds left
      (rightLower, rightUpper) = integerIntervalBounds right
      lower = maximumMaybe leftLower rightLower
      upper = minimumMaybe leftUpper rightUpper
  in case (lower, upper) of
      (Just low, Just high)
        | low <= high -> Just low
        | otherwise -> Nothing
      (Just low, Nothing) -> Just low
      (Nothing, Just high) -> Just high
      (Nothing, Nothing) -> Just 0

integerIntervalContainedIn :: IntegerInterval -> IntegerInterval -> Bool
integerIntervalContainedIn source target =
  let (sourceLower, sourceUpper) = integerIntervalBounds source
      (targetLower, targetUpper) = integerIntervalBounds target
  in lowerContained sourceLower targetLower
      && upperContained sourceUpper targetUpper

directedIntegerSubintervalFits
  :: IntegerInterval
  -> Integer
  -> IntegerRangeTarget
  -> Bool
directedIntegerSubintervalFits outer start target =
  case (integerIntervalDirection outer, target) of
    (AscendingIntegerRange, FiniteIntegerTarget final) ->
      start <= final
        && integerIntervalContains outer start
        && integerIntervalContains outer final
    (AscendingIntegerRange, UpwardsIntegerTarget) ->
      integerIntervalTarget outer `elem`
        [UpwardsIntegerTarget, AllIntegersTarget]
        && integerIntervalContains outer start
    (DescendingIntegerRange, FiniteIntegerTarget final) ->
      start >= final
        && integerIntervalContains outer start
        && integerIntervalContains outer final
    (DescendingIntegerRange, DownwardsIntegerTarget) ->
      integerIntervalTarget outer `elem`
        [DownwardsIntegerTarget, AllIntegersTarget]
        && integerIntervalContains outer start
    (ProductIntegerRange, FiniteIntegerTarget final) ->
      integerIntervalContains outer start
        && integerIntervalContains outer final
    (ProductIntegerRange, UpwardsIntegerTarget) -> True
    (ProductIntegerRange, DownwardsIntegerTarget) -> True
    (ProductIntegerRange, AllIntegersTarget) -> True
    _ -> False

integerIntervalWidth :: Integer -> Integer -> Natural
integerIntervalWidth start target =
  fromInteger (abs (target - start) + 1)

integerAtOffset :: IntegerRangeDirection -> Integer -> Natural -> Integer
integerAtOffset AscendingIntegerRange start offset =
  start + toInteger offset
integerAtOffset DescendingIntegerRange start offset =
  start - toInteger offset
integerAtOffset ProductIntegerRange _ offset =
  if even offset
    then toInteger (offset `div` 2)
    else negate (toInteger (offset `div` 2)) - 1

integerOffset :: IntegerRangeDirection -> Integer -> Integer -> Natural
integerOffset AscendingIntegerRange start value =
  fromInteger (value - start)
integerOffset DescendingIntegerRange start value =
  fromInteger (start - value)
integerOffset ProductIntegerRange _ value
  | value >= 0 = fromInteger (2 * value)
  | otherwise = fromInteger (2 * (negate value - 1) + 1)

maximumMaybe :: Ord value => Maybe value -> Maybe value -> Maybe value
maximumMaybe Nothing right = right
maximumMaybe left Nothing = left
maximumMaybe (Just left) (Just right) = Just (max left right)

minimumMaybe :: Ord value => Maybe value -> Maybe value -> Maybe value
minimumMaybe Nothing right = right
minimumMaybe left Nothing = left
minimumMaybe (Just left) (Just right) = Just (min left right)

lowerContained :: Maybe Integer -> Maybe Integer -> Bool
lowerContained Nothing Nothing = True
lowerContained Nothing (Just _) = False
lowerContained (Just _) Nothing = True
lowerContained (Just source) (Just target) = target <= source

upperContained :: Maybe Integer -> Maybe Integer -> Bool
upperContained Nothing Nothing = True
upperContained Nothing (Just _) = False
upperContained (Just _) Nothing = True
upperContained (Just source) (Just target) = source <= target
