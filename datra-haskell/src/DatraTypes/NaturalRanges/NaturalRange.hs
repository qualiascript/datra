{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Inclusive natural ranges and the federation of their directed subranges.
module NaturalRange
  ( NaturalRange
  , NaturalRangeEndpoint
  , Upwards
  , upwards
  , NaturalRangeDirection (..)
  , NaturalRangeTarget (..)
  , NaturalSubrange
  , NaturalSubrangeDescription (..)
  , naturalRange
  , naturalRangeEllipsisRange
  , naturalRangeFederation
  , naturalRangeStart
  , naturalRangeTarget
  , naturalRangeDirection
  , naturalRangesDisjoint
  , naturalRangeOverlapWitness
  , naturalRangeIsSubfederationOf
  , naturalRangeEmptySubrange
  , naturalRangeFullSubrange
  , naturalRangeLargestSubrangeBelow
  , naturalRangeFiniteSubrange
  , naturalRangeUpwardsSubrange
  , naturalSubrangeDescription
  , naturalSubrangeEllipsisRange
  ) where

import Atlas (AtlasWitness, atlasWitness)
import AtlasConfederation
  ( AtlasConfederationComponent
  , AtlasMergePresentation (AtlasMergeAtom)
  , atlasConfederation
  , atlasConfederationComponentWitness
  )
import AtlasFederation
  ( AtlasFederation
  , AtlasFederationSeparation
      ( DifferentPageOrderTypes
      , SeparatedCorrespondingPageElements
      )
  , atlasFederation
  )
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import Dominion (Dominion, dominion)
import EllipsisNatural (EllipsisNatural)
import EllipsisRange (EllipsisRange)
import EmptyAtlas (emptyAtlas)
import MapOperators.IndexedAtlasMap (indexedAtlasAtlas)
import MapOperators.OrderedAtlasMap
  ( OrderedAtlasMap (EmptyOrderedAtlasMap, NonEmptyOrderedAtlasMap)
  )
import Numeric.Natural (Natural)
import SuperEllipsis
  ( dotSuperEllipsisRank
  , nextSuperEllipsisRank
  )
import SuperEllipsisRange
  ( SuperEllipsisRangeTarget (GivenTarget, MinusSign, PlusSign)
  , superEllipsisRange
  , superEllipsisRangeOrderedMap
  )
import SuperEllipsisValue (superEllipsisValueOrdinal)

-- | The literal accepted as the open upper endpoint of a 'NaturalRange'.
data Upwards = Upwards

-- | The Datra literal @upwards@.
upwards :: Upwards
upwards = Upwards

-- | Values accepted in the target position of 'naturalRange'.
--
-- An ordinary target is an 'EllipsisNatural'; 'upwards' selects the open
-- ascending range instead.
class NaturalRangeEndpoint endpoint where
  endpointTarget :: endpoint -> NaturalRangeTarget

instance NaturalRangeEndpoint (EllipsisNatural scope) where
  endpointTarget =
    FiniteNaturalTarget . ellipsisNaturalValue

instance NaturalRangeEndpoint Upwards where
  endpointTarget _ = UpwardsTarget

data NaturalRangeTarget
  = FiniteNaturalTarget Natural
  | UpwardsTarget
  deriving (Eq, Show)

data NaturalRangeDirection
  = AscendingNaturalRange
  | DescendingNaturalRange
  deriving (Eq, Show)

-- | One range contained in a 'NaturalRange'.  The phantom scope prevents an
-- index obtained from one federation from being used with another.
type role NaturalSubrange nominal
data NaturalSubrange scope
  = EmptySubrange
  | FiniteSubrange Natural Natural
  | UpwardsSubrange Natural
  deriving (Eq, Show)

data NaturalSubrangeDescription
  = EmptyNaturalSubrange
  | FiniteNaturalSubrange Natural Natural
  | UpwardsNaturalSubrange Natural
  deriving (Eq, Show)

-- | An inclusive range together with the federation of every contained range
-- having the same direction.  A finite range always includes the empty range
-- and all of its directed, contiguous, nonempty subranges.  An open range also
-- includes every finite ascending subrange and every contained @upwards@
-- subrange.
data NaturalRange rangeScope federationScope = NaturalRange
  { naturalRangeEllipsisRange :: EllipsisRange rangeScope
  , naturalRangeFederation
      :: AtlasFederation federationScope (NaturalSubrange rangeScope)
  , naturalRangeStart :: Natural
  , naturalRangeTarget :: NaturalRangeTarget
  , naturalRangeDirection :: NaturalRangeDirection
  }

-- | Construct an inclusive natural range.  Finite targets are translated to
-- the half-open 'EllipsisRange' boundary expected by the core range type:
-- ascending @a..b@ becomes @a..(b+1)@, descending @a..b@ becomes
-- @a..(b-1)@, and a zero target uses @..-@.  @upwards@ becomes @a..@.
naturalRange
  :: NaturalRangeEndpoint endpoint
  => EllipsisNatural originScope
  -> endpoint
  -> (forall rangeScope federationScope.
       NaturalRange rangeScope federationScope
       -> result)
  -> Maybe result
naturalRange origin endpoint useRange =
  inclusiveEllipsisRange start target $ \valueRange ->
    naturalRangeFederationFor valueRange start target $ \federation ->
      useRange
        NaturalRange
          { naturalRangeEllipsisRange = valueRange
          , naturalRangeFederation = federation
          , naturalRangeStart = start
          , naturalRangeTarget = target
          , naturalRangeDirection = directionOf start target
          }
  where
    start = ellipsisNaturalValue origin
    target = endpointTarget endpoint

naturalRangeEmptySubrange
  :: NaturalRange rangeScope federationScope
  -> NaturalSubrange rangeScope
naturalRangeEmptySubrange _ = EmptySubrange

-- | The federation index corresponding to the entire outer range.
naturalRangeFullSubrange
  :: NaturalRange rangeScope federationScope
  -> NaturalSubrange rangeScope
naturalRangeFullSubrange valueRange =
  case naturalRangeTarget valueRange of
    FiniteNaturalTarget target ->
      FiniteSubrange (naturalRangeStart valueRange) target
    UpwardsTarget -> UpwardsSubrange (naturalRangeStart valueRange)

-- | Select the largest member whose natural positions are all strictly below
-- the supplied finite limit.  The empty member makes this operation total.
naturalRangeLargestSubrangeBelow
  :: NaturalRange rangeScope federationScope
  -> Natural
  -> NaturalSubrange rangeScope
naturalRangeLargestSubrangeBelow valueRange limit
  | limit == 0 = EmptySubrange
  | otherwise =
      case naturalRangeTarget valueRange of
        UpwardsTarget
          | start < limit -> FiniteSubrange start (limit - 1)
          | otherwise -> EmptySubrange
        FiniteNaturalTarget target
          | start <= target && start < limit ->
              FiniteSubrange start (min target (limit - 1))
          | start > target && target < limit ->
              FiniteSubrange (min start (limit - 1)) target
          | otherwise -> EmptySubrange
  where
    start = naturalRangeStart valueRange

-- | Refine finite inclusive endpoints to membership in this federation.
-- Endpoints must lie within the outer range and follow its direction.
naturalRangeFiniteSubrange
  :: NaturalRange rangeScope federationScope
  -> Natural
  -> Natural
  -> Maybe (NaturalSubrange rangeScope)
naturalRangeFiniteSubrange valueRange start target
  | finiteSubrangeFits
      (naturalRangeStart valueRange)
      (naturalRangeTarget valueRange)
      start
      target = Just (FiniteSubrange start target)
  | otherwise = Nothing

-- | Refine an open ascending subrange to membership in this federation.
-- Such a subrange exists only inside an outer @upwards@ range.
naturalRangeUpwardsSubrange
  :: NaturalRange rangeScope federationScope
  -> Natural
  -> Maybe (NaturalSubrange rangeScope)
naturalRangeUpwardsSubrange valueRange start =
  case naturalRangeTarget valueRange of
    UpwardsTarget
      | naturalRangeStart valueRange <= start ->
          Just (UpwardsSubrange start)
    _ -> Nothing

-- | Decide whether the value domains of two natural ranges are disjoint.
-- Traversal direction is irrelevant: concatenation ambiguity depends on
-- values which may occur on both sides, not on the order in which they occur.
naturalRangesDisjoint
  :: NaturalRange leftRangeScope leftFederationScope
  -> NaturalRange rightRangeScope rightFederationScope
  -> Bool
naturalRangesDisjoint left right =
  case naturalRangeOverlapWitness left right of
    Nothing -> True
    Just _ -> False

-- | Produce a shared value when two natural ranges overlap.  Because every
-- NaturalRange federation contains both its empty range and every singleton,
-- this value is also a concrete witness that concatenation is non-injective:
-- @[x] ++ [] == [] ++ [x]@.
naturalRangeOverlapWitness
  :: NaturalRange leftRangeScope leftFederationScope
  -> NaturalRange rightRangeScope rightFederationScope
  -> Maybe Natural
naturalRangeOverlapWitness left right =
  let (leftLower, leftUpper) = naturalRangeBounds left
      (rightLower, rightUpper) = naturalRangeBounds right
      lower = max leftLower rightLower
  in if withinUpper lower leftUpper && withinUpper lower rightUpper
      then Just lower
      else Nothing

-- | Decide inclusion between the federations generated by two natural
-- ranges.  It is enough to check the source's largest member: containment of
-- that directed interval implies containment of every one of its directed
-- subintervals (and both federations always contain the empty member).
--
-- This also handles the direction-degenerate singleton case correctly: a
-- singleton-generated federation is included in either directional family
-- when its sole value lies inside the target.
naturalRangeIsSubfederationOf
  :: NaturalRange sourceRangeScope sourceFederationScope
  -> NaturalRange targetRangeScope targetFederationScope
  -> Bool
naturalRangeIsSubfederationOf source target =
  case naturalRangeTarget source of
    FiniteNaturalTarget final ->
      case naturalRangeFiniteSubrange
        target (naturalRangeStart source) final of
          Just _ -> True
          Nothing -> False
    UpwardsTarget ->
      case naturalRangeUpwardsSubrange
        target (naturalRangeStart source) of
          Just _ -> True
          Nothing -> False

naturalRangeBounds
  :: NaturalRange rangeScope federationScope
  -> (Natural, Maybe Natural)
naturalRangeBounds valueRange =
  case naturalRangeTarget valueRange of
    UpwardsTarget -> (naturalRangeStart valueRange, Nothing)
    FiniteNaturalTarget target ->
      (min (naturalRangeStart valueRange) target,
       Just (max (naturalRangeStart valueRange) target))

withinUpper :: Natural -> Maybe Natural -> Bool
withinUpper _ Nothing = True
withinUpper value (Just upper) = value <= upper

naturalSubrangeDescription
  :: NaturalSubrange scope
  -> NaturalSubrangeDescription
naturalSubrangeDescription EmptySubrange = EmptyNaturalSubrange
naturalSubrangeDescription (FiniteSubrange start target) =
  FiniteNaturalSubrange start target
naturalSubrangeDescription (UpwardsSubrange start) =
  UpwardsNaturalSubrange start

-- | Materialize a federation member as the core range used by access and
-- other range operations.
naturalSubrangeEllipsisRange
  :: NaturalSubrange scope
  -> (forall rangeScope. EllipsisRange rangeScope -> result)
  -> Maybe result
naturalSubrangeEllipsisRange EmptySubrange =
  superEllipsisRange
    (nextSuperEllipsisRank dotSuperEllipsisRank)
    (finiteOrdinal 0)
    (GivenTarget (finiteOrdinal 0))
naturalSubrangeEllipsisRange (FiniteSubrange start target) =
  inclusiveEllipsisRange start (FiniteNaturalTarget target)
naturalSubrangeEllipsisRange (UpwardsSubrange start) =
  inclusiveEllipsisRange start UpwardsTarget

inclusiveEllipsisRange
  :: Natural
  -> NaturalRangeTarget
  -> (forall scope. EllipsisRange scope -> result)
  -> Maybe result
inclusiveEllipsisRange start target =
  superEllipsisRange
    ellipsisRank
    (finiteOrdinal start)
    (ellipsisTarget start target)
  where
    ellipsisRank = nextSuperEllipsisRank dotSuperEllipsisRank

ellipsisTarget :: Natural -> NaturalRangeTarget -> SuperEllipsisRangeTarget
ellipsisTarget _ UpwardsTarget = PlusSign
ellipsisTarget start (FiniteNaturalTarget target)
  | start <= target = GivenTarget (finiteOrdinal (target + 1))
  | target == 0 = MinusSign
  | otherwise = GivenTarget (finiteOrdinal (target - 1))

ellipsisNaturalValue :: EllipsisNatural scope -> Natural
ellipsisNaturalValue value =
  case naturalAtOrdinal (superEllipsisValueOrdinal value) of
    Just natural -> natural
    Nothing -> 0

directionOf :: Natural -> NaturalRangeTarget -> NaturalRangeDirection
directionOf _ UpwardsTarget = AscendingNaturalRange
directionOf start (FiniteNaturalTarget target)
  | start <= target = AscendingNaturalRange
  | otherwise = DescendingNaturalRange

finiteSubrangeFits
  :: Natural
  -> NaturalRangeTarget
  -> Natural
  -> Natural
  -> Bool
finiteSubrangeFits lower UpwardsTarget start target =
  lower <= start && start <= target
finiteSubrangeFits outerStart (FiniteNaturalTarget outerTarget) start target
  | outerStart <= outerTarget =
      outerStart <= start && start <= target && target <= outerTarget
  | otherwise =
      outerTarget <= target && target <= start && start <= outerStart

naturalRangeFederationFor
  :: EllipsisRange rangeScope
  -> Natural
  -> NaturalRangeTarget
  -> (forall federationScope.
       AtlasFederation federationScope (NaturalSubrange rangeScope)
       -> result)
  -> result
naturalRangeFederationFor valueRange start target useFederation =
  withRangeAtlasWitness valueRange $ \rangeWitness ->
    atlasConfederation
      (subrangeDominion start target)
      subrangeComponent
      (AtlasMergeAtom rangeWitness) $ \confederation ->
        useFederation
          (atlasFederation confederation subrangesSeparated)

subrangeComponent :: NaturalSubrange scope -> AtlasConfederationComponent
subrangeComponent EmptySubrange = emptyRangeComponent
subrangeComponent (FiniteSubrange start target) =
  case inclusiveEllipsisRange
    start (FiniteNaturalTarget target) rangeComponent of
      Just component -> component
      Nothing -> emptyRangeComponent
subrangeComponent (UpwardsSubrange start) =
  case inclusiveEllipsisRange start UpwardsTarget rangeComponent of
    Just component -> component
    Nothing -> emptyRangeComponent

rangeComponent :: EllipsisRange scope -> AtlasConfederationComponent
rangeComponent valueRange =
  withRangeAtlasWitness valueRange atlasConfederationComponentWitness

emptyRangeComponent :: AtlasConfederationComponent
emptyRangeComponent =
  emptyAtlas (atlasConfederationComponentWitness . atlasWitness)

withRangeAtlasWitness
  :: EllipsisRange scope
  -> (forall atlasObject. AtlasWitness atlasObject -> result)
  -> result
withRangeAtlasWitness valueRange useWitness =
  case superEllipsisRangeOrderedMap valueRange of
    EmptyOrderedAtlasMap ->
      emptyAtlas (useWitness . atlasWitness)
    NonEmptyOrderedAtlasMap valueMap ->
      useWitness (atlasWitness (indexedAtlasAtlas valueMap))

subrangesSeparated
  :: NaturalSubrange scope
  -> NaturalSubrange scope
  -> AtlasFederationSeparation
subrangesSeparated left right
  | subrangeSize left /= subrangeSize right =
      DifferentPageOrderTypes 1
  | otherwise =
      SeparatedCorrespondingPageElements 1 (finiteOrdinal 0)

subrangeSize :: NaturalSubrange scope -> Maybe Natural
subrangeSize EmptySubrange = Just 0
subrangeSize (FiniteSubrange start target)
  | start <= target = Just (target - start + 1)
  | otherwise = Just (start - target + 1)
subrangeSize (UpwardsSubrange _) = Nothing

subrangeDominion
  :: Natural
  -> NaturalRangeTarget
  -> Dominion (NaturalSubrange scope)
subrangeDominion start UpwardsTarget =
  dominion
    (rankUpwardsSubrange start)
    (unrankUpwardsSubrange start)
    (const ())
subrangeDominion start (FiniteNaturalTarget target) =
  dominion
    (rankFiniteSubrange start target)
    (unrankFiniteSubrange start target)
    (const ())

rankFiniteSubrange
  :: Natural
  -> Natural
  -> NaturalSubrange scope
  -> Natural
rankFiniteSubrange _ _ EmptySubrange = 0
rankFiniteSubrange outerStart outerTarget (FiniteSubrange start target) =
  1 + triangularPrefix width startOffset + (targetOffset - startOffset)
  where
    width = distance outerStart outerTarget + 1
    (startOffset, targetOffset)
      | outerStart <= outerTarget =
          (start - outerStart, target - outerStart)
      | otherwise =
          (outerStart - start, outerStart - target)
rankFiniteSubrange _ _ (UpwardsSubrange _) = 0

unrankFiniteSubrange
  :: Natural
  -> Natural
  -> Natural
  -> Maybe (NaturalSubrange scope)
unrankFiniteSubrange _ _ 0 = Just EmptySubrange
unrankFiniteSubrange outerStart outerTarget valueRank = do
  (startOffset, targetOffset) <-
    unrankFinitePair width (valueRank - 1)
  pure
    (if outerStart <= outerTarget
      then FiniteSubrange
        (outerStart + startOffset)
        (outerStart + targetOffset)
      else FiniteSubrange
        (outerStart - startOffset)
        (outerStart - targetOffset))
  where
    width = distance outerStart outerTarget + 1

triangularPrefix :: Natural -> Natural -> Natural
triangularPrefix width offset =
  offset * (2 * width - offset + 1) `div` 2

unrankFinitePair :: Natural -> Natural -> Maybe (Natural, Natural)
unrankFinitePair width = go 0
  where
    go offset remainder
      | offset >= width = Nothing
      | remainder < rowSize = Just (offset, offset + remainder)
      | otherwise = go (offset + 1) (remainder - rowSize)
      where
        rowSize = width - offset

rankUpwardsSubrange :: Natural -> NaturalSubrange scope -> Natural
rankUpwardsSubrange _ EmptySubrange = 0
rankUpwardsSubrange outerStart (FiniteSubrange start target) =
  1 + 2 * pairNaturals (start - outerStart) (target - start)
rankUpwardsSubrange outerStart (UpwardsSubrange start) =
  2 + 2 * (start - outerStart)

unrankUpwardsSubrange
  :: Natural
  -> Natural
  -> Maybe (NaturalSubrange scope)
unrankUpwardsSubrange _ 0 = Just EmptySubrange
unrankUpwardsSubrange outerStart valueRank
  | odd valueRank = do
      (startOffset, lengthOffset) <-
        unpairNaturals ((valueRank - 1) `div` 2)
      let start = outerStart + startOffset
      pure (FiniteSubrange start (start + lengthOffset))
  | otherwise =
      Just (UpwardsSubrange (outerStart + (valueRank - 2) `div` 2))

pairNaturals :: Natural -> Natural -> Natural
pairNaturals left right =
  triangular (left + right) + right

unpairNaturals :: Natural -> Maybe (Natural, Natural)
unpairNaturals = go 0
  where
    go diagonal remainder
      | remainder < diagonal + 1 =
          Just (diagonal - remainder, remainder)
      | otherwise = go (diagonal + 1) (remainder - diagonal - 1)

triangular :: Natural -> Natural
triangular value = value * (value + 1) `div` 2

distance :: Natural -> Natural -> Natural
distance left right
  | left <= right = right - left
  | otherwise = left - right
