{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Inclusive natural intervals regarded as federations of individual
-- 'EllipsisNatural' values.
module ValuedNaturalRange
  ( ValuedNaturalRange
  , ValuedNatural
  , valuedNaturalRange
  , valuedNaturalRangeEither
  , valuedNaturalRangeEllipsisRange
  , valuedNaturalRangeFederation
  , valuedNaturalRangeStart
  , valuedNaturalRangeTarget
  , valuedNaturalRangeDirection
  , valuedNaturalRangeValue
  , valuedNaturalValue
  , valuedNaturalRangeContains
  , valuedNaturalRangesOverlapWitness
  , valuedNaturalRangeOverlapNaturalRange
  , valuedNaturalRangeIsSubfederationOf
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
  , AtlasFederationSeparation (SeparatedCorrespondingPageElements)
  , atlasFederation
  )
import DatraOrdinal (finiteOrdinal)
import Dominion (Dominion, dominion)
import EllipsisNatural
  ( EllipsisNatural
  , ellipsisNaturalTotal
  )
import EllipsisRange (EllipsisRange)
import EmptyAtlas (emptyAtlas)
import MapOperators.IndexedAtlasMap (indexedAtlasAtlas)
import MapOperators.OrderedAtlasMap
  ( OrderedAtlasMap (EmptyOrderedAtlasMap, NonEmptyOrderedAtlasMap)
  )
import NaturalRange
  ( NaturalRange
  , NaturalRangeDirection
  , NaturalRangeEndpoint
  , NaturalRangeTarget (..)
  )
import NaturalRange qualified
import Numeric.Natural (Natural)
import SuperEllipsisRange
  ( SuperEllipsisRangeError
  , superEllipsisRangeOrderedMap
  )
import SuperEllipsisValue (superEllipsisValueRange)

-- | One value-member of a 'ValuedNaturalRange'.  The phantom scope prevents
-- an index from one federation from being used with another.
type role ValuedNatural nominal
newtype ValuedNatural scope = ValuedNatural
  { valuedNaturalValue :: Natural
  }
  deriving (Eq, Show)

-- | An inclusive interval whose component Atlases are precisely its
-- singleton 'EllipsisNatural' values.  Unlike 'NaturalRange', this federation
-- has neither an empty member nor members containing multiple values.
data ValuedNaturalRange rangeScope federationScope = ValuedNaturalRange
  { valuedNaturalRangeEllipsisRange :: EllipsisRange rangeScope
  , valuedNaturalRangeFederation
      :: AtlasFederation federationScope (ValuedNatural rangeScope)
  , valuedNaturalRangeStart :: Natural
  , valuedNaturalRangeTarget :: NaturalRangeTarget
  , valuedNaturalRangeDirection :: NaturalRangeDirection
  }

valuedNaturalRange
  :: NaturalRangeEndpoint endpoint
  => EllipsisNatural originScope
  -> endpoint
  -> (forall rangeScope federationScope.
       ValuedNaturalRange rangeScope federationScope
       -> result)
  -> Maybe result
valuedNaturalRange origin endpoint useRange =
  case valuedNaturalRangeEither origin endpoint useRange of
    Left _ -> Nothing
    Right result -> Just result

valuedNaturalRangeEither
  :: NaturalRangeEndpoint endpoint
  => EllipsisNatural originScope
  -> endpoint
  -> (forall rangeScope federationScope.
       ValuedNaturalRange rangeScope federationScope
       -> result)
  -> Either SuperEllipsisRangeError result
valuedNaturalRangeEither origin endpoint useRange =
  NaturalRange.naturalRangeEither origin endpoint $ \outerRange ->
    valuedNaturalRangeFederationFor outerRange $ \federation ->
      useRange
        ValuedNaturalRange
          { valuedNaturalRangeEllipsisRange =
              NaturalRange.naturalRangeEllipsisRange outerRange
          , valuedNaturalRangeFederation = federation
          , valuedNaturalRangeStart = NaturalRange.naturalRangeStart outerRange
          , valuedNaturalRangeTarget =
              NaturalRange.naturalRangeTarget outerRange
          , valuedNaturalRangeDirection =
              NaturalRange.naturalRangeDirection outerRange
          }

valuedNaturalRangeValue
  :: ValuedNaturalRange rangeScope federationScope
  -> Natural
  -> Maybe (ValuedNatural rangeScope)
valuedNaturalRangeValue valueRange value
  | valuedNaturalRangeContains valueRange value =
      Just (ValuedNatural value)
  | otherwise = Nothing

valuedNaturalRangeContains
  :: ValuedNaturalRange rangeScope federationScope
  -> Natural
  -> Bool
valuedNaturalRangeContains valueRange value =
  let (lower, upper) = valuedNaturalRangeBounds valueRange
  in value >= lower && maybe True (value <=) upper

valuedNaturalRangesOverlapWitness
  :: ValuedNaturalRange leftRangeScope leftFederationScope
  -> ValuedNaturalRange rightRangeScope rightFederationScope
  -> Maybe Natural
valuedNaturalRangesOverlapWitness left right =
  overlapWitness
    (valuedNaturalRangeBounds left)
    (valuedNaturalRangeBounds right)

valuedNaturalRangeOverlapNaturalRange
  :: ValuedNaturalRange valuedRangeScope valuedFederationScope
  -> NaturalRange naturalRangeScope naturalFederationScope
  -> Maybe Natural
valuedNaturalRangeOverlapNaturalRange valued natural =
  overlapWitness
    (valuedNaturalRangeBounds valued)
    (naturalRangeBounds natural)

-- | Inclusion is inclusion of value sets.  Traversal direction is irrelevant
-- because each component is an individual natural Atlas.
valuedNaturalRangeIsSubfederationOf
  :: ValuedNaturalRange sourceRangeScope sourceFederationScope
  -> ValuedNaturalRange targetRangeScope targetFederationScope
  -> Bool
valuedNaturalRangeIsSubfederationOf source target =
  let (sourceLower, sourceUpper) = valuedNaturalRangeBounds source
      (targetLower, targetUpper) = valuedNaturalRangeBounds target
  in targetLower <= sourceLower
      && upperBoundContained sourceUpper targetUpper

valuedNaturalRangeFederationFor
  :: NaturalRange rangeScope naturalFederationScope
  -> (forall federationScope.
       AtlasFederation federationScope (ValuedNatural rangeScope)
       -> result)
  -> result
valuedNaturalRangeFederationFor outerRange useFederation =
  withRangeAtlasWitness
    (NaturalRange.naturalRangeEllipsisRange outerRange) $ \rangeWitness ->
      atlasConfederation
        (valuedNaturalDominion
          (NaturalRange.naturalRangeStart outerRange)
          (NaturalRange.naturalRangeTarget outerRange))
        valuedNaturalComponent
        (AtlasMergeAtom rangeWitness) $ \confederation ->
          useFederation
            (atlasFederation confederation valuesSeparated)

valuedNaturalComponent
  :: ValuedNatural scope
  -> AtlasConfederationComponent
valuedNaturalComponent (ValuedNatural value) =
  ellipsisNaturalTotal value $ \natural ->
    withRangeAtlasWitness
      (superEllipsisValueRange natural)
      atlasConfederationComponentWitness

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

valuesSeparated
  :: ValuedNatural scope
  -> ValuedNatural scope
  -> AtlasFederationSeparation
valuesSeparated _ _ =
  SeparatedCorrespondingPageElements 1 (finiteOrdinal 0)

valuedNaturalDominion
  :: Natural
  -> NaturalRangeTarget
  -> Dominion (ValuedNatural scope)
valuedNaturalDominion start target =
  dominion
    (rankValuedNatural start target)
    (unrankValuedNatural start target)
    (const ())

rankValuedNatural
  :: Natural
  -> NaturalRangeTarget
  -> ValuedNatural scope
  -> Natural
rankValuedNatural start UpwardsTarget (ValuedNatural value) = value - start
rankValuedNatural start (FiniteNaturalTarget target) (ValuedNatural value)
  | start <= target = value - start
  | otherwise = start - value

unrankValuedNatural
  :: Natural
  -> NaturalRangeTarget
  -> Natural
  -> Maybe (ValuedNatural scope)
unrankValuedNatural start UpwardsTarget valueRank =
  Just (ValuedNatural (start + valueRank))
unrankValuedNatural start (FiniteNaturalTarget target) valueRank
  | valueRank >= width = Nothing
  | start <= target = Just (ValuedNatural (start + valueRank))
  | otherwise = Just (ValuedNatural (start - valueRank))
  where
    width
      | start <= target = target - start + 1
      | otherwise = start - target + 1

valuedNaturalRangeBounds
  :: ValuedNaturalRange rangeScope federationScope
  -> (Natural, Maybe Natural)
valuedNaturalRangeBounds valueRange =
  bounds
    (valuedNaturalRangeStart valueRange)
    (valuedNaturalRangeTarget valueRange)

naturalRangeBounds
  :: NaturalRange rangeScope federationScope
  -> (Natural, Maybe Natural)
naturalRangeBounds valueRange =
  bounds
    (NaturalRange.naturalRangeStart valueRange)
    (NaturalRange.naturalRangeTarget valueRange)

bounds :: Natural -> NaturalRangeTarget -> (Natural, Maybe Natural)
bounds start UpwardsTarget = (start, Nothing)
bounds start (FiniteNaturalTarget target) =
  (min start target, Just (max start target))

overlapWitness
  :: (Natural, Maybe Natural)
  -> (Natural, Maybe Natural)
  -> Maybe Natural
overlapWitness (leftLower, leftUpper) (rightLower, rightUpper) =
  let lower = max leftLower rightLower
  in if withinUpper lower leftUpper && withinUpper lower rightUpper
      then Just lower
      else Nothing

withinUpper :: Natural -> Maybe Natural -> Bool
withinUpper _ Nothing = True
withinUpper value (Just upper) = value <= upper

upperBoundContained :: Maybe Natural -> Maybe Natural -> Bool
upperBoundContained Nothing Nothing = True
upperBoundContained Nothing (Just _) = False
upperBoundContained (Just _) Nothing = True
upperBoundContained (Just source) (Just target) = source <= target
