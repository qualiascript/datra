{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Inclusive integer intervals regarded as federations of individual
-- integer values.
module ValuedIntegerRange
  ( ValuedIntegerRange
  , ValuedInteger
  , valuedIntegerRange
  , valuedAllIntegers
  , valuedIntegerRangeInsertion
  , valuedIntegerRangeFederation
  , valuedIntegerRangeStart
  , valuedIntegerRangeTarget
  , valuedIntegerRangeDirection
  , valuedIntegerRangeValue
  , valuedIntegerValue
  , valuedIntegerRangeContains
  , valuedIntegerRangesOverlapWitness
  , valuedIntegerRangeOverlapIntegerRange
  , valuedIntegerRangeIsSubfederationOf
  ) where

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
import Ellipsis (Ellipsis)
import EllipsisInteger (EllipsisInteger)
import IntegerRange
  ( IntegerRange
  , IntegerRangeDirection
  , IntegerRangeEndpoint
  , IntegerRangeTarget (..)
  )
import IntegerRange qualified
import IntegerRange.Encoding
  ( IntegerElement
  , integerSequenceInsertion
  , integerSingletonInsertion
  , withIntegerInsertionAtlasWitness
  )
import IntegerRange.Interval
  ( IntegerInterval
  , integerAtOffset
  , integerInterval
  , integerIntervalContainedIn
  , integerIntervalContains
  , integerIntervalDirection
  , integerIntervalOverlapWitness
  , integerIntervalStart
  , integerIntervalTarget
  , integerIntervalWidth
  , integerOffset
  )
import Numeric.Natural (Natural)
import SuperEllipsisInsertion (SuperEllipsisInsertion)

type role ValuedInteger nominal
newtype ValuedInteger scope = ValuedInteger
  { valuedIntegerValue :: Integer
  }
  deriving (Eq, Show)

data ValuedIntegerRange rangeScope federationScope = ValuedIntegerRange
  { valuedIntegerRangeInsertion
      :: SuperEllipsisInsertion Ellipsis (IntegerElement rangeScope)
  , valuedIntegerRangeFederation
      :: AtlasFederation federationScope (ValuedInteger rangeScope)
  , valuedIntegerRangeInterval :: IntegerInterval
  }

valuedIntegerRangeStart
  :: ValuedIntegerRange rangeScope federationScope -> Integer
valuedIntegerRangeStart =
  integerIntervalStart . valuedIntegerRangeInterval

valuedIntegerRangeTarget
  :: ValuedIntegerRange rangeScope federationScope -> IntegerRangeTarget
valuedIntegerRangeTarget =
  integerIntervalTarget . valuedIntegerRangeInterval

valuedIntegerRangeDirection
  :: ValuedIntegerRange rangeScope federationScope -> IntegerRangeDirection
valuedIntegerRangeDirection =
  integerIntervalDirection . valuedIntegerRangeInterval

valuedIntegerRange
  :: IntegerRangeEndpoint endpoint
  => EllipsisInteger originScope
  -> endpoint
  -> (forall rangeScope federationScope.
       ValuedIntegerRange rangeScope federationScope
       -> result)
  -> Maybe result
valuedIntegerRange origin endpoint useRange =
  IntegerRange.integerRange origin endpoint $ \outerRange ->
    valuedIntegerRangeFor
      (IntegerRange.integerRangeStart outerRange)
      (IntegerRange.integerRangeTarget outerRange)
      useRange

-- | The complete @Int@ value family, ordered by its @Nat x 2@ encoding.
valuedAllIntegers
  :: (forall rangeScope federationScope.
       ValuedIntegerRange rangeScope federationScope
       -> result)
  -> result
valuedAllIntegers = valuedIntegerRangeFor 0 AllIntegersTarget

valuedIntegerRangeValue
  :: ValuedIntegerRange rangeScope federationScope
  -> Integer
  -> Maybe (ValuedInteger rangeScope)
valuedIntegerRangeValue valueRange value
  | valuedIntegerRangeContains valueRange value = Just (ValuedInteger value)
  | otherwise = Nothing

valuedIntegerRangeContains
  :: ValuedIntegerRange rangeScope federationScope
  -> Integer
  -> Bool
valuedIntegerRangeContains valueRange =
  integerIntervalContains (valuedIntegerRangeInterval valueRange)

valuedIntegerRangesOverlapWitness
  :: ValuedIntegerRange leftRangeScope leftFederationScope
  -> ValuedIntegerRange rightRangeScope rightFederationScope
  -> Maybe Integer
valuedIntegerRangesOverlapWitness left right =
  integerIntervalOverlapWitness
    (valuedIntegerRangeInterval left)
    (valuedIntegerRangeInterval right)

valuedIntegerRangeOverlapIntegerRange
  :: ValuedIntegerRange valuedRangeScope valuedFederationScope
  -> IntegerRange integerRangeScope integerFederationScope
  -> Maybe Integer
valuedIntegerRangeOverlapIntegerRange valued ordinary =
  integerIntervalOverlapWitness
    (valuedIntegerRangeInterval valued)
    (integerInterval
      (IntegerRange.integerRangeStart ordinary)
      (IntegerRange.integerRangeTarget ordinary))

valuedIntegerRangeIsSubfederationOf
  :: ValuedIntegerRange sourceRangeScope sourceFederationScope
  -> ValuedIntegerRange targetRangeScope targetFederationScope
  -> Bool
valuedIntegerRangeIsSubfederationOf source target =
  integerIntervalContainedIn
    (valuedIntegerRangeInterval source)
    (valuedIntegerRangeInterval target)

valuedIntegerRangeFor
  :: Integer
  -> IntegerRangeTarget
  -> (forall rangeScope federationScope.
       ValuedIntegerRange rangeScope federationScope
       -> result)
  -> result
valuedIntegerRangeFor start target useRange =
  integerSequenceInsertion start target $ \insertion ->
    valuedIntegerRangeFederationFor insertion start target $ \federation ->
      useRange
        ValuedIntegerRange
          { valuedIntegerRangeInsertion = insertion
          , valuedIntegerRangeFederation = federation
          , valuedIntegerRangeInterval = integerInterval start target
          }

valuedIntegerRangeFederationFor
  :: SuperEllipsisInsertion Ellipsis (IntegerElement rangeScope)
  -> Integer
  -> IntegerRangeTarget
  -> (forall federationScope.
       AtlasFederation federationScope (ValuedInteger rangeScope)
       -> result)
  -> result
valuedIntegerRangeFederationFor insertion start target useFederation =
  withIntegerInsertionAtlasWitness insertion $ \rangeWitness ->
    atlasConfederation
      (valuedIntegerDominion start target)
      valuedIntegerComponent
      (AtlasMergeAtom rangeWitness) $ \confederation ->
        useFederation
          (atlasFederation confederation valuesSeparated)

valuedIntegerComponent
  :: ValuedInteger scope -> AtlasConfederationComponent
valuedIntegerComponent (ValuedInteger value) =
  integerSingletonInsertion value $ \insertion ->
    withIntegerInsertionAtlasWitness
      insertion atlasConfederationComponentWitness

valuesSeparated
  :: ValuedInteger scope
  -> ValuedInteger scope
  -> AtlasFederationSeparation
valuesSeparated _ _ =
  SeparatedCorrespondingPageElements 1 (finiteOrdinal 0)

valuedIntegerDominion
  :: Integer
  -> IntegerRangeTarget
  -> Dominion (ValuedInteger scope)
valuedIntegerDominion start target =
  dominion
    (rankValuedInteger start target)
    (unrankValuedInteger start target)
    (const ())

rankValuedInteger
  :: Integer
  -> IntegerRangeTarget
  -> ValuedInteger scope
  -> Natural
rankValuedInteger start target (ValuedInteger value) =
  integerOffset
    (integerIntervalDirection (integerInterval start target))
    start
    value

unrankValuedInteger
  :: Integer
  -> IntegerRangeTarget
  -> Natural
  -> Maybe (ValuedInteger scope)
unrankValuedInteger start target valueRank =
  case target of
    FiniteIntegerTarget final
      | valueRank >= integerIntervalWidth start final -> Nothing
    _ -> pure ()
  >> pure
      (ValuedInteger
        (integerAtOffset
          (integerIntervalDirection (integerInterval start target))
          start
          valueRank))
