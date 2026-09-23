{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Inclusive integer ranges and the federation of their directed subranges.
module IntegerRange
  ( IntegerRange
  , IntegerRangeEndpoint
  , Upwards
  , Downwards
  , upwards
  , downwards
  , IntegerRangeDirection (..)
  , IntegerRangeTarget (..)
  , IntegerSubrange
  , IntegerSubrangeDescription (..)
  , integerRange
  , integerRangeInsertion
  , integerRangeFederation
  , integerRangeStart
  , integerRangeTarget
  , integerRangeDirection
  , integerRangesDisjoint
  , integerRangeOverlapWitness
  , integerRangeIsSubfederationOf
  , integerRangeEmptySubrange
  , integerRangeFullSubrange
  , integerRangeFiniteSubrange
  , integerRangeUpwardsSubrange
  , integerRangeDownwardsSubrange
  , integerSubrangeDescription
  ) where

import AtlasConfederation
  ( AtlasConfederationComponent
  , AtlasMergePresentation (AtlasMergeAtom)
  , atlasConfederation
  , atlasConfederationComponentWitness
  )
import Atlas qualified
import AtlasFederation
  ( AtlasFederation
  , AtlasFederationSeparation
      ( DifferentPageOrderTypes
      , SeparatedCorrespondingPageElements
      )
  , atlasFederation
  )
import DatraOrdinal (finiteOrdinal)
import Dominion (Dominion, dominion)
import Ellipsis (Ellipsis)
import EllipsisInteger (EllipsisInteger, ellipsisIntegerValue)
import EmptyAtlas (emptyAtlas)
import IntegerRange.Encoding
  ( IntegerElement
  , integerSequenceInsertion
  , withIntegerInsertionAtlasWitness
  )
import IntegerRange.Interval
  ( IntegerInterval
  , IntegerRangeDirection (..)
  , IntegerRangeTarget (..)
  , directedIntegerSubintervalFits
  , integerAtOffset
  , integerInterval
  , integerIntervalDirection
  , integerIntervalOverlapWitness
  , integerIntervalStart
  , integerIntervalTarget
  , integerIntervalWidth
  , integerOffset
  )
import Numeric.Natural (Natural)
import SuperEllipsisInsertion (SuperEllipsisInsertion)

data Upwards = Upwards
data Downwards = Downwards

upwards :: Upwards
upwards = Upwards

downwards :: Downwards
downwards = Downwards

class IntegerRangeEndpoint endpoint where
  endpointTarget :: endpoint -> IntegerRangeTarget

instance IntegerRangeEndpoint (EllipsisInteger scope) where
  endpointTarget = FiniteIntegerTarget . ellipsisIntegerValue

instance IntegerRangeEndpoint Upwards where
  endpointTarget _ = UpwardsIntegerTarget

instance IntegerRangeEndpoint Downwards where
  endpointTarget _ = DownwardsIntegerTarget

type role IntegerSubrange nominal
data IntegerSubrange scope
  = EmptySubrange
  | FiniteSubrange Integer Integer
  | UpwardsSubrange Integer
  | DownwardsSubrange Integer
  deriving (Eq, Show)

data IntegerSubrangeDescription
  = EmptyIntegerSubrange
  | FiniteIntegerSubrange Integer Integer
  | UpwardsIntegerSubrange Integer
  | DownwardsIntegerSubrange Integer
  deriving (Eq, Show)

data IntegerRange rangeScope federationScope = IntegerRange
  { integerRangeInsertion
      :: SuperEllipsisInsertion Ellipsis (IntegerElement rangeScope)
  , integerRangeFederation
      :: AtlasFederation federationScope (IntegerSubrange rangeScope)
  , integerRangeInterval :: IntegerInterval
  }

integerRangeStart :: IntegerRange rangeScope federationScope -> Integer
integerRangeStart = integerIntervalStart . integerRangeInterval

integerRangeTarget
  :: IntegerRange rangeScope federationScope
  -> IntegerRangeTarget
integerRangeTarget = integerIntervalTarget . integerRangeInterval

integerRangeDirection
  :: IntegerRange rangeScope federationScope
  -> IntegerRangeDirection
integerRangeDirection = integerIntervalDirection . integerRangeInterval

integerRange
  :: IntegerRangeEndpoint endpoint
  => EllipsisInteger originScope
  -> endpoint
  -> (forall rangeScope federationScope.
       IntegerRange rangeScope federationScope
       -> result)
  -> Maybe result
integerRange origin endpoint useRange =
  Just
    (integerSequenceInsertion start target $ \insertion ->
      integerRangeFederationFor insertion start target $ \federation ->
        useRange
          IntegerRange
            { integerRangeInsertion = insertion
            , integerRangeFederation = federation
            , integerRangeInterval = integerInterval start target
            })
  where
    start = ellipsisIntegerValue origin
    target = endpointTarget endpoint

integerRangeEmptySubrange
  :: IntegerRange rangeScope federationScope
  -> IntegerSubrange rangeScope
integerRangeEmptySubrange _ = EmptySubrange

integerRangeFullSubrange
  :: IntegerRange rangeScope federationScope
  -> IntegerSubrange rangeScope
integerRangeFullSubrange valueRange =
  case integerRangeTarget valueRange of
    FiniteIntegerTarget target ->
      FiniteSubrange (integerRangeStart valueRange) target
    UpwardsIntegerTarget -> UpwardsSubrange (integerRangeStart valueRange)
    DownwardsIntegerTarget -> DownwardsSubrange (integerRangeStart valueRange)
    AllIntegersTarget -> EmptySubrange

integerRangeFiniteSubrange
  :: IntegerRange rangeScope federationScope
  -> Integer
  -> Integer
  -> Maybe (IntegerSubrange rangeScope)
integerRangeFiniteSubrange valueRange start target
  | directedIntegerSubintervalFits
      (integerRangeInterval valueRange)
      start
      (FiniteIntegerTarget target) = Just (FiniteSubrange start target)
  | otherwise = Nothing

integerRangeUpwardsSubrange
  :: IntegerRange rangeScope federationScope
  -> Integer
  -> Maybe (IntegerSubrange rangeScope)
integerRangeUpwardsSubrange valueRange start
  | directedIntegerSubintervalFits
      (integerRangeInterval valueRange) start UpwardsIntegerTarget =
      Just (UpwardsSubrange start)
  | otherwise = Nothing

integerRangeDownwardsSubrange
  :: IntegerRange rangeScope federationScope
  -> Integer
  -> Maybe (IntegerSubrange rangeScope)
integerRangeDownwardsSubrange valueRange start
  | directedIntegerSubintervalFits
      (integerRangeInterval valueRange) start DownwardsIntegerTarget =
      Just (DownwardsSubrange start)
  | otherwise = Nothing

integerRangesDisjoint
  :: IntegerRange leftRangeScope leftFederationScope
  -> IntegerRange rightRangeScope rightFederationScope
  -> Bool
integerRangesDisjoint left right =
  case integerRangeOverlapWitness left right of
    Nothing -> True
    Just _ -> False

integerRangeOverlapWitness
  :: IntegerRange leftRangeScope leftFederationScope
  -> IntegerRange rightRangeScope rightFederationScope
  -> Maybe Integer
integerRangeOverlapWitness left right =
  integerIntervalOverlapWitness
    (integerRangeInterval left)
    (integerRangeInterval right)

integerRangeIsSubfederationOf
  :: IntegerRange sourceRangeScope sourceFederationScope
  -> IntegerRange targetRangeScope targetFederationScope
  -> Bool
integerRangeIsSubfederationOf source target =
  case integerRangeTarget source of
    FiniteIntegerTarget final ->
      case integerRangeFiniteSubrange
          target (integerRangeStart source) final of
        Just _ -> True
        Nothing -> False
    UpwardsIntegerTarget ->
      case integerRangeUpwardsSubrange target (integerRangeStart source) of
        Just _ -> True
        Nothing -> False
    DownwardsIntegerTarget ->
      case integerRangeDownwardsSubrange target (integerRangeStart source) of
        Just _ -> True
        Nothing -> False
    AllIntegersTarget -> False

integerSubrangeDescription
  :: IntegerSubrange scope
  -> IntegerSubrangeDescription
integerSubrangeDescription EmptySubrange = EmptyIntegerSubrange
integerSubrangeDescription (FiniteSubrange start target) =
  FiniteIntegerSubrange start target
integerSubrangeDescription (UpwardsSubrange start) =
  UpwardsIntegerSubrange start
integerSubrangeDescription (DownwardsSubrange start) =
  DownwardsIntegerSubrange start

integerRangeFederationFor
  :: SuperEllipsisInsertion Ellipsis (IntegerElement rangeScope)
  -> Integer
  -> IntegerRangeTarget
  -> (forall federationScope.
       AtlasFederation federationScope (IntegerSubrange rangeScope)
       -> result)
  -> result
integerRangeFederationFor insertion start target useFederation =
  withIntegerInsertionAtlasWitness insertion $ \rangeWitness ->
    atlasConfederation
      (subrangeDominion start target)
      subrangeComponent
      (AtlasMergeAtom rangeWitness) $ \confederation ->
        useFederation
          (atlasFederation confederation subrangesSeparated)

subrangeComponent :: IntegerSubrange scope -> AtlasConfederationComponent
subrangeComponent EmptySubrange =
  emptyAtlas (atlasConfederationComponentWitness . Atlas.atlasWitness)
subrangeComponent subrange =
  let (start, target) =
        case subrange of
          FiniteSubrange origin final ->
            (origin, FiniteIntegerTarget final)
          UpwardsSubrange origin -> (origin, UpwardsIntegerTarget)
          DownwardsSubrange origin -> (origin, DownwardsIntegerTarget)
  in integerSequenceInsertion start target $ \insertion ->
      withIntegerInsertionAtlasWitness
        insertion atlasConfederationComponentWitness

subrangesSeparated
  :: IntegerSubrange scope
  -> IntegerSubrange scope
  -> AtlasFederationSeparation
subrangesSeparated left right
  | subrangeSize left /= subrangeSize right = DifferentPageOrderTypes 1
  | otherwise = SeparatedCorrespondingPageElements 1 (finiteOrdinal 0)

subrangeSize :: IntegerSubrange scope -> Maybe Natural
subrangeSize EmptySubrange = Just 0
subrangeSize (FiniteSubrange start target) =
  Just (integerIntervalWidth start target)
subrangeSize (UpwardsSubrange _) = Nothing
subrangeSize (DownwardsSubrange _) = Nothing

subrangeDominion
  :: Integer
  -> IntegerRangeTarget
  -> Dominion (IntegerSubrange scope)
subrangeDominion start (FiniteIntegerTarget target) =
  dominion
    (rankFiniteSubrange start target)
    (unrankFiniteSubrange start target)
    (const ())
subrangeDominion start target =
  dominion
    (rankOpenSubrange start target)
    (unrankOpenSubrange start target)
    (const ())

rankFiniteSubrange
  :: Integer -> Integer -> IntegerSubrange scope -> Natural
rankFiniteSubrange _ _ EmptySubrange = 0
rankFiniteSubrange outerStart outerTarget (FiniteSubrange start target) =
  1 + triangularPrefix width startOffset + (targetOffset - startOffset)
  where
    direction = integerIntervalDirection
      (integerInterval outerStart (FiniteIntegerTarget outerTarget))
    width = integerIntervalWidth outerStart outerTarget
    startOffset = integerOffset direction outerStart start
    targetOffset = integerOffset direction outerStart target
rankFiniteSubrange _ _ _ = 0

unrankFiniteSubrange
  :: Integer -> Integer -> Natural -> Maybe (IntegerSubrange scope)
unrankFiniteSubrange _ _ 0 = Just EmptySubrange
unrankFiniteSubrange outerStart outerTarget valueRank = do
  (startOffset, targetOffset) <-
    unrankFinitePair width (valueRank - 1)
  pure
    (FiniteSubrange
      (integerAtOffset direction outerStart startOffset)
      (integerAtOffset direction outerStart targetOffset))
  where
    direction = integerIntervalDirection
      (integerInterval outerStart (FiniteIntegerTarget outerTarget))
    width = integerIntervalWidth outerStart outerTarget

rankOpenSubrange
  :: Integer
  -> IntegerRangeTarget
  -> IntegerSubrange scope
  -> Natural
rankOpenSubrange _ _ EmptySubrange = 0
rankOpenSubrange outerStart target (FiniteSubrange start final) =
  1 + 2 * pairNaturals
    (integerOffset direction outerStart start)
    (integerOffset direction start final)
  where
    direction = integerIntervalDirection (integerInterval outerStart target)
rankOpenSubrange outerStart UpwardsIntegerTarget (UpwardsSubrange start) =
  2 + 2 * integerOffset AscendingIntegerRange outerStart start
rankOpenSubrange outerStart DownwardsIntegerTarget (DownwardsSubrange start) =
  2 + 2 * integerOffset DescendingIntegerRange outerStart start
rankOpenSubrange _ _ _ = 0

unrankOpenSubrange
  :: Integer
  -> IntegerRangeTarget
  -> Natural
  -> Maybe (IntegerSubrange scope)
unrankOpenSubrange _ _ 0 = Just EmptySubrange
unrankOpenSubrange outerStart target valueRank
  | odd valueRank = do
      (startOffset, lengthOffset) <-
        unpairNaturals ((valueRank - 1) `div` 2)
      let start = integerAtOffset direction outerStart startOffset
      pure
        (FiniteSubrange
          start (integerAtOffset direction start lengthOffset))
  | otherwise =
      let start = integerAtOffset direction outerStart ((valueRank - 2) `div` 2)
      in case target of
          UpwardsIntegerTarget -> Just (UpwardsSubrange start)
          DownwardsIntegerTarget -> Just (DownwardsSubrange start)
          _ -> Nothing
  where
    direction = integerIntervalDirection (integerInterval outerStart target)

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

pairNaturals :: Natural -> Natural -> Natural
pairNaturals left right = triangular (left + right) + right

unpairNaturals :: Natural -> Maybe (Natural, Natural)
unpairNaturals = go 0
  where
    go diagonal remainder
      | remainder < diagonal + 1 =
          Just (diagonal - remainder, remainder)
      | otherwise = go (diagonal + 1) (remainder - diagonal - 1)

triangular :: Natural -> Natural
triangular value = value * (value + 1) `div` 2
