-- | Fair natural traversals of arbitrary Datra ordinal maps.
--
-- Cantor normal form decomposes an ordinal into finitely many @omega^n@
-- lanes. Each lane has its ordinary Cantor diagonal traversal; 'FoliageMap'
-- interleaves those lanes without changing the ordinal's own access order.
module FoliageMap
  ( FoliageMap
  , foliageMap
  , foliageMapOrderType
  , foliageMapPositionAt
  , foliageMapRankOf
  ) where

import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  , naturalRankOfOrdinal
  , ordinal
  , ordinalAtNaturalRank
  , ordinalCoefficients
  , ordinalLT
  )
import Numeric.Natural (Natural)

newtype FoliageMap = FoliageMap
  { foliageMapOrderType :: Ordinal
  }

foliageMap :: Ordinal -> FoliageMap
foliageMap = FoliageMap

-- | Select the ordinal position at a fair natural traversal rank.
foliageMapPositionAt :: FoliageMap -> Natural -> Maybe Ordinal
foliageMapPositionAt (FoliageMap orderType) rankCode = do
  let coefficients = ordinalCoefficients orderType
      laneCount = sum coefficients
      infiniteLaneCount = sum (dropFiniteCoefficient coefficients)
  if rankCode < laneCount
    then do
      lane <- laneAt coefficients True rankCode
      valueInLane lane 0
    else if infiniteLaneCount == 0
      then Nothing
      else do
        let shifted = rankCode - laneCount
            (laterRound, infiniteLane) =
              shifted `divMod` infiniteLaneCount
        lane <- laneAt coefficients False infiniteLane
        valueInLane lane (laterRound + 1)

-- | Invert 'foliageMapPositionAt' for positions below this map's order type.
foliageMapRankOf :: FoliageMap -> Ordinal -> Maybe Natural
foliageMapRankOf (FoliageMap orderType) position
  | not (ordinalLT position orderType) = Nothing
  | otherwise = do
      lane <- laneContaining
        (ordinalCoefficients orderType)
        (ordinalCoefficients position)
      localRank <- case laneExponent lane of
        0 -> Just 0
        degree -> naturalRankOfOrdinal degree (laneRemainder lane)
      let coefficients = ordinalCoefficients orderType
          laneCount = sum coefficients
          infiniteLaneCount = sum (dropFiniteCoefficient coefficients)
      if localRank == 0
        then Just (laneOverallIndex lane)
        else Just
          ( laneCount
              + (localRank - 1) * infiniteLaneCount
              + laneInfiniteIndex lane
          )

data TraversalLane = TraversalLane
  { lanePrefix :: Ordinal
  , laneExponent :: Natural
  , laneOverallIndex :: Natural
  , laneInfiniteIndex :: Natural
  , laneRemainder :: Ordinal
  }

valueInLane :: TraversalLane -> Natural -> Maybe Ordinal
valueInLane lane localRank = do
  local <- case laneExponent lane of
    0 -> if localRank == 0 then Just (finiteOrdinal 0) else Nothing
    degree -> ordinalAtNaturalRank degree localRank
  pure (addOrdinals (lanePrefix lane) local)

laneAt :: [Natural] -> Bool -> Natural -> Maybe TraversalLane
laneAt coefficients includeFinite target =
  go [] highestExponent 0 0 target coefficients
  where
    highestExponent = listNaturalLength coefficients - 1
    go _ _ _ _ _ [] = Nothing
    go higher degree overallIndex infiniteIndex remaining
        (coefficient : lower)
      | not includeFinite && degree == 0 = Nothing
      | remaining < coefficient = Just TraversalLane
          { lanePrefix = ordinal
              (higher <> [remaining] <> replicateNatural degree 0)
          , laneExponent = degree
          , laneOverallIndex = overallIndex + remaining
          , laneInfiniteIndex = infiniteIndex + remaining
          , laneRemainder = finiteOrdinal 0
          }
      | otherwise =
          go
            (higher <> [coefficient])
            (if degree == 0 then 0 else degree - 1)
            (overallIndex + coefficient)
            (if degree == 0
              then infiniteIndex
              else infiniteIndex + coefficient)
            (remaining - coefficient)
            lower

laneContaining
  :: [Natural]
  -> [Natural]
  -> Maybe TraversalLane
laneContaining orderCoefficients positionCoefficients =
  go [] highestExponent 0 0 orderCoefficients paddedPosition
  where
    width = listNaturalLength orderCoefficients
    highestExponent = width - 1
    paddedPosition =
      replicateNatural
        (width - listNaturalLength positionCoefficients)
        0
        <> positionCoefficients
    go _ _ _ _ [] _ = Nothing
    go _ _ _ _ _ [] = Nothing
    go higher degree overallIndex infiniteIndex
        (limit : limits) (selected : selecteds)
      | selected < limit = Just TraversalLane
          { lanePrefix = ordinal
              (higher <> [selected] <> replicateNatural degree 0)
          , laneExponent = degree
          , laneOverallIndex = overallIndex + selected
          , laneInfiniteIndex = infiniteIndex + selected
          , laneRemainder = ordinal selecteds
          }
      | selected == limit =
          go
            (higher <> [limit])
            (if degree == 0 then 0 else degree - 1)
            (overallIndex + limit)
            (if degree == 0
              then infiniteIndex
              else infiniteIndex + limit)
            limits
            selecteds
      | otherwise = Nothing

dropFiniteCoefficient :: [Natural] -> [Natural]
dropFiniteCoefficient [] = []
dropFiniteCoefficient [_] = []
dropFiniteCoefficient (coefficient : remaining) =
  coefficient : dropFiniteCoefficient remaining

listNaturalLength :: [value] -> Natural
listNaturalLength [] = 0
listNaturalLength (_ : values) = 1 + listNaturalLength values

replicateNatural :: Natural -> value -> [value]
replicateNatural 0 _ = []
replicateNatural count value =
  value : replicateNatural (count - 1) value
