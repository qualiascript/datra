{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

-- | Checked ordinal sums of consolidations with concrete chain endpoints.
module Consolidation.Sum (sumConsolidations, sumConsolidationsBetween, sumApply, sumPreimage) where

import Chain.Internal (Chain, chainPosition)
import Chain.Order (chainPrecedes)
import Chain.Sum (sumChains, sumChainPosition, sumPrecedes, sumChainOrder)
import Consolidation.Core (consolidation)
import Consolidation.Ordered
  ( OrderedConsolidation, orderedSource, orderedTarget
  , orderedConsolidation, orderedApply, orderedPreimage, orderedPreimageProof, orderedMonotone, orderedFunctions )

-- ALIGN: CONSOLIDATION-SUM.
-- ALIGN: CONSOLIDATION-SUM-INTERPRETATION.
{-@ sumConsolidations :: left:OrderedConsolidation a b -> right:OrderedConsolidation c d
      -> {result:OrderedConsolidation (Either a c) (Either b d) |
           chainPosition (orderedSource result) == sumChainPosition (orderedSource left) (orderedSource right)
           && chainPosition (orderedTarget result) == sumChainPosition (orderedTarget left) (orderedTarget right)
           && orderedApply result == sumApply left right
           && orderedPreimage result == sumPreimage left right} @-}
sumConsolidations
  :: OrderedConsolidation a b -> OrderedConsolidation c d
  -> OrderedConsolidation (Either a c) (Either b d)
sumConsolidations left right =
  sumConsolidationsBetween left right
    (sumChains (orderedSource left) (orderedSource right))
    (sumChains (orderedTarget left) (orderedTarget right))

{-@ sumConsolidationsBetween :: left:OrderedConsolidation a b -> right:OrderedConsolidation c d
      -> source:{Chain (Either a c) |
           chainPosition source == sumChainPosition (orderedSource left) (orderedSource right)}
      -> target:{Chain (Either b d) |
           chainPosition target == sumChainPosition (orderedTarget left) (orderedTarget right)}
      -> {result:OrderedConsolidation (Either a c) (Either b d) |
           orderedSource result == source && orderedTarget result == target
           && orderedApply result == sumApply left right
           && orderedPreimage result == sumPreimage left right} @-}
sumConsolidationsBetween
  :: OrderedConsolidation a b -> OrderedConsolidation c d
  -> Chain (Either a c) -> Chain (Either b d) -> OrderedConsolidation (Either a c) (Either b d)
sumConsolidationsBetween left right source target =
  let result = orderedConsolidation source target
        (consolidation (sumApply left right) (sumPreimage left right)
          (sumMonotone left right source target) (sumSurjective left right))
  in orderedFunctions result `seq` result

{-@ reflect sumApply @-}
sumApply :: OrderedConsolidation a b -> OrderedConsolidation c d -> Either a c -> Either b d
sumApply left _ (Left value) = Left (orderedApply left value)
sumApply _ right (Right value) = Right (orderedApply right value)

{-@ reflect sumPreimage @-}
sumPreimage :: OrderedConsolidation a b -> OrderedConsolidation c d -> Either b d -> Either a c
sumPreimage left _ (Left value) = Left (orderedPreimage left value)
sumPreimage _ right (Right value) = Right (orderedPreimage right value)

{-@ sumSurjective :: left:OrderedConsolidation a b -> right:OrderedConsolidation c d
      -> value:Either b d -> {sumApply left right (sumPreimage left right value) == value} @-}
sumSurjective :: OrderedConsolidation a b -> OrderedConsolidation c d -> Either b d -> ()
{-@ ple sumSurjective @-}
sumSurjective left _ (Left value) = orderedPreimageProof left value
sumSurjective _ right (Right value) = orderedPreimageProof right value

{-@ sumApplyMonotone :: left:OrderedConsolidation a b -> right:OrderedConsolidation c d
      -> first:Either a c -> mappedFirst:{Either b d | mappedFirst == sumApply left right first}
      -> second:{Either a c | sumPrecedes (orderedSource left) (orderedSource right) first second}
      -> {result:Either b d | sumPrecedes (orderedTarget left) (orderedTarget right) mappedFirst result
           && result == sumApply left right second} @-}
sumApplyMonotone :: OrderedConsolidation a b -> OrderedConsolidation c d
  -> Either a c -> Either b d -> Either a c -> Either b d
{-@ ple sumApplyMonotone @-}
sumApplyMonotone left _ (Left first) _ (Left second) =
  orderedMonotone left first second `seq` Left (orderedApply left second)
sumApplyMonotone _ right (Left _) _ (Right second) = Right (orderedApply right second)
sumApplyMonotone left _ (Right _) _ (Left second) = Left (orderedApply left second)
sumApplyMonotone _ right (Right first) _ (Right second) =
  orderedMonotone right first second `seq` Right (orderedApply right second)

{-@ sumMonotone :: left:OrderedConsolidation a b -> right:OrderedConsolidation c d
      -> source:{Chain (Either a c) |
           chainPosition source == sumChainPosition (orderedSource left) (orderedSource right)}
      -> target:{Chain (Either b d) |
           chainPosition target == sumChainPosition (orderedTarget left) (orderedTarget right)}
      -> first:Either a c -> mappedFirst:{Either b d | mappedFirst == sumApply left right first}
      -> second:{Either a c | chainPrecedes source first second}
      -> {result:Either b d | chainPrecedes target mappedFirst result
           && result == sumApply left right second} @-}
sumMonotone :: OrderedConsolidation a b -> OrderedConsolidation c d
  -> Chain (Either a c) -> Chain (Either b d) -> Either a c -> Either b d -> Either a c -> Either b d
{-@ ple sumMonotone @-}
sumMonotone left right _ _ first mappedFirst second =
  sumChainOrder (orderedSource left) (orderedSource right) first second `seq`
    let result = sumApplyMonotone left right first mappedFirst second
    in sumChainOrder (orderedTarget left) (orderedTarget right) mappedFirst result `seq` result
