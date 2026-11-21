{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--higherorder" @-}
{-@ qualif ReindexAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | Transport an ordered consolidation through checked carrier equivalences.
module Consolidation.Reindex (reindexConsolidation, reindexApply, reindexPreimage) where

import Chain (Chain, chainPosition, chainOrderType, reindexChain, reindexedPosition)
import Chain.Order (chainPrecedes, reindexedPrecedes)
import Consolidation.Core (restrictedConsolidation)
import Consolidation.Ordered
  ( OrderedConsolidation, orderedConsolidation, orderedSource, orderedTarget
  , orderedApply, orderedPreimage, orderedMonotone, orderedPreimageProof, orderedFunctions )

-- ALIGN: CONSOLIDATION-REINDEX.
{-@ reindexConsolidation :: sourceContains:(c -> Bool) -> targetContains:(d -> Bool)
      -> mapping:OrderedConsolidation a b
      -> sourceFrom:(a -> {value:c | sourceContains value})
      -> sourceTo:({value:c | sourceContains value} -> a)
      -> (value:a -> {sourceTo (sourceFrom value) == value})
      -> (value:{c | sourceContains value} -> {sourceFrom (sourceTo value) == value})
      -> targetFrom:(b -> {value:d | targetContains value})
      -> targetTo:({value:d | targetContains value} -> b)
      -> (value:b -> {targetTo (targetFrom value) == value})
      -> (value:{d | targetContains value} -> {targetFrom (targetTo value) == value})
      -> {result:OrderedConsolidation {value:c | sourceContains value} {value:d | targetContains value} |
           chainPosition (orderedSource result) == reindexedPosition sourceContains (orderedSource mapping) sourceTo
           && chainPosition (orderedTarget result) == reindexedPosition targetContains (orderedTarget mapping) targetTo
           && chainOrderType (orderedSource result) == chainOrderType (orderedSource mapping)
           && chainOrderType (orderedTarget result) == chainOrderType (orderedTarget mapping)
           && orderedApply result == reindexApply mapping targetFrom sourceTo
           && orderedPreimage result == reindexPreimage mapping sourceFrom targetTo} @-}
reindexConsolidation :: (c -> Bool) -> (d -> Bool) -> OrderedConsolidation a b
  -> (a -> c) -> (c -> a) -> (a -> ()) -> (c -> ())
  -> (b -> d) -> (d -> b) -> (b -> ()) -> (d -> ()) -> OrderedConsolidation c d
reindexConsolidation sourceContains targetContains mapping
    sourceFrom sourceTo sourceLeft sourceRight targetFrom targetTo targetLeft targetRight =
  let source = reindexChain sourceContains (orderedSource mapping) sourceFrom sourceTo sourceLeft sourceRight
      target = reindexChain targetContains (orderedTarget mapping) targetFrom targetTo targetLeft targetRight
      result = orderedConsolidation source target
       (restrictedConsolidation sourceContains targetContains
         (reindexApply mapping targetFrom sourceTo)
         (reindexPreimage mapping sourceFrom targetTo)
         (reindexMonotone sourceContains targetContains mapping targetFrom sourceTo targetTo targetLeft source target)
         (reindexSurjective mapping sourceFrom sourceTo sourceLeft targetFrom targetTo targetRight))
  in orderedFunctions result `seq` result

{-@ reflect reindexApply @-}
reindexApply :: OrderedConsolidation a b -> (b -> d) -> (c -> a) -> c -> d
reindexApply mapping targetFrom sourceTo value = targetFrom (orderedApply mapping (sourceTo value))

{-@ reflect reindexPreimage @-}
reindexPreimage :: OrderedConsolidation a b -> (a -> c) -> (d -> b) -> d -> c
reindexPreimage mapping sourceFrom targetTo value = sourceFrom (orderedPreimage mapping (targetTo value))

{-@ reindexSurjective :: mapping:OrderedConsolidation a b
      -> sourceFrom:(a -> c) -> sourceTo:(c -> a)
      -> (value:a -> {sourceTo (sourceFrom value) == value})
      -> targetFrom:(b -> d) -> targetTo:(d -> b)
      -> (value:d -> {targetFrom (targetTo value) == value})
      -> value:d -> {reindexApply mapping targetFrom sourceTo
            (reindexPreimage mapping sourceFrom targetTo value) == value} @-}
reindexSurjective :: OrderedConsolidation a b -> (a -> c) -> (c -> a) -> (a -> ())
  -> (b -> d) -> (d -> b) -> (d -> ()) -> d -> ()
{-@ ple reindexSurjective @-}
reindexSurjective mapping _ _ sourceLeft _ targetTo targetRight value =
  sourceLeft (orderedPreimage mapping (targetTo value)) `seq`
    orderedPreimageProof mapping (targetTo value) `seq` targetRight value

{-@ reindexMonotone :: sourceContains:(c -> Bool) -> targetContains:(d -> Bool)
      -> mapping:OrderedConsolidation a b
      -> targetFrom:(b -> {value:d | targetContains value})
      -> sourceTo:({value:c | sourceContains value} -> a)
      -> targetTo:({value:d | targetContains value} -> b)
      -> (value:b -> {targetTo (targetFrom value) == value})
      -> source:{Chain {value:c | sourceContains value} |
           chainPosition source == reindexedPosition sourceContains (orderedSource mapping) sourceTo}
      -> target:{Chain {value:d | targetContains value} |
           chainPosition target == reindexedPosition targetContains (orderedTarget mapping) targetTo}
      -> first:{c | sourceContains first}
      -> mappedFirst:{d | targetContains mappedFirst && mappedFirst == reindexApply mapping targetFrom sourceTo first}
      -> second:{c | sourceContains second && chainPrecedes source first second}
      -> {result:d | targetContains result && chainPrecedes target mappedFirst result
           && result == reindexApply mapping targetFrom sourceTo second} @-}
reindexMonotone :: (c -> Bool) -> (d -> Bool) -> OrderedConsolidation a b
  -> (b -> d) -> (c -> a) -> (d -> b) -> (b -> ()) -> Chain c -> Chain d -> c -> d -> c -> d
{-@ ple reindexMonotone @-}
reindexMonotone sourceContains targetContains mapping targetFrom sourceTo targetTo targetLeft source target first mappedFirst second =
  reindexedPrecedes sourceContains (orderedSource mapping) sourceTo source first second `seq`
  orderedMonotone mapping (sourceTo first) (sourceTo second) `seq`
    targetLeft (orderedApply mapping (sourceTo first)) `seq`
      targetLeft (orderedApply mapping (sourceTo second)) `seq`
        let result = reindexApply mapping targetFrom sourceTo second
        in reindexedPrecedes targetContains (orderedTarget mapping) targetTo target mappedFirst result `seq` result
