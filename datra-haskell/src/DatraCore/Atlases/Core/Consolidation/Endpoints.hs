{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ qualif EndpointAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | Reuse actual page chains after checking their positions pointwise.
module Consolidation.Endpoints (withConsolidationEndpoints) where

import Chain.Internal (Chain, chainPosition)
import Chain.Order (chainPrecedes)
import Consolidation.Core (restrictedConsolidation)
import Consolidation.Ordered
  ( OrderedConsolidation, orderedSource, orderedTarget, orderedConsolidation
  , orderedApply, orderedPreimage, orderedFunctions, orderedMonotone, orderedPreimageProof )

-- ALIGN: CONSOLIDATION-ENDPOINTS.
{-@ withConsolidationEndpoints :: sourceContains:(a -> Bool) -> targetContains:(b -> Bool)
      -> mapping:OrderedConsolidation {value:a | sourceContains value} {value:b | targetContains value}
      -> source:Chain {value:a | sourceContains value} -> target:Chain {value:b | targetContains value}
      -> (value:{a | sourceContains value} -> {chainPosition source value == chainPosition (orderedSource mapping) value})
      -> (value:{b | targetContains value} -> {chainPosition target value == chainPosition (orderedTarget mapping) value})
      -> {result:OrderedConsolidation {value:a | sourceContains value} {value:b | targetContains value} | orderedSource result == source && orderedTarget result == target
           && orderedApply result == orderedApply mapping && orderedPreimage result == orderedPreimage mapping} @-}
withConsolidationEndpoints :: (a -> Bool) -> (b -> Bool) -> OrderedConsolidation a b -> Chain a -> Chain b
  -> (a -> ()) -> (b -> ()) -> OrderedConsolidation a b
withConsolidationEndpoints sourceContains targetContains mapping source target sourcePositions targetPositions =
  let result = orderedConsolidation source target
        (restrictedConsolidation sourceContains targetContains (orderedApply mapping) (orderedPreimage mapping)
          (endpointMonotone sourceContains targetContains mapping source target sourcePositions targetPositions)
          (orderedPreimageProof mapping))
  in orderedFunctions result `seq` result

{-@ endpointMonotone :: sourceContains:(a -> Bool) -> targetContains:(b -> Bool)
      -> mapping:OrderedConsolidation {value:a | sourceContains value} {value:b | targetContains value} -> source:Chain {value:a | sourceContains value} -> target:Chain {value:b | targetContains value}
      -> (value:{a | sourceContains value} -> {chainPosition source value == chainPosition (orderedSource mapping) value})
      -> (value:{b | targetContains value} -> {chainPosition target value == chainPosition (orderedTarget mapping) value})
      -> first:{a | sourceContains first} -> mappedFirst:{b | targetContains mappedFirst && mappedFirst == orderedApply mapping first}
      -> second:{a | sourceContains second && chainPrecedes source first second}
      -> {result:b | targetContains result && result == orderedApply mapping second && chainPrecedes target mappedFirst result} @-}
endpointMonotone :: (a -> Bool) -> (b -> Bool) -> OrderedConsolidation a b -> Chain a -> Chain b
  -> (a -> ()) -> (b -> ()) -> a -> b -> a -> b
{-@ ple endpointMonotone @-}
endpointMonotone _ _ mapping _ _ sourcePositions targetPositions first mappedFirst second =
  sourcePositions first `seq` sourcePositions second `seq`
    orderedMonotone mapping first second `seq`
      targetPositions mappedFirst `seq` targetPositions (orderedApply mapping second) `seq`
        orderedApply mapping second
