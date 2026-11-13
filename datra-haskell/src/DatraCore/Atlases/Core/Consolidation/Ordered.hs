{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | A consolidation certified against the orders of two actual chains.
module Consolidation.Ordered
  ( OrderedConsolidation
  , orderedSource
  , orderedTarget
  , orderedMap
  , orderedMonotone
  , orderedConsolidation
  , identityOrderedConsolidation
  , composeOrderedConsolidations
  ) where

import Chain (Chain)
import Chain.Order (chainPrecedes)
import Consolidation.Core
  ( Consolidation, applyConsolidation, consolidationMonotone
  , identityConsolidation, composeConsolidations )

{-@ data OrderedConsolidation source target = OrderedConsolidation
      { orderedSource :: Chain source
      , orderedTarget :: Chain target
      , orderedMap :: Consolidation
           <{\earlier later -> chainPrecedes orderedSource earlier later},
            {\earlier later -> chainPrecedes orderedTarget earlier later}> source target
      } @-}
data OrderedConsolidation source target = OrderedConsolidation
  { orderedSource :: Chain source
  , orderedTarget :: Chain target
  , orderedMap :: Consolidation source target
  }

{-@ orderedConsolidation :: source:Chain a -> target:Chain b
      -> mapping:Consolidation
           <{\earlier later -> chainPrecedes source earlier later},
            {\earlier later -> chainPrecedes target earlier later}> a b
      -> {result:OrderedConsolidation a b |
            orderedSource result == source && orderedTarget result == target
            && orderedMap result == mapping} @-}
-- ALIGN: CONSOLIDATION-ORDERED.
orderedConsolidation :: Chain a -> Chain b -> Consolidation a b -> OrderedConsolidation a b
orderedConsolidation source target mapping =
  OrderedConsolidation source target mapping

{-@ orderedMonotone :: value:OrderedConsolidation a b
      -> left:a -> right:{a | chainPrecedes (orderedSource value) left right}
      -> {chainPrecedes (orderedTarget value)
            (applyConsolidation (orderedMap value) left)
            (applyConsolidation (orderedMap value) right)} @-}
-- ALIGN: CONSOLIDATION-ORDERED-MONOTONE.
orderedMonotone :: OrderedConsolidation a b -> a -> a -> ()
orderedMonotone (OrderedConsolidation _ _ mapping) left right =
  consolidationMonotone mapping left right `seq` ()

{-@ identityOrderedConsolidation :: page:Chain a
      -> {result:OrderedConsolidation a a |
           orderedSource result == page && orderedTarget result == page
           && orderedMap result == identityConsolidation} @-}
-- ALIGN: CONSOLIDATION-ORDERED-IDENTITY.
identityOrderedConsolidation :: Chain a -> OrderedConsolidation a a
identityOrderedConsolidation page = orderedConsolidation page page identityConsolidation

{-@ composeOrderedConsolidations :: second:OrderedConsolidation b c
      -> first:{OrderedConsolidation a b | orderedTarget first == orderedSource second}
      -> {result:OrderedConsolidation a c |
           orderedSource result == orderedSource first
           && orderedTarget result == orderedTarget second
           && orderedMap result == composeConsolidations (orderedMap second) (orderedMap first)} @-}
-- ALIGN: CONSOLIDATION-ORDERED-COMPOSITION.
composeOrderedConsolidations
  :: OrderedConsolidation b c -> OrderedConsolidation a b -> OrderedConsolidation a c
composeOrderedConsolidations (OrderedConsolidation _ target second)
    (OrderedConsolidation source _ first) =
  orderedConsolidation source target (composeConsolidations second first)
