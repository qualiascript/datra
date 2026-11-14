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
  , orderedOpposite
  , orderedApply
  , orderedPreimage
  , orderedPreimageProof
  , orderedFunctions
  ) where

import Chain (Chain)
import Chain.Order (chainPrecedes)
import Consolidation.Core
  ( Consolidation (..), Coconsolidation, op, unop, consolidationMonotone
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
            (orderedApply value left) (orderedApply value right)} @-}
-- ALIGN: CONSOLIDATION-ORDERED-MONOTONE.
orderedMonotone :: OrderedConsolidation a b -> a -> a -> ()
orderedMonotone value@(OrderedConsolidation _ _ mapping) left right =
  consolidationMonotone mapping left right `seq` orderedFunctions value

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

{-@ orderedOpposite :: value:OrderedConsolidation a b
      -> {result:Coconsolidation
           <{\earlier later -> chainPrecedes (orderedTarget value) earlier later},
            {\earlier later -> chainPrecedes (orderedSource value) earlier later}> b a |
              unop result == orderedMap value} @-}
orderedOpposite :: OrderedConsolidation a b -> Coconsolidation b a
orderedOpposite (OrderedConsolidation _ _ mapping) = op mapping

{-@ reflect orderedApply @-}
{-@ orderedApply :: value:OrderedConsolidation a b
      -> {forward:(a -> b) | forward == applyConsolidation (orderedMap value)} @-}
orderedApply :: OrderedConsolidation a b -> a -> b
orderedApply (OrderedConsolidation _ _ (Consolidation forward _ _ _)) = forward

{-@ reflect orderedPreimage @-}
{-@ orderedPreimage :: value:OrderedConsolidation a b
      -> {backward:(b -> a) | backward == consolidationPreimage (orderedMap value)} @-}
orderedPreimage :: OrderedConsolidation a b -> b -> a
orderedPreimage (OrderedConsolidation _ _ (Consolidation _ backward _ _)) = backward

{-@ orderedPreimageProof :: mapping:OrderedConsolidation a b -> value:b
      -> {orderedApply mapping (orderedPreimage mapping value) == value} @-}
-- ALIGN: CONSOLIDATION-ORDERED-PREIMAGE.
orderedPreimageProof :: OrderedConsolidation a b -> b -> ()
orderedPreimageProof (OrderedConsolidation _ _ (Consolidation _ _ _ inverseProof)) value =
  inverseProof value

-- | Relate the public scalar operations to the stored function fields.
{-@ orderedFunctions :: value:OrderedConsolidation a b
      -> {orderedApply value == applyConsolidation (orderedMap value)
           && orderedPreimage value == consolidationPreimage (orderedMap value)} @-}
orderedFunctions :: OrderedConsolidation a b -> ()
orderedFunctions value@(OrderedConsolidation _ _ (Consolidation {})) =
  orderedApply value `seq` orderedPreimage value `seq` ()
