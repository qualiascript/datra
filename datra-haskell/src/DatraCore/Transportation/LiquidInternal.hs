{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | LiquidHaskell-verified transportation representation and functor laws.
module Transportation.LiquidInternal
  ( Transportation (..)
  , transportation
  , transportationIdentity
  , transportationComposition
  ) where

import Consolidation.LiquidInternal
  ( Consolidation
  , applyConsolidation
  , composeConsolidations
  , composeConsolidationsApply
  , composeFunctions
  , composeMonotone
  , composePointSurjective
  , identityConsolidation
  , identityConsolidationApply
  , identityMap
  , identityMonotone
  , identityPointSurjective
  )

-- | A morphism in the target of the transportation functor.
--
-- Haskell already represents the object part of @Tra : Con -> Type@ with the
-- carrier type parameters @source@ and @target@. This wrapper makes its
-- morphism part explicit without discarding those types.
{-@
data Transportation source target = Transportation
  { runTransportation :: source -> target }
@-}
data Transportation source target = Transportation
  { runTransportation :: source -> target
  }

-- | The morphism action of the transportation functor.
{-@ reflect transportation @-}
transportation
  :: Consolidation source target
  -> Transportation source target
transportation value = Transportation (applyConsolidation value)

-- | Transportation preserves identity pointwise.
{-@
transportationIdentity
  :: value:object ->
     { proof:() |
       runTransportation (transportation identityConsolidation) value
         == value }
@-}
transportationIdentity :: object -> ()
transportationIdentity = identityConsolidationApply

-- | Transportation preserves composition pointwise.
{-@
transportationComposition
  :: second:Consolidation middle target
  -> first:Consolidation source middle
  -> value:source
  -> { proof:() |
       runTransportation
         (transportation (composeConsolidations second first)) value
         == runTransportation (transportation second)
              (runTransportation (transportation first) value) }
@-}
transportationComposition
  :: Consolidation middle target
  -> Consolidation source middle
  -> source
  -> ()
transportationComposition = composeConsolidationsApply
