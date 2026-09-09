{-# LANGUAGE CPP #-}
#include "../LiquidPlugin.h"
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | LiquidHaskell-verified consolidation-transport representation and functor laws.
module ConsolidationTransport.LiquidInternal
  ( ConsolidationTransport (..)
  , consolidationTransport
  , consolidationTransportIdentity
  , consolidationTransportComposition
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

-- | A morphism in the target of the consolidation-transport functor.
--
-- Haskell already represents the object part of @Tra : Con -> Type@ with the
-- carrier type parameters @source@ and @target@. This wrapper makes its
-- morphism part explicit without discarding those types.
{-@
data ConsolidationTransport source target = ConsolidationTransport
  { runConsolidationTransport :: source -> target }
@-}
data ConsolidationTransport source target = ConsolidationTransport
  { runConsolidationTransport :: source -> target
  }

-- | The morphism action of the consolidation-transport functor.
{-@ reflect consolidationTransport @-}
consolidationTransport
  :: Consolidation source target
  -> ConsolidationTransport source target
consolidationTransport value = ConsolidationTransport (applyConsolidation value)

-- | Consolidation transport preserves identity pointwise.
{-@
consolidationTransportIdentity
  :: value:object ->
     { proof:() |
       runConsolidationTransport (consolidationTransport identityConsolidation) value
         == value }
@-}
consolidationTransportIdentity :: object -> ()
consolidationTransportIdentity = identityConsolidationApply

-- | Consolidation transport preserves composition pointwise.
{-@
consolidationTransportComposition
  :: second:Consolidation middle target
  -> first:Consolidation source middle
  -> value:source
  -> { proof:() |
       runConsolidationTransport
         (consolidationTransport (composeConsolidations second first)) value
         == runConsolidationTransport (consolidationTransport second)
              (runConsolidationTransport (consolidationTransport first) value) }
@-}
consolidationTransportComposition
  :: Consolidation middle target
  -> Consolidation source middle
  -> source
  -> ()
consolidationTransportComposition = composeConsolidationsApply
