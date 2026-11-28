{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | Coalitions and the Coalizing functor from stable Atlas transversals to
-- domanial insertions.
module Coalition
  ( CoalitionElement
  , coalitionElementRank
  , withCoalitionElement
  , coalition
  , stableCoalitionMap
  , coalizingFunctorObject
  , coalizingFunctorHom
  , coalizingIdentityMap
  , coalizingFunctorIdentity
  , coalizingFunctorComposition
  , coalizingFunctorCompositionPreimage
  ) where

import Coalition.Internal
