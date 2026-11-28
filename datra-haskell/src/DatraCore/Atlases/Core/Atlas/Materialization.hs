{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | Endpoint observations of the actual symbolic materialization. These retain
-- complete owners even when nominal object indices alone do not identify them.
module Atlas.Materialization
  ( morphismSourceOwner, morphismTargetOwner, homSourceOwner, homTargetOwner
  , atlasMorphismTargetWitness, targetAtlasWitness, materializeAtlasHom
  ) where

import Atlas.Morphism.Internal
  ( morphismSourceOwner, morphismTargetOwner, homSourceOwner, homTargetOwner
  , atlasMorphismTargetWitness, targetAtlasWitness, materializeAtlasHom )
