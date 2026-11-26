{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | Checked primitive morphisms between the owning accepted data carriers.
-- Naturality observations require valid owning arrows and accepted source data.
module Atlas.Morphism
  ( AtlasMorphismAction
  , AtlasObjectMap
  , AtlasMappedObject
  , IdentityAtlasObjectMap
  , identityAtlasObjectMap
  , identityAtlasMorphismObject
  , identityAtlasMorphismPreservesArrow
  , atlasObjectMap
  , atlasMorphismAction
  , atlasMorphismSource
  , atlasMorphismTarget
  , mapAtlasMorphismActionObject
  , mapAtlasMorphismActionComponent
  , mapAtlasMorphismActionElement
  , mapPrimitiveElement
  , atlasMorphismActionPreservesArrow
  , atlasMorphismActionNaturality
  , atlasMorphismObjectMapWitness
  , normalizeAtlasMorphismAction
  , normalizeAtlasMorphismActionRetains
  ) where

import Atlas.Morphism.LiquidInternal
  ( AtlasMorphismAction
  , AtlasObjectMap
  , AtlasMappedObject
  , IdentityAtlasObjectMap
  , identityAtlasObjectMap
  , identityAtlasMorphismObject
  , identityAtlasMorphismPreservesArrow
  , atlasObjectMap
  , atlasMorphismAction
  , atlasMorphismSource
  , atlasMorphismTarget
  , mapAtlasMorphismActionObject
  , mapAtlasMorphismActionComponent
  , mapAtlasMorphismActionElement
  , mapPrimitiveElement
  , atlasMorphismActionPreservesArrow
  , atlasMorphismActionNaturality
  , atlasMorphismObjectMapWitness
  , normalizeAtlasMorphismAction
  , normalizeAtlasMorphismActionRetains
  )
