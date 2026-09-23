{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden implementation of Atlas Map Federations.
module AtlasMapFederation.Internal
  ( AtlasMapFederation
  , atlasMapFederation
  , atlasMapFederationAtlasFederation
  , atlasMapFederationForgottenMap
  ) where

import AtlasFederation (AtlasFederation)
import AtlasMap (AtlasMap)
import DataTransformationMap
  ( DataTransformationMap
  , dataTransformationMap
  )
import Navigation (Navigation)
import StableConfederalData
  ( ForgottenAtlasFederation
  , forgetAtlasFederationToDataTransformation
  )

-- | An Atlas federation whose canonical forgotten DaTra object is a Data
-- Transformation Map. This is the Haskell representation of Lean's
-- @AtlasMapFederation@ refinement.
type role AtlasMapFederation nominal nominal
data AtlasMapFederation federationScope index = AtlasMapFederation
  (AtlasFederation federationScope index)
  (DataTransformationMap
    (ForgottenAtlasFederation federationScope index))

-- | Refine an Atlas federation after proving that its canonical forgotten
-- DaTra object is a Data Transformation Map.
atlasMapFederation
  :: AtlasFederation federationScope index
  -> (forall atlas.
       Navigation atlas (ForgottenAtlasFederation federationScope index)
       -> AtlasMap atlas)
  -> AtlasMapFederation federationScope index
atlasMapFederation federation isDaTraMap =
  AtlasMapFederation
    federation
    (dataTransformationMap
      (forgetAtlasFederationToDataTransformation federation)
      isDaTraMap)

atlasMapFederationAtlasFederation
  :: AtlasMapFederation federationScope index
  -> AtlasFederation federationScope index
atlasMapFederationAtlasFederation (AtlasMapFederation federation _) =
  federation

atlasMapFederationForgottenMap
  :: AtlasMapFederation federationScope index
  -> DataTransformationMap
       (ForgottenAtlasFederation federationScope index)
atlasMapFederationForgottenMap (AtlasMapFederation _ forgottenMap) =
  forgottenMap
