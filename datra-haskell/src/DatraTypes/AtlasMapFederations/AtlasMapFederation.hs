{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Atlas federations whose canonical forgotten DaTra set is a Data
-- Transformation Map, plus the generic compile-time structure used by map
-- operators.
module AtlasMapFederation
  ( AtlasMapFederation
  , atlasMapFederation
  , atlasMapFederationAtlasFederation
  , atlasMapFederationForgottenMap
  , AtlasMapFederationDecision (..)
  , AtlasMapFederationExpression (..)
  , atlasMapFederationExpressionIsSingleton
  , foldAtlasMapFederationExpression
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
-- Transformation Map.
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

-- | Result of a compile-time proof procedure.  A refutation is a proof that
-- an operation is invalid; an undecidable result only says that the compiler
-- has no applicable decision procedure.
data AtlasMapFederationDecision refutation uncertainty proof
  = AtlasMapFederationProved proof
  | AtlasMapFederationRefuted refutation
  | AtlasMapFederationUndecidable uncertainty
  deriving (Eq, Show)

-- | Construction tree for an Atlas-map federation.
--
-- @primitive@ is open to new primitive federation kinds.  @singleton@ is the
-- concrete one-map case.  Sequential and expansion nodes retain enough
-- structure to make their product indices differentiable; concatenation is
-- admitted only after its caller proves injectivity.
data AtlasMapFederationExpression primitive singleton
  = SingletonAtlasMapFederation singleton
  | PrimitiveAtlasMapFederation primitive
  | SequentialAtlasMapFederation
      [AtlasMapFederationExpression primitive singleton]
  | ExpansionAtlasMapFederation
      (AtlasMapFederationExpression primitive singleton)
      (AtlasMapFederationExpression primitive singleton)
  | ConcatenatedAtlasMapFederation
      (AtlasMapFederationExpression primitive singleton)
      (AtlasMapFederationExpression primitive singleton)

atlasMapFederationExpressionIsSingleton
  :: AtlasMapFederationExpression primitive singleton
  -> Bool
atlasMapFederationExpressionIsSingleton
    (SingletonAtlasMapFederation _) = True
atlasMapFederationExpressionIsSingleton _ = False

foldAtlasMapFederationExpression
  :: (singleton -> result)
  -> (primitive -> result)
  -> ([result] -> result)
  -> (result -> result -> result)
  -> (result -> result -> result)
  -> AtlasMapFederationExpression primitive singleton
  -> result
foldAtlasMapFederationExpression onSingleton _ _ _ _
    (SingletonAtlasMapFederation singleton) =
  onSingleton singleton
foldAtlasMapFederationExpression _ onPrimitive _ _ _
    (PrimitiveAtlasMapFederation primitive) =
  onPrimitive primitive
foldAtlasMapFederationExpression
    onSingleton onPrimitive onSequential onExpansion onConcatenation
    (SequentialAtlasMapFederation members) =
  onSequential (map recur members)
  where
    recur = foldAtlasMapFederationExpression
      onSingleton onPrimitive onSequential onExpansion onConcatenation
foldAtlasMapFederationExpression
    onSingleton onPrimitive onSequential onExpansion onConcatenation
    (ExpansionAtlasMapFederation left right) =
  onExpansion (recur left) (recur right)
  where
    recur = foldAtlasMapFederationExpression
      onSingleton onPrimitive onSequential onExpansion onConcatenation
foldAtlasMapFederationExpression
    onSingleton onPrimitive onSequential onExpansion onConcatenation
    (ConcatenatedAtlasMapFederation left right) =
  onConcatenation (recur left) (recur right)
  where
    recur = foldAtlasMapFederationExpression
      onSingleton onPrimitive onSequential onExpansion onConcatenation
