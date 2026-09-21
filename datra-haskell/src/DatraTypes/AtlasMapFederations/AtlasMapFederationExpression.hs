-- | Compile-time results and construction trees used by Atlas-map-federation
-- operators in DatraTypes.
module AtlasMapFederationExpression
  ( AtlasMapFederationDecision (..)
  , AtlasMapFederationExpression (..)
  , atlasMapFederationExpressionIsSingleton
  , foldAtlasMapFederationExpression
  ) where

-- | Result of a compile-time proof procedure. A refutation is a proof that
-- an operation is invalid; an undecidable result only says that the compiler
-- has no applicable decision procedure.
data AtlasMapFederationDecision refutation uncertainty proof
  = AtlasMapFederationProved proof
  | AtlasMapFederationRefuted refutation
  | AtlasMapFederationUndecidable uncertainty
  deriving (Eq, Show)

-- | Construction tree for an Atlas-map federation.
--
-- @primitive@ is open to new primitive federation kinds. @singleton@ is the
-- concrete one-map case. Sequential and expansion nodes retain enough
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
