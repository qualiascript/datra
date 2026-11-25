module DatraTypes.Scope
  ( Scope (..)
  , ScopeHandoff (..)
  , ScopedDependentDeclaration (..)
  , RuntimeSingletonPayload (..)
  , RuntimeDeclarationValue (..)
  , RuntimeDeclarationPresentation (..)
  , DeclarationLayerOrigin (..)
  , DeclarationLayerImportPolicy (..)
  , DependentDeclarationLayer (..)
  ) where

import DatraLanguage.AST (Expression)
import DatraLanguage.ContextualDeclaration (ContextualRole)
import DatraLanguage.DependentDeclaration (DependentDeclaration)
import DatraTypes
import DatraTypes.Closure (DependencyAddress)
import DatraTypes.Resolution (ResolutionStack)
import DatraTypes.Scope.Protection (ScopeHandoffDecision)

-- | A scope owns the declaration layers and runtime authority active at one
-- lexical point.  Syntax visibility will be indexed by these same declaration
-- layers; it must not be represented by a parallel context.
data Scope = Scope
  { scopeDependentDeclarationLayers :: [DependentDeclarationLayer]
  , scopePresentationOwner :: Maybe PresentationOwner
  , scopeActivation :: ScopeActivation
  , scopeHandoff :: Maybe ScopeHandoff
  }

data ScopeHandoff = ScopeHandoff
  { scopeHandoffReceiver :: ScopeActivation
  , scopeHandoffPolicyDecision
      :: ScopeProtectionPolicy -> ScopeHandoffDecision
  }

-- | A declaration's name family and implementation are interpreted in the
-- lexical snapshots at its source position.  This representation is mutually
-- recursive with 'Scope', so the complete runtime declaration SCC lives here.
data ScopedDependentDeclaration
  = ScopedDatraDependentDeclaration
      Scope
      Scope
      (DependentDeclaration Expression)
      (Maybe RuntimeSingletonPayload)
  | ScopedRuntimeSingletonDeclaration Scope RuntimeSingletonPayload
  | ScopedProjectedDependentDeclaration Scope NamedMapView

-- | Metadata for a runtime-created singleton declaration.  Runtime names use
-- the same declaration layers, overlap checks, protection, and closure rules
-- as source declarations.
data RuntimeSingletonPayload = RuntimeSingletonPayload
  { runtimeDeclarationName :: String
  , runtimeDeclarationIsDefinition :: Bool
  , runtimeDeclarationValue :: RuntimeDeclarationValue
  , runtimeDeclarationPresentation :: RuntimeDeclarationPresentation
  , runtimeDeclarationOrigin :: Maybe DependencyAddress
  , runtimeDeclarationDefinition
      :: Maybe (Scope, Maybe Expression, Expression)
  , runtimeDeclarationPublicScope :: Maybe Scope
  , runtimeDeclarationReevaluatesForRestrictedReduction :: Bool
  }

data RuntimeDeclarationValue
  = EvaluatedRuntimeValue InterpretedValue
  | ContextualRuntimeValue
      ContextualRole
      Bool
      (Maybe [ScopedDependentDeclaration])
      (ResolutionStack
        -> ReductionContext
        -> Either InterpretingError InterpretedValue)

data RuntimeDeclarationPresentation
  = DirectRuntimePresentation
  | ReferencedRuntimePresentation [PresentationOwner]
  | TransparentRuntimePresentation

data DeclarationLayerOrigin
  = SourceDeclarationLayer
  | RuntimeDeclarationLayer
  deriving (Eq)

data DeclarationLayerImportPolicy
  = LocalDeclarationLayer
  | PreferentialImport
  | StrictImport
  deriving (Eq)

data DependentDeclarationLayer = DependentDeclarationLayer
  { dependentDeclarationLayerOrigin :: DeclarationLayerOrigin
  , dependentDeclarationLayerImportPolicy :: DeclarationLayerImportPolicy
  , dependentDeclarationLayerMembers :: [ScopedDependentDeclaration]
  }
