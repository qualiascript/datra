module DatraTypes.Closure
  ( DependencyKey (..)
  , DependencyAddress (..)
  , DependencyPath (..)
  , DependencyRoot (..)
  , Dependency (..)
  , Resolver (..)
  ) where

import DatraLanguage.AST
import DatraLanguage.ContextualDeclaration (ContextualRole)
import Numeric.Natural (Natural)

-- | Runtime dependency identity and resolver types.  Dependency discovery and
-- AST rewriting are evaluation operations and live in 'Evaluation.Closure'.
newtype DependencyAddress = DependencyAddress
  { dependencyAddressSegments :: [SimpleIdentifierString]
  }
  deriving (Eq, Show)

data DependencyKey
  = BindingDependency String Expression
  deriving (Eq, Show)

data Dependency = Dependency
  { dependencyKey :: DependencyKey
  , dependencyAddress :: DependencyAddress
  , dependencyDeclaration :: DependentDeclaration Expression
  , dependencyResolver :: Resolver
  }

data DependencyRoot
  = AmbientRoot
  | ContextualRoot ContextualRole
  deriving (Eq, Show)

data DependencyPath = DependencyPath
  { dependencyPathRoot :: DependencyRoot
  , dependencyPathSegments :: [String]
  }
  deriving (Eq, Show)

data Resolver = Resolver
  { resolveDependency :: DependencyPath -> Maybe Dependency
  , resolveScopeIndex :: Expression -> Maybe String
  , resolveContextualDepth :: ContextualRole -> Natural -> Maybe Dependency
  , resolveDefinitionReference :: DependencyPath -> Bool
  }
