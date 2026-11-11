-- | Semantic roles for Datra's dynamically introduced contextual
-- declarations. This module owns their source spelling; the AST itself keeps
-- representing them as ordinary declarations, identifiers, and applications.
module DatraLanguage.ContextualRole
  ( ContextualRole (..)
  , contextualSurfaceName
  , contextualPrivateName
  ) where

data ContextualRole
  = ContextualThis
  | ContextualIt
  deriving (Bounded, Enum, Eq, Ord, Show)

contextualSurfaceName :: ContextualRole -> String
contextualSurfaceName ContextualThis = "this"
contextualSurfaceName ContextualIt = "it"

contextualPrivateName :: ContextualRole -> String
contextualPrivateName role = '_' : contextualSurfaceName role
