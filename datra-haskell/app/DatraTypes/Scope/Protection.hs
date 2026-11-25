module DatraTypes.Scope.Protection
  ( ScopeHandoffDecision (..)
  ) where

-- | The disposition of a protected value crossing a lexical-scope boundary.
-- The operations implementing the decision belong to evaluation, not to this
-- representation module.
data ScopeHandoffDecision
  = PreserveScopeProtection
  | TransferScopeProtection
  | RejectScopeProtection
  deriving (Eq, Show)
