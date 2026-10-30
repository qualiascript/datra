module SyntaxRewriting.Dependencies
  ( DependencyGraph
  , emptyDependencyGraph
  , registerDependencies
  , releaseDependency
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import SyntaxRewriting.Types
  ( RewriteDependency
  , RewriteNodeId
  )

-- Reverse edges retain registration order.  A Map is used only for lookup;
-- its key order never determines scheduler traversal or wakeup order.
newtype DependencyGraph = DependencyGraph
  (Map RewriteDependency [RewriteNodeId])

emptyDependencyGraph :: DependencyGraph
emptyDependencyGraph = DependencyGraph Map.empty

registerDependencies
  :: RewriteNodeId
  -> Set RewriteDependency
  -> DependencyGraph
  -> DependencyGraph
registerDependencies node dependencies (DependencyGraph waiters) =
  DependencyGraph (foldl' register waiters dependencies)
  where
    register current dependency = Map.alter append dependency current
    append Nothing = Just [node]
    append (Just nodes)
      | node `elem` nodes = Just nodes
      | otherwise = Just (nodes <> [node])

releaseDependency
  :: RewriteDependency
  -> DependencyGraph
  -> ([RewriteNodeId], DependencyGraph)
releaseDependency dependency (DependencyGraph waiters) =
  ( Map.findWithDefault [] dependency waiters
  , DependencyGraph (Map.delete dependency waiters)
  )
