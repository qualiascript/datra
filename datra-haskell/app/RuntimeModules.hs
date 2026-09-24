-- | Runtime module sources and the evaluation-mode transformation applied to
-- a root program and every module in its dependency graph.
module RuntimeModules
  ( ModuleSource (..)
  , EvaluationMode (..)
  , expressionForMode
  , modulesForMode
  ) where

import DatraLanguage.AST (Expression (..), mapExpressionChildren)

data ModuleSource
  = StdLibModule
  | ModuleSource FilePath Expression [(String, ModuleSource)]

data EvaluationMode
  = DevelopmentMode
  | ProductionMode
  deriving (Eq, Show)

expressionForMode :: EvaluationMode -> Expression -> Expression
expressionForMode DevelopmentMode = id
expressionForMode ProductionMode = removeSoftAssertions
  where
    removeSoftAssertions (Assert False _) = AtlasMap []
    removeSoftAssertions expressionValue =
      mapExpressionChildren removeSoftAssertions expressionValue

modulesForMode
  :: EvaluationMode
  -> [(String, ModuleSource)]
  -> [(String, ModuleSource)]
modulesForMode mode = map transformNamed
  where
    transformNamed (name, source) = (name, transform source)
    transform StdLibModule = StdLibModule
    transform (ModuleSource path expression dependencies) =
      ModuleSource
        path
        (expressionForMode mode expression)
        (modulesForMode mode dependencies)
