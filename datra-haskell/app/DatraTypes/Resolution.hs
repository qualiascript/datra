module DatraTypes.Resolution
  ( ResolutionKey (..)
  , ResolutionStack
  ) where

import DatraLanguage.AST (Expression)

-- | One active identifier-definition evaluation.  The expression is retained
-- so genuinely distinct recursive definitions with the same spelling do not
-- share a recursion guard.
data ResolutionKey = ResolutionKey String Expression
  deriving (Eq)

type ResolutionStack = [ResolutionKey]
