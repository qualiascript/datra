module DatraLanguage.Application
  ( applicationSelections
  , applicationPhrase
  , applicationSpine
  , rawApplicationPhrase
  , applicationFrom
  ) where

import DatraLanguage.AST (Expression (..))

-- | Enumerate raw application prefixes longest-first.
applicationSelections :: Expression -> [(Expression, [Expression])]
applicationSelections = go []
  where
    go remaining selected =
      (selected, remaining) : case selected of
        FunctionApplication function argument ->
          go (argument : remaining) function
        _ -> []

-- | Project an application to its semantic operands. A logical line break is
-- matcher-visible in the raw phrase but is not an application operand.
applicationPhrase :: Expression -> [Expression]
applicationPhrase = filter (/= LineBreak) . rawApplicationPhrase

applicationSpine :: Expression -> (Expression, [Expression])
applicationSpine value = case applicationPhrase value of
  [] -> (AtlasMap [], [])
  function : arguments -> (function, arguments)

rawApplicationPhrase :: Expression -> [Expression]
rawApplicationPhrase value = case rawSpine value of
  (function, arguments) -> function : arguments

rawSpine :: Expression -> (Expression, [Expression])
rawSpine = go []
  where
    go arguments (FunctionApplication function argument) =
      go (argument : arguments) function
    go arguments function = (function, arguments)

applicationFrom :: [Expression] -> Expression
applicationFrom [] = AtlasMap []
applicationFrom (first : remaining) =
  foldl FunctionApplication first remaining
