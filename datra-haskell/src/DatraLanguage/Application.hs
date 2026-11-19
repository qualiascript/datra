module DatraLanguage.Application
  ( applicationSelections
  , applicationPhrase
  , applicationSpine
  , rawApplicationPhrase
  , unresolvedApplicationFrom
  , applicationFrom
  ) where

import DatraLanguage.AST (Expression (..))

-- | Enumerate raw application prefixes longest-first.
applicationSelections :: Expression -> [(Expression, [Expression])]
applicationSelections value@UnresolvedApplication {} =
  [ (unresolvedApplicationFrom selected, remaining)
  | count <- reverse [1 .. length phrase]
  , let (selected, remaining) = splitAt count phrase
  ]
  where
    phrase = rawApplicationPhrase value
applicationSelections value = go [] value
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
rawApplicationPhrase (UnresolvedApplication expressions) = expressions
rawApplicationPhrase value = case rawSpine value of
  (function, arguments) -> function : arguments

rawSpine :: Expression -> (Expression, [Expression])
rawSpine = go []
  where
    go arguments (FunctionApplication function argument) =
      go (argument : arguments) function
    go arguments function = (function, arguments)

unresolvedApplicationFrom :: [Expression] -> Expression
unresolvedApplicationFrom [] = AtlasMap []
unresolvedApplicationFrom [expressionValue] = expressionValue
unresolvedApplicationFrom expressions = UnresolvedApplication expressions

applicationFrom :: [Expression] -> Expression
applicationFrom [] = AtlasMap []
applicationFrom (first : remaining) =
  foldl FunctionApplication first remaining
