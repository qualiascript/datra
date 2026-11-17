module DatraLanguage.Application
  ( applicationSelections
  , applicationPhrase
  , applicationSpine
  , rawApplicationPhrase
  , applicationFrom
  , presentedApplication
  , presentationLiteral
  ) where

import DatraLanguage.AST (Expression (..))
import DatraLanguage.ConcreteSyntax
  ( isSourcePresentationCharacter )

-- | Enumerate raw application prefixes longest-first. Unconsumed operands are
-- retained exactly, including unresolved whitespace literals.
applicationSelections :: Expression -> [(Expression, [Expression])]
applicationSelections = go []
  where
    go remaining selected =
      (selected, remaining) : case selected of
        FunctionApplication function argument ->
          go (argument : remaining) function
        _ -> []

-- | Project an application to its semantic operands. Presentation literals
-- have no structural position after a matcher has selected an extent.
applicationPhrase :: Expression -> [Expression]
applicationPhrase = filter (not . presentationLiteral) . rawApplicationPhrase

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

-- | Retain a consumed source separator as an ordinary unresolved operand.
-- Its eventual application or sequencing meaning belongs to built-in
-- dependent declarations, not to the parser.
presentedApplication :: String -> Expression -> Expression -> Expression
presentedApplication separator left right
  | null separator = FunctionApplication left right
  | otherwise = FunctionApplication
      (FunctionApplication left (UnresolvedSyntaxLiteral separator))
      right

presentationLiteral :: Expression -> Bool
presentationLiteral (UnresolvedSyntaxLiteral source) =
  not (null source) && all isSourcePresentationCharacter source
presentationLiteral _ = False
