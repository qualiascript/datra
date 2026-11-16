module DatraLanguage.Application
  ( applicationSelections
  , applicationPhrase
  , nativeApplicationPhrase
  , applicationSpine
  , applicationFrom
  , presentedApplication
  , trailingHorizontalSyntax
  , syntaxWhitespaceSource
  , horizontalSyntaxWhitespace
  , lineSyntaxWhitespace
  , lineSeparatedApplication
  , horizontallySeparatedApplication
  ) where

import Control.Monad (guard)
import Data.Char (isSpace)
import DatraLanguage.AST (Expression (..))

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

-- | Structural application projection used by Atlas syntax and syntax-value
-- captures. Whitespace literals have no structural position in this mode.
applicationPhrase :: Expression -> [Expression]
applicationPhrase = filter (not . syntaxWhitespaceLiteral) . rawPhrase

-- | Native application ignores horizontal separators but cannot cross a line
-- separator before the newline declaration establishes a sequence boundary.
nativeApplicationPhrase :: Expression -> Maybe [Expression]
nativeApplicationPhrase value = do
  let phrase = rawPhrase value
  guard (not (any lineWhitespaceLiteral phrase))
  pure (filter (not . horizontalWhitespaceLiteral) phrase)

applicationSpine :: Expression -> (Expression, [Expression])
applicationSpine value = case applicationPhrase value of
  [] -> (AtlasMap [], [])
  function : arguments -> (function, arguments)

rawPhrase :: Expression -> [Expression]
rawPhrase value = case rawSpine value of
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

-- | Recover horizontal trivia consumed by an existing lexeme parser. This is
-- the only character-level compatibility boundary needed by source parsing.
trailingHorizontalSyntax :: String -> String
trailingHorizontalSyntax = reverse
  . takeWhile horizontalCharacter
  . reverse

syntaxWhitespaceSource :: String -> Bool
syntaxWhitespaceSource source =
  not (null source) && all isSpace source

horizontalSyntaxWhitespace :: String -> Bool
horizontalSyntaxWhitespace source =
  syntaxWhitespaceSource source && not (containsLineBoundary source)

lineSyntaxWhitespace :: String -> Bool
lineSyntaxWhitespace source =
  syntaxWhitespaceSource source && containsLineBoundary source

syntaxWhitespaceLiteral :: Expression -> Bool
syntaxWhitespaceLiteral (UnresolvedSyntaxLiteral source) =
  syntaxWhitespaceSource source
syntaxWhitespaceLiteral _ = False

horizontalWhitespaceLiteral :: Expression -> Bool
horizontalWhitespaceLiteral (UnresolvedSyntaxLiteral source) =
  horizontalSyntaxWhitespace source
horizontalWhitespaceLiteral _ = False

lineWhitespaceLiteral :: Expression -> Bool
lineWhitespaceLiteral (UnresolvedSyntaxLiteral source) =
  lineSyntaxWhitespace source
lineWhitespaceLiteral _ = False

-- | Final newline fallback. Split the complete presentation phrase without
-- disturbing horizontal separators inside each line.
lineSeparatedApplication :: Expression -> Maybe Expression
lineSeparatedApplication expressionValue = do
  let (completedReversed, currentReversed, foundLine) =
        foldl splitLine ([], [], False) (rawPhrase expressionValue)
      linePhrases = reverse
        (reverse currentReversed : completedReversed)
  guard foundLine
  guard (all (not . null) linePhrases)
  pure (AtlasMap (map applicationFrom linePhrases))
  where
    splitLine (completed, current, foundLine) member
      | lineWhitespaceLiteral member =
          (reverse current : completed, [], True)
      | otherwise = (completed, member : current, foundLine)

-- | Final horizontal fallback. Compact adjacency is deliberately untouched.
-- A separator-only subtree has no application to construct; ordinary syntax
-- finalization turns that exhausted literal into 'ElidedSyntax'.
horizontallySeparatedApplication :: Expression -> Maybe Expression
horizontallySeparatedApplication expressionValue = do
  let phrase = rawPhrase expressionValue
      operands = filter (not . horizontalWhitespaceLiteral) phrase
  guard (not (any lineWhitespaceLiteral phrase))
  guard (any horizontalWhitespaceLiteral phrase)
  case operands of
    [] -> Nothing
    _ -> pure (applicationFrom operands)

horizontalCharacter :: Char -> Bool
horizontalCharacter character =
  isSpace character && not (lineBoundary character)

containsLineBoundary :: String -> Bool
containsLineBoundary = any lineBoundary

lineBoundary :: Char -> Bool
lineBoundary character = character == '\n' || character == '\r'
