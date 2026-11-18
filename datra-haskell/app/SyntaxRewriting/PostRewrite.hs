-- | Internal candidates which run after declarative syntax has had the first
-- opportunity to consume a complete source phrase.
module SyntaxRewriting.PostRewrite
  ( postRewriteCandidate
  , postRewriteExpansion
  ) where

import DatraLanguage.AST (Expression (..))
import DatraLanguage.AST.Syntax ((<:>))
import DatraLanguage.Application
  ( rawApplicationPhrase
  , unresolvedApplicationFrom
  )
import StringExpression (TemplateSelection (..))
import StringInterpolation
  ( DeclarativeMatcherPlan (..)
  , LiteralExpressionPattern (..)
  , SyntaxRule (..)
  , SyntaxRuleSemantics (..)
  )
import SyntaxRewriting.Candidates (compileRewriteRule)
import SyntaxRewriting.Types (StructuralCandidate (..))

postRewriteCandidate
  :: (Expression -> Bool)
  -> Expression
  -> Maybe StructuralCandidate
postRewriteCandidate hasDeclaredCandidate source = do
  expansion <- terminalFallback hasDeclaredCandidate source
  let rule = SyntaxRule
        { declarativeMatcherPlan = LiteralExpressionMatcher
            (LiteralExpressionPattern [])
        , syntaxSemantics = SyntaxPostRewrite expansion
        }
  pure StructuralCandidate
    { structuralCandidateRule = compileRewriteRule rule
    , structuralCandidateBranch = 0
    , structuralCandidateSelection = TemplateSelection source []
    , structuralCandidateCaptures = []
    , structuralCandidateRemaining = []
    }

-- Reapply a declarative candidate's unconsumed phrase through the same
-- terminal operation used when no declaration matched at all. This is the
-- point where an expanded prefix has finished consuming syntax but its source
-- continuation has not yet entered ordinary traversal.
postRewriteExpansion
  :: (Expression -> Bool)
  -> Expression
  -> [Expression]
  -> Expression
postRewriteExpansion hasDeclaredCandidate expansion remaining =
  maybe source id (terminalFallback hasDeclaredCandidate source)
  where
    source = unresolvedApplicationFrom (expansion : remaining)

terminalFallback
  :: (Expression -> Bool)
  -> Expression
  -> Maybe Expression
terminalFallback hasDeclaredCandidate source =
  case lineBreakFallback source of
    Just expansion -> Just expansion
    Nothing -> applicationFallback hasDeclaredCandidate source

-- Split only the first unconsumed logical line break. The untouched tail is
-- re-entered as a fresh phrase, so syntax beginning on its first line gets a
-- chance to consume later breaks under the environment published by the
-- completed prefix.
lineBreakFallback :: Expression -> Maybe Expression
lineBreakFallback source = case break (== LineBreak)
    (rawApplicationPhrase source) of
  (before, LineBreak : after)
    | not (null before) && not (null after) ->
        Just
          ( unresolvedApplicationFrom before
              <:> unresolvedApplicationFrom after
          )
  _ -> Nothing

-- Give each ordinary argument boundary, from left to right, the opportunity
-- to begin declared syntax. The rebuilt suffix enters normal child traversal,
-- where the declaration selects and expands its own extent.
applicationFallback
  :: (Expression -> Bool)
  -> Expression
  -> Maybe Expression
applicationFallback hasDeclaredCandidate source = case source of
  UnresolvedApplication phrase@(_ : _ : _) -> Just (foldPhrase phrase)
  _ -> Nothing
  where
    foldPhrase (first : remaining) = foldRemaining first remaining
    foldPhrase [] = AtlasMap []
    foldRemaining function [] = function
    foldRemaining function remaining@(argument : later)
      | hasDeclaredCandidate suffix =
          FunctionApplication function suffix
      | otherwise =
          foldRemaining (FunctionApplication function argument) later
      where
        suffix = unresolvedApplicationFrom remaining
