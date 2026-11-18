-- | Internal candidates which run after declarative syntax has had the first
-- opportunity to consume a complete source phrase.
module SyntaxRewriting.PostRewrite
  ( postRewriteCandidate
  , postRewriteExpansion
  ) where

import DatraLanguage.AST (Expression (..))
import DatraLanguage.AST.Syntax ((<:>))
import DatraLanguage.Application (applicationFrom, rawApplicationPhrase)
import StringExpression (TemplateSelection (..))
import StringInterpolation
  ( DeclarativeMatcherPlan (..)
  , LiteralExpressionPattern (..)
  , SyntaxRule (..)
  , SyntaxRuleSemantics (..)
  )
import SyntaxRewriting.Candidates (compileRewriteRule)
import SyntaxRewriting.Types (StructuralCandidate (..))

postRewriteCandidate :: Expression -> Maybe StructuralCandidate
postRewriteCandidate source = do
  expansion <- lineBreakFallback source
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
postRewriteExpansion :: Expression -> [Expression] -> Expression
postRewriteExpansion expansion remaining =
  maybe source id (lineBreakFallback source)
  where
    source = applicationFrom (expansion : remaining)

-- Split only the first unconsumed logical line break. The untouched tail is
-- re-entered as a fresh phrase, so syntax beginning on its first line gets a
-- chance to consume later breaks under the environment published by the
-- completed prefix.
lineBreakFallback :: Expression -> Maybe Expression
lineBreakFallback source = case break (== LineBreak)
    (rawApplicationPhrase source) of
  (before, LineBreak : after)
    | not (null before) && not (null after) ->
        Just (applicationFrom before <:> applicationFrom after)
  _ -> Nothing
