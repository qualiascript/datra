-- | Internal candidates which run after declarative syntax has had the first
-- opportunity to consume a complete source phrase.
module SyntaxRewriting.PostRewrite
  ( postRewriteCandidate
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

-- Split the complete raw application phrase at every unconsumed logical line
-- break. Each line remains an ordinary application; the lines form one flat
-- sequence. Empty lines are parser layout and therefore cannot reach here.
lineBreakFallback :: Expression -> Maybe Expression
lineBreakFallback source = case splitLineBreaks (rawApplicationPhrase source) of
  [_] -> Nothing
  linesOfSource
    | all (not . null) linesOfSource ->
        Just (foldl1 (<:>) (map applicationFrom linesOfSource))
    | otherwise -> Nothing

splitLineBreaks :: [Expression] -> [[Expression]]
splitLineBreaks = foldr split [[]]
  where
    split LineBreak linesOfSource = [] : linesOfSource
    split expressionValue (current : remaining) =
      (expressionValue : current) : remaining
    split _ [] = []
