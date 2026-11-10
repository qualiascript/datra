-- | Match declared string interpolations against an already parsed AST.
--
-- Matching is deliberately independent of source layout. The input template
-- and source have both been lowered by the neutral parser, so core operators
-- are matched as AST constructors. Holes receive selected AST subexpressions.
-- A caller supplies the
-- membership decision for each hole so value holes can use Datra's ordinary
-- string-template/value matching rather than a second parser-side type system.
module StringInterpolation.Matching
  ( StringInterpolationMatchFailure (..)
  , SyntaxMatch (..)
  , StructuralSyntaxMatch (..)
  , enumerateSyntaxRulesSelections
  , enumerateSyntaxRuleSelections
  , matchSyntaxRule
  , matchSyntaxRules
  , matchSyntaxRulesWith
  , expandSyntaxMatch
  ) where

import DatraLanguage.AST (Expression (FunctionApplication))
import StringInterpolation
  ( StringExpression (..)
  , SyntaxRule (..)
  , TemplateSelection (..)
  , expandSyntax
  )
import StringInterpolation.Projection
  ( StringInterpolationParser
  , applicationFrom
  , applicationPhrase
  , structuralTemplateCaptures
  )
data StringInterpolationMatchFailure
  = NoMatchingStringInterpolation
  deriving (Eq, Show)

type HoleMatches = StringExpression Expression -> Expression -> Bool
type CaptureHole =
  [(StringExpression Expression, Expression)]
  -> StringExpression Expression
  -> Expression
  -> Maybe Expression

data SyntaxMatch = SyntaxMatch
  { syntaxMatchRule :: SyntaxRule
  , syntaxMatchSelection :: TemplateSelection Expression Expression
  , syntaxMatchRemaining :: [Expression]
  }

-- | A template match whose holes have only been partitioned structurally.
-- No capture membership, evaluation, or generic inference has occurred.
-- Keeping this distinct from 'SyntaxMatch' lets the rewrite scheduler retain
-- every greedy choice point and type its children incrementally.
data StructuralSyntaxMatch = StructuralSyntaxMatch
  { structuralSyntaxMatchRule :: SyntaxRule
  , structuralSyntaxMatchSelection
      :: TemplateSelection Expression Expression
  , structuralSyntaxMatchCaptures
      :: [(StringExpression Expression, Expression)]
  , structuralSyntaxMatchRemaining :: [Expression]
  }

enumerateSyntaxRuleSelections
  :: StringInterpolationParser
  -> SyntaxRule
  -> Expression
  -> [StructuralSyntaxMatch]
enumerateSyntaxRuleSelections parser rule =
  enumerateSyntaxRulesSelections parser [rule]

enumerateSyntaxRulesSelections
  :: StringInterpolationParser
  -> [SyntaxRule]
  -> Expression
  -> [StructuralSyntaxMatch]
enumerateSyntaxRulesSelections parser rules expressionValue =
  [ StructuralSyntaxMatch rule
      (TemplateSelection
        (applicationFrom candidate)
        (map snd captures))
      captures
      remaining
  | rule <- rules
  , consumed <- reverse [1 .. length phrase]
  , let (candidate, remaining) = splitAt consumed phrase
        selected = applicationFrom candidate
  , captures <- structuralTemplateCaptures parser
      (stringInterpolationTemplate rule) selected
  ]
  where
    phrase = applicationPhrase expressionValue

-- | Match within one application spine. Its explicit head identifier first
-- filters templates by their literal prefix. The selected template
-- still expands to its own binding, whose name may differ. Rules
-- are tried in declaration order. Within the first rule that fits, the rule
-- tries the longest prefix available inside that context; holes likewise try
-- their longest available sequence and backtrack when membership or the
-- remaining pieces fail. Unconsumed arguments are reapplied to the rewritten
-- prefix. Matching never descends through another AST node to enlarge the
-- context.
matchSyntaxRules
  :: StringInterpolationParser
  -> HoleMatches
  -> [SyntaxRule]
  -> Expression
  -> Either StringInterpolationMatchFailure Expression
matchSyntaxRules parser holeMatches rules expressionValue =
  matchSyntaxRulesWith parser
    (\_ kind value ->
      if holeMatches kind value then Just value else Nothing)
    rules expressionValue

matchSyntaxRulesWith
  :: StringInterpolationParser
  -> CaptureHole
  -> [SyntaxRule]
  -> Expression
  -> Either StringInterpolationMatchFailure Expression
matchSyntaxRulesWith parser captureHole rules expressionValue =
  expandSyntaxMatch <$> chooseSuccessful
    [ SyntaxMatch
        (structuralSyntaxMatchRule matched)
        ((structuralSyntaxMatchSelection matched)
          { templateSelectionCaptures = map snd captures })
        (structuralSyntaxMatchRemaining matched)
    | matched <- enumerateSyntaxRulesSelections parser rules expressionValue
    , captures <- maybeToList
        (validateCaptures captureHole
          (structuralSyntaxMatchCaptures matched))
    ]

validateCaptures
  :: CaptureHole
  -> [(StringExpression Expression, Expression)]
  -> Maybe [(StringExpression Expression, Expression)]
validateCaptures captureHole = go []
  where
    go selected [] = Just selected
    go selected ((kind, source) : remaining) = do
      captured <- captureHole selected kind source
      go (selected <> [(kind, captured)]) remaining

expandSyntaxMatch :: SyntaxMatch -> Expression
expandSyntaxMatch matched = foldl FunctionApplication expanded
  (syntaxMatchRemaining matched)
  where
    expanded = expandSyntax
      (syntaxMatchRule matched) (syntaxMatchSelection matched)

-- | Match one already admitted declaration. This is the parser integration
-- boundary: parsing establishes the contextual AST extent of a phrase, while
-- this matcher remains solely responsible for interpreting its template.
matchSyntaxRule
  :: StringInterpolationParser
  -> HoleMatches
  -> SyntaxRule
  -> Expression
  -> Either StringInterpolationMatchFailure Expression
matchSyntaxRule parser holeMatches rule =
  matchSyntaxRules parser holeMatches [rule]

chooseSuccessful
  :: [SyntaxMatch]
  -> Either StringInterpolationMatchFailure SyntaxMatch
chooseSuccessful [] = Left NoMatchingStringInterpolation
chooseSuccessful (matched : _) = Right matched

maybeToList :: Maybe value -> [value]
maybeToList Nothing = []
maybeToList (Just value) = [value]
