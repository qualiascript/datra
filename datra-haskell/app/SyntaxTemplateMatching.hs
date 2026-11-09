-- | Match declared syntax templates against an already parsed AST.
--
-- Matching is deliberately independent of source layout. The input template
-- and source have both been lowered by the neutral parser, so core operators
-- are matched as AST constructors. Holes receive selected AST subexpressions.
-- A caller supplies the
-- membership decision for each hole so value holes can use Datra's ordinary
-- string-template/value matching rather than a second parser-side type system.
module SyntaxTemplateMatching
  ( SyntaxTemplateMatchFailure (..)
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
import SyntaxDefinitions
  ( SyntaxHoleKind (..)
  , SyntaxRule (..)
  , TemplateSelection (..)
  , expandSyntax
  )
import SyntaxTemplateProjection
  ( applicationFrom
  , applicationPhrase
  , structuralTemplateCaptures
  )
data SyntaxTemplateMatchFailure
  = NoMatchingSyntaxTemplate
  deriving (Eq, Show)

type HoleMatches = SyntaxHoleKind Expression -> Expression -> Bool
type CaptureHole =
  [(SyntaxHoleKind Expression, Expression)]
  -> SyntaxHoleKind Expression
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
      :: [(SyntaxHoleKind Expression, Expression)]
  , structuralSyntaxMatchRemaining :: [Expression]
  }

enumerateSyntaxRuleSelections
  :: SyntaxRule
  -> Expression
  -> [StructuralSyntaxMatch]
enumerateSyntaxRuleSelections rule = enumerateSyntaxRulesSelections [rule]

enumerateSyntaxRulesSelections
  :: [SyntaxRule]
  -> Expression
  -> [StructuralSyntaxMatch]
enumerateSyntaxRulesSelections rules expressionValue =
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
  , captures <- structuralTemplateCaptures
      (syntaxTemplate rule) selected
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
  :: HoleMatches
  -> [SyntaxRule]
  -> Expression
  -> Either SyntaxTemplateMatchFailure Expression
matchSyntaxRules holeMatches rules expressionValue =
  matchSyntaxRulesWith
    (\_ kind value ->
      if holeMatches kind value then Just value else Nothing)
    rules expressionValue

matchSyntaxRulesWith
  :: CaptureHole
  -> [SyntaxRule]
  -> Expression
  -> Either SyntaxTemplateMatchFailure Expression
matchSyntaxRulesWith captureHole rules expressionValue =
  expandSyntaxMatch <$> chooseSuccessful
    [ SyntaxMatch
        (structuralSyntaxMatchRule matched)
        ((structuralSyntaxMatchSelection matched)
          { templateSelectionCaptures = map snd captures })
        (structuralSyntaxMatchRemaining matched)
    | matched <- enumerateSyntaxRulesSelections rules expressionValue
    , captures <- maybeToList
        (validateCaptures captureHole
          (structuralSyntaxMatchCaptures matched))
    ]

validateCaptures
  :: CaptureHole
  -> [(SyntaxHoleKind Expression, Expression)]
  -> Maybe [(SyntaxHoleKind Expression, Expression)]
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
  :: HoleMatches
  -> SyntaxRule
  -> Expression
  -> Either SyntaxTemplateMatchFailure Expression
matchSyntaxRule holeMatches rule =
  matchSyntaxRules holeMatches [rule]

chooseSuccessful
  :: [SyntaxMatch]
  -> Either SyntaxTemplateMatchFailure SyntaxMatch
chooseSuccessful [] = Left NoMatchingSyntaxTemplate
chooseSuccessful (matched : _) = Right matched

maybeToList :: Maybe value -> [value]
maybeToList Nothing = []
maybeToList (Just value) = [value]
