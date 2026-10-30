-- | Match declared syntax templates against an already parsed AST.
--
-- Matching is deliberately independent of source layout.  The input is an
-- application AST, literals are compared by canonical source spelling, and
-- holes receive reconstructed AST subexpressions.  A caller supplies the
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

import DatraLanguage.AST
  ( Expression (..)
  , IdentifierString (IdentifierString)
  )
import DatraLanguage.AST.Source (renderSourceExpression)
import SyntaxDefinitions
  ( SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxRule (..)
  , SyntaxTemplate (..)
  , TemplateSelection (..)
  , expandSyntax
  , syntaxTemplateLiteralPrefix
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
  | rule <- filter (prefixMatches phrase) rules
  , consumed <- reverse
      [minimumRequiredValues (rulePieces rule) .. length phrase]
  , let (candidate, remaining) = splitAt consumed phrase
  , captures <- matchPiecesStructurally (rulePieces rule) candidate
  ]
  where
    phrase = applicationPhrase expressionValue
    prefixMatches values rule = and
      (zipWith matchesLiteralExpression
        (syntaxTemplateLiteralPrefix rule)
        values)
      && length (syntaxTemplateLiteralPrefix rule) <= length values

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

rulePieces :: SyntaxRule -> [SyntaxPiece Expression]
rulePieces = syntaxTemplatePieces . syntaxTemplate

applicationPhrase :: Expression -> [Expression]
applicationPhrase expressionValue =
  case applicationSpine expressionValue of
    (headValue, arguments) -> headValue : arguments

applicationSpine :: Expression -> (Expression, [Expression])
applicationSpine = go []
  where
    go arguments (FunctionApplication function argument) =
      go (argument : arguments) function
    go arguments function = (function, arguments)

matchPiecesStructurally
  :: [SyntaxPiece Expression]
  -> [Expression]
  -> [[(SyntaxHoleKind Expression, Expression)]]
matchPiecesStructurally [] [] = [[]]
matchPiecesStructurally [] _ = []
matchPiecesStructurally
    (SyntaxLiteral literal : pieces) (value : values)
  | matchesLiteralExpression literal value =
      matchPiecesStructurally pieces values
matchPiecesStructurally (SyntaxLiteral _ : _) _ = []
matchPiecesStructurally (SyntaxHole kind : pieces) values =
  [ (kind, capture) : captures
  | count <- reverse [1 .. maximumCaptureLength pieces values]
  , let (captured, remaining) = splitAt count values
        capture = applicationFrom captured
  , captures <- matchPiecesStructurally pieces remaining
  ]

maybeToList :: Maybe value -> [value]
maybeToList Nothing = []
maybeToList (Just value) = [value]

maximumCaptureLength :: [SyntaxPiece Expression] -> [Expression] -> Int
maximumCaptureLength remaining values =
  max 0 (length values - minimumRequiredValues remaining)

minimumRequiredValues :: [SyntaxPiece Expression] -> Int
minimumRequiredValues = length

applicationFrom :: [Expression] -> Expression
applicationFrom [] = AtlasMap []
applicationFrom (first : remaining) =
  foldl FunctionApplication first remaining

matchesLiteralExpression :: String -> Expression -> Bool
matchesLiteralExpression literal expressionValue =
  case expressionValue of
    IdentifierReference (IdentifierString value) -> value == literal
    _ -> renderSourceExpression expressionValue == literal
