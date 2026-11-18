-- | Mode-specific declarative matching over an already parsed AST. Each
-- matcher owns its candidate projection; only typed capture validation is
-- shared after a match has been produced.
module StringInterpolation.Matching
  ( ExpressionParser (..)
  , StringInterpolationMatchFailure (..)
  , SyntaxMatch (..)
  , DeclarativeMatch (..)
  , enumerateSyntaxRulesSelections
  , enumerateSyntaxRuleSelections
  , matchSyntaxRule
  , matchSyntaxRules
  , matchSyntaxRulesWith
  , expandSyntaxMatch
  ) where

import Data.Functor.Identity (runIdentity)
import DatraLanguage.Application
  ( applicationFrom
  , applicationSelections
  , rawApplicationPhrase
  )
import DatraLanguage.AST
  ( Expression (..)
  , LiteralTemplateLiteral (..)
  , SymbolLiteral (..)
  )
import DatraLanguage.AST.Source (renderSourceExpression)
import StringInterpolation
  ( DeclarativeMatcherPlan (..)
  , DeclarativeCapture (..)
  , LiteralTemplatePattern (..)
  , LiteralTemplatePatternPart (..)
  , IdentifierApplicationPattern (..)
  , LiteralExpressionPattern (..)
  , LiteralExpressionPatternPart (..)
  , StringExpression (..)
  , SyntaxRule (..)
  , TemplateSelection (..)
  , expandSyntax
  )
import StringInterpolation.Exact (matchExactSegments)

newtype ExpressionParser = ExpressionParser
  { parseExpressionText :: String -> Maybe Expression
  }

data StringInterpolationMatchFailure
  = NoMatchingStringInterpolation
  deriving (Eq, Show)

type HoleMatches = DeclarativeCapture -> Expression -> Bool
type CaptureHole =
  [(DeclarativeCapture, Expression)]
  -> DeclarativeCapture
  -> Expression
  -> Maybe Expression

data SyntaxMatch = SyntaxMatch
  { syntaxMatchRule :: SyntaxRule
  , syntaxMatchSelection :: TemplateSelection Expression Expression
  , syntaxMatchRemaining :: [Expression]
  }

-- | The common result produced only after one concrete matcher mode succeeds.
-- Capture membership and generic inference have not yet run.
data DeclarativeMatch = DeclarativeMatch
  { declarativeMatchRule :: SyntaxRule
  , declarativeMatchSelection
      :: TemplateSelection Expression Expression
  , declarativeMatchCaptures
      :: [(DeclarativeCapture, Expression)]
  , declarativeMatchRemaining :: [Expression]
  }

enumerateSyntaxRuleSelections
  :: ExpressionParser
  -> SyntaxRule
  -> Expression
  -> [DeclarativeMatch]
enumerateSyntaxRuleSelections parser rule =
  enumerateSyntaxRulesSelections parser [rule]

enumerateSyntaxRulesSelections
  :: ExpressionParser
  -> [SyntaxRule]
  -> Expression
  -> [DeclarativeMatch]
enumerateSyntaxRulesSelections parser rules expressionValue =
  concatMap matchesRule rules
  where
    matchesRule rule = case declarativeMatcherPlan rule of
      IdentifierApplicationMatcher patternValue ->
        matchIdentifierApplication rule patternValue expressionValue
      LiteralTemplateMatcher patternValue ->
        matchLiteralTemplate rule patternValue expressionValue
      LiteralExpressionMatcher patternValue ->
        matchLiteralExpression parser rule patternValue expressionValue

matchIdentifierApplication
  :: SyntaxRule
  -> IdentifierApplicationPattern
  -> Expression
  -> [DeclarativeMatch]
matchIdentifierApplication rule patternValue expressionValue =
  [ DeclarativeMatch rule
      (TemplateSelection selected [captured])
      [ ( StringExpressionCapture
            (identifierApplicationOperand patternValue)
        , captured
        )
      ]
      remaining
  | (selected, remaining) <- applicationSelections expressionValue
  , actualHead : operands <- [rawApplicationPhrase selected]
  , not (null operands)
  , LineBreak `notElem` operands
  , actualHead == identifierApplicationHead patternValue
  , let captured = applicationFrom operands
  ]

matchLiteralTemplate
  :: SyntaxRule
  -> LiteralTemplatePattern
  -> Expression
  -> [DeclarativeMatch]
matchLiteralTemplate rule patternValue expressionValue =
  [ declarativeMatch rule selected captures remaining
  | (selected, remaining) <- applicationSelections expressionValue
  , captures <- literalTemplateCaptures patternValue
      (rawApplicationPhrase selected)
  ]

matchLiteralExpression
  :: ExpressionParser
  -> SyntaxRule
  -> LiteralExpressionPattern (StringExpression Expression)
  -> Expression
  -> [DeclarativeMatch]
matchLiteralExpression parser rule patternValue expressionValue =
  [ declarativeMatch rule selected captures remaining
  | (selected, remaining) <- applicationSelections expressionValue
  , captures <- literalExpressionCaptures parser patternValue selected
  ]

declarativeMatch
  :: SyntaxRule
  -> Expression
  -> [(DeclarativeCapture, Expression)]
  -> [Expression]
  -> DeclarativeMatch
declarativeMatch rule selected captures remaining = DeclarativeMatch rule
  (TemplateSelection selected (map snd captures)) captures remaining

literalTemplateCaptures
  :: LiteralTemplatePattern
  -> [Expression]
  -> [[(DeclarativeCapture, Expression)]]
literalTemplateCaptures (LiteralTemplatePattern parts) = match parts
  where
    match [] [] = [[]]
    match [] _ = []
    match (LiteralTemplatePatternLiteral expected : remaining) candidates =
      [ later
      | let (_, afterLineBreaks) = span (== LineBreak) candidates
      , actual : rest <- [afterLineBreaks]
      , literalMatches expected actual
      , later <- match remaining rest
      ]
    match (LiteralTemplatePatternCapture target : remaining) candidates =
      [ (LiteralTemplateCapture target, applicationFrom selected) : later
      | let (_, afterLineBreaks) = span (== LineBreak) candidates
      , (selected, rest) <- captureSelections afterLineBreaks
      , later <- match remaining rest
      ]

    literalMatches literal actual = case (literal, actual) of
      (IdentifierTemplateLiteral expected, IdentifierReference actualName) ->
        expected == actualName
      (SymbolTemplateLiteral (SymbolLiteral expected),
          UnresolvedSyntaxLiteral actualSymbol) ->
        expected == actualSymbol
      _ -> False

    captureSelections candidates =
      [ splitAt count candidates
      | count <- reverse [1 .. length candidates]
      , candidates !! (count - 1) /= LineBreak
      ]

literalExpressionCaptures
  :: ExpressionParser
  -> LiteralExpressionPattern (StringExpression Expression)
  -> Expression
  -> [[(DeclarativeCapture, Expression)]]
literalExpressionCaptures parser (LiteralExpressionPattern parts) source =
  [ zip (map StringExpressionCapture captureKinds) selected
  | selected <- runIdentity
      (matchExactSegments view decode parts (renderSourceExpression source))
  ]
  where
    captureKinds =
      [ kind
      | LiteralExpressionPatternCapture kind <- parts
      ]
    view partValue = case partValue of
      LiteralExpressionPatternLiteral literal -> Right literal
      LiteralExpressionPatternCapture capture -> Left capture
    decode = decodeCapture parser

decodeCapture
  :: Applicative f
  => ExpressionParser
  -> StringExpression Expression
  -> String
  -> f [Expression]
decodeCapture parser kind captured = pure (captureExpressions kind captured)
  where
    captureExpressions selectedKind sourceText = case selectedKind of
      LiteralString {} -> []
      StringLiteralString {} -> [AsciiStringLiteral sourceText]
      ExpressionString {} -> parsed
      BlockString {} -> parsed
      FunctionBodyString {} -> parsed
      DeclarationString {} -> parsed
      DependentArgumentString {} -> parsed
      IdentifierExpressionString {} -> parsed
      -- An unevaluated value descriptor has not acquired its canonical-string
      -- codec yet. Retain both candidates until ordinary typed selection
      -- specializes or rejects them.
      ValueString {} -> parsed <> [AsciiStringLiteral sourceText]
      where
        parsed = case parseExpressionText parser sourceText of
          Just expressionValue -> [expressionValue]
          Nothing -> []

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
  :: ExpressionParser
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
  :: ExpressionParser
  -> CaptureHole
  -> [SyntaxRule]
  -> Expression
  -> Either StringInterpolationMatchFailure Expression
matchSyntaxRulesWith parser captureHole rules expressionValue =
  expandSyntaxMatch <$> chooseSuccessful
    [ SyntaxMatch
        (declarativeMatchRule matched)
        ((declarativeMatchSelection matched)
          { templateSelectionCaptures = map snd captures })
        (declarativeMatchRemaining matched)
    | matched <- enumerateSyntaxRulesSelections parser rules expressionValue
    , captures <- maybeToList
        (validateCaptures captureHole
          (declarativeMatchCaptures matched))
    ]

validateCaptures
  :: CaptureHole
  -> [(DeclarativeCapture, Expression)]
  -> Maybe [(DeclarativeCapture, Expression)]
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
  :: ExpressionParser
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
