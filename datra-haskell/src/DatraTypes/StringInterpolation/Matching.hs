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
  , applicationPhrase
  , applicationSelections
  , nativeApplicationPhrase
  )
import DatraLanguage.AST
  ( Expression (AsciiStringLiteral, FunctionApplication) )
import DatraLanguage.AST.Source (renderSourceExpression)
import StringInterpolation
  ( DeclarativeMatcherPlan (..)
  , NativeApplicationPattern (..)
  , ExactPresentationPattern (..)
  , ExactPresentationPart (..)
  , AtlasSyntaxPattern (..)
  , AtlasSyntaxPart (..)
  , StringExpression (..)
  , SyntaxRule (..)
  , TemplateSelection (..)
  , expandSyntax
  , horizontallySeparatedApplication
  , lineSeparatedApplication
  )
import StringInterpolation.Exact (matchExactSegments)

newtype ExpressionParser = ExpressionParser
  { parseExpressionText :: String -> Maybe Expression
  }

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

-- | The common result produced only after one concrete matcher mode succeeds.
-- Capture membership and generic inference have not yet run.
data DeclarativeMatch = DeclarativeMatch
  { declarativeMatchRule :: SyntaxRule
  , declarativeMatchSelection
      :: TemplateSelection Expression Expression
  , declarativeMatchCaptures
      :: [(StringExpression Expression, Expression)]
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
      NativeApplicationMatcher patternValue ->
        matchNativeApplication rule patternValue expressionValue
      AtlasSyntaxMatcher patternValue ->
        matchAtlasSyntax rule patternValue expressionValue
      ExactPresentationMatcher patternValue ->
        matchExactPresentation parser rule patternValue expressionValue
      LineSequenceMatcher -> matchLineSequence rule expressionValue
      HorizontalApplicationMatcher ->
        matchHorizontalApplication rule expressionValue

matchNativeApplication
  :: SyntaxRule
  -> NativeApplicationPattern
  -> Expression
  -> [DeclarativeMatch]
matchNativeApplication rule patternValue expressionValue =
  [ DeclarativeMatch rule
      (TemplateSelection selected [captured])
      [(nativeApplicationOperand patternValue, captured)]
      remaining
  | (selected, remaining) <- applicationSelections expressionValue
  , Just (actualHead : operands) <- [nativeApplicationPhrase selected]
  , not (null operands)
  , actualHead == nativeApplicationHead patternValue
  , let captured = applicationFrom operands
  ]

matchAtlasSyntax
  :: SyntaxRule
  -> AtlasSyntaxPattern
  -> Expression
  -> [DeclarativeMatch]
matchAtlasSyntax rule patternValue expressionValue =
  [ declarativeMatch rule selected captures remaining
  | (selected, remaining) <- applicationSelections expressionValue
  , captures <- atlasSyntaxCaptures patternValue
      (applicationPhrase selected)
  ]

matchExactPresentation
  :: ExpressionParser
  -> SyntaxRule
  -> ExactPresentationPattern (StringExpression Expression)
  -> Expression
  -> [DeclarativeMatch]
matchExactPresentation parser rule patternValue expressionValue =
  [ declarativeMatch rule selected captures remaining
  | (selected, remaining) <- applicationSelections expressionValue
  , captures <- exactPresentationCaptures parser patternValue selected
  ]

matchLineSequence :: SyntaxRule -> Expression -> [DeclarativeMatch]
matchLineSequence rule expressionValue =
  [ DeclarativeMatch rule
      (TemplateSelection expressionValue []) [] []
  | Just _ <- [lineSeparatedApplication expressionValue]
  ]

matchHorizontalApplication :: SyntaxRule -> Expression -> [DeclarativeMatch]
matchHorizontalApplication rule expressionValue =
  [ DeclarativeMatch rule
      (TemplateSelection expressionValue []) [] []
  | Just _ <- [horizontallySeparatedApplication expressionValue]
  ]

declarativeMatch
  :: SyntaxRule
  -> Expression
  -> [(StringExpression Expression, Expression)]
  -> [Expression]
  -> DeclarativeMatch
declarativeMatch rule selected captures remaining = DeclarativeMatch rule
  (TemplateSelection selected (map snd captures)) captures remaining

atlasSyntaxCaptures
  :: AtlasSyntaxPattern
  -> [Expression]
  -> [[(StringExpression Expression, Expression)]]
atlasSyntaxCaptures (AtlasSyntaxPattern parts) = match parts
  where
    match [] [] = [[]]
    match [] _ = []
    match _ [] = []
    match (AtlasSyntaxLiteral expected : remaining)
        (actual : candidates)
      | expected == actual = match remaining candidates
      | otherwise = []
    match (AtlasSyntaxCapture capture : remaining) candidates =
      [ (capture, applicationFrom selected) : later
      | count <- reverse [1 .. length candidates]
      , let (selected, rest) = splitAt count candidates
      , later <- match remaining rest
      ]

exactPresentationCaptures
  :: ExpressionParser
  -> ExactPresentationPattern (StringExpression Expression)
  -> Expression
  -> [[(StringExpression Expression, Expression)]]
exactPresentationCaptures parser (ExactPresentationPattern parts) source =
  [ zip captureKinds selected
  | selected <- runIdentity
      (matchExactSegments view decode parts (renderSourceExpression source))
  ]
  where
    captureKinds =
      [ kind
      | ExactPresentationCapture kind <- parts
      ]
    view partValue = case partValue of
      ExactPresentationLiteral literal -> Right literal
      ExactPresentationCapture capture -> Left capture
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
