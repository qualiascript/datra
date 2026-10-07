-- | Match declared syntax templates against an already parsed AST.
--
-- Matching is deliberately independent of source layout.  The input is an
-- application AST, literals are compared by canonical source spelling, and
-- holes receive reconstructed AST subexpressions.  A caller supplies the
-- membership decision for each hole so value holes can use Datra's ordinary
-- string-template/value matching rather than a second parser-side type system.
module SyntaxTemplateMatching
  ( SyntaxTemplateMatchFailure (..)
  , SyntaxTemplateFederation
  , SyntaxTemplateFederationFailure (..)
  , compileSyntaxTemplateFederation
  , canonicalSyntaxTemplate
  , matchSyntaxRule
  , matchSyntaxRules
  , matchSyntaxRulesWith
  , matchSyntaxTemplates
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationDecision (..))
import Data.Foldable (traverse_)
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
  , expandSyntax
  , syntaxTemplateLiteralPrefix
  )
import DatraLanguage.Diagnostics.Application
  ( SyntaxExpansionFailure )

data SyntaxTemplateMatchFailure
  = NotSyntaxApplication
  | NoMatchingSyntaxTemplate
  | SyntaxTemplateExpansionFailure SyntaxExpansionFailure
  deriving (Eq, Show)

newtype SyntaxTemplateFederation = SyntaxTemplateFederation [SyntaxRule]

data SyntaxTemplateFederationFailure
  = OverlappingSyntaxTemplates String String
  | UndecidableSyntaxTemplates String String
  deriving (Eq, Show)

-- | Admit a template federation only after every pair which can share a
-- surface head has a proof of deterministic distinction. Distinct leading
-- literals are disjoint without consulting the decision procedure; a template
-- without a leading literal remains on the conservative fallback path.
compileSyntaxTemplateFederation
  :: (SyntaxRule
      -> SyntaxRule
      -> AtlasMapFederationDecision refutation uncertainty ())
  -> [SyntaxRule]
  -> Either SyntaxTemplateFederationFailure SyntaxTemplateFederation
compileSyntaxTemplateFederation decide rules = do
  traverse_ requireDistinct
    [ (left, right)
    | (position, left) <- zip [0 :: Int ..] rules
    , right <- drop (position + 1) rules
    , templatesCanCompete left right
    ]
  pure (SyntaxTemplateFederation rules)
  where
    requireDistinct (left, right) =
      case decide left right of
        AtlasMapFederationProved () -> Right ()
        AtlasMapFederationRefuted _ -> Left
          (OverlappingSyntaxTemplates
            (canonicalSyntaxTemplate left)
            (canonicalSyntaxTemplate right))
        AtlasMapFederationUndecidable _ -> Left
          (UndecidableSyntaxTemplates
            (canonicalSyntaxTemplate left)
            (canonicalSyntaxTemplate right))
    templatesCanCompete left right = and
      (zipWith (==)
        (syntaxTemplateLiteralPrefix left)
        (syntaxTemplateLiteralPrefix right))

type HoleMatches = SyntaxHoleKind Expression -> Expression -> Bool
type CaptureHole =
  [(SyntaxHoleKind Expression, Expression)]
  -> SyntaxHoleKind Expression
  -> Expression
  -> Maybe Expression

data SuccessfulMatch = SuccessfulMatch
  { successfulRule :: SyntaxRule
  , successfulCaptures :: [Expression]
  , successfulRemaining :: [Expression]
  }

-- | Match within one application spine. Its explicit head identifier first
-- filters templates by their literal prefix. The selected template
-- still expands to its own binding, whose name may differ. Rules
-- are tried in declaration order. Within the first rule that fits, the rule
-- tries the longest prefix available inside that context; holes likewise try
-- their longest available sequence and backtrack when membership or the
-- remaining pieces fail. Unconsumed arguments are reapplied to the rewritten
-- prefix. Matching never descends through another AST node to enlarge the
-- context.
matchSyntaxTemplates
  :: HoleMatches
  -> SyntaxTemplateFederation
  -> Expression
  -> Either SyntaxTemplateMatchFailure Expression
matchSyntaxTemplates holeMatches
    federation expressionValue =
  matchSyntaxTemplatesWith
    (\_ kind value ->
      if holeMatches kind value then Just value else Nothing)
    federation expressionValue

matchSyntaxTemplatesWith
  :: CaptureHole
  -> SyntaxTemplateFederation
  -> Expression
  -> Either SyntaxTemplateMatchFailure Expression
matchSyntaxTemplatesWith captureHole
    (SyntaxTemplateFederation rules) expressionValue = do
  let phrase = applicationPhrase expressionValue
      applicable = filter (prefixMatches phrase) rules
      successful =
        [ SuccessfulMatch rule captures remaining
        | rule <- applicable
        , consumed <- reverse
            [minimumRequiredValues (rulePieces rule) .. length phrase]
        , let (candidate, remaining) = splitAt consumed phrase
        , captures <- matchPieces captureHole [] (rulePieces rule) candidate
        ]
  matched <- chooseSuccessful successful
  expanded <- either
    (Left . SyntaxTemplateExpansionFailure)
    Right
    (expandSyntax (successfulRule matched) (successfulCaptures matched))
  pure (foldl FunctionApplication expanded (successfulRemaining matched))
  where
    prefixMatches phrase rule = and
      (zipWith matchesLiteral
        (syntaxTemplateLiteralPrefix rule)
        phrase)
      && length (syntaxTemplateLiteralPrefix rule) <= length phrase
    matchesLiteral = matchesLiteralExpression

-- | Match one already admitted declaration. This is the parser integration
-- boundary: parsing establishes the contextual AST extent of a phrase, while
-- this matcher remains solely responsible for interpreting its template.
matchSyntaxRule
  :: HoleMatches
  -> SyntaxRule
  -> Expression
  -> Either SyntaxTemplateMatchFailure Expression
matchSyntaxRule holeMatches rule =
  matchSyntaxTemplates holeMatches (SyntaxTemplateFederation [rule])

-- | Match declarations in their source order. Admission of overlapping
-- function templates belongs to function federation; this operation only
-- applies the already-visible ordered declarations to one parsed AST.
matchSyntaxRules
  :: HoleMatches
  -> [SyntaxRule]
  -> Expression
  -> Either SyntaxTemplateMatchFailure Expression
matchSyntaxRules holeMatches rules =
  matchSyntaxTemplates holeMatches (SyntaxTemplateFederation rules)

-- | Variant used by production post-AST rewriting. Besides deciding
-- membership, a hole may canonicalize the captured AST value. Literal value
-- holes use this to turn a matched identifier token such as @hard@ into the
-- corresponding string value before function application is constructed.
matchSyntaxRulesWith
  :: CaptureHole
  -> [SyntaxRule]
  -> Expression
  -> Either SyntaxTemplateMatchFailure Expression
matchSyntaxRulesWith captureHole rules =
  matchSyntaxTemplatesWith captureHole (SyntaxTemplateFederation rules)

chooseSuccessful
  :: [SuccessfulMatch]
  -> Either SyntaxTemplateMatchFailure SuccessfulMatch
chooseSuccessful [] = Left NoMatchingSyntaxTemplate
chooseSuccessful (matched : _) = Right matched

canonicalSyntaxTemplate :: SyntaxRule -> String
canonicalSyntaxTemplate rule = unwords
  (map renderPiece (rulePieces rule))
  where
    renderPiece (SyntaxLiteral literal) = literal
    renderPiece (SyntaxHole ExpressionSyntaxHole {}) = "%_Expr"
    renderPiece (SyntaxHole BlockSyntaxHole {}) = "%_Block"
    renderPiece (SyntaxHole IdentifierExpressionSyntaxHole {}) = "%_IdenExp"
    renderPiece (SyntaxHole (ValueSyntaxHole kind)) =
      case kind of
        IdentifierReference (IdentifierString name) -> '%' : name
        _ -> "%(" <> renderSourceExpression kind <> ")"

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

matchPieces
  :: CaptureHole
  -> [(SyntaxHoleKind Expression, Expression)]
  -> [SyntaxPiece Expression]
  -> [Expression]
  -> [[Expression]]
matchPieces _ _ [] [] = [[]]
matchPieces _ _ [] _ = []
matchPieces holeMatches capturedValues
    (SyntaxLiteral literal : pieces) (value : values)
  | matchesLiteralExpression literal value =
      matchPieces holeMatches capturedValues pieces values
matchPieces _ _ (SyntaxLiteral _ : _) _ = []
matchPieces holeMatches capturedValues (SyntaxHole kind : pieces) values =
  [ matchedCapture : captures
  | count <- reverse [1 .. maximumCaptureLength pieces values]
  , let (captured, remaining) = splitAt count values
  , let capture = applicationFrom captured
  , matchedCapture <- maybeToList
      (holeMatches capturedValues kind capture)
  , captures <- matchPieces holeMatches
      (capturedValues <> [(kind, matchedCapture)]) pieces remaining
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
