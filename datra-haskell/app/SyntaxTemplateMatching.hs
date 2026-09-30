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
  , matchSyntaxTemplates
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationDecision (..))
import Data.Foldable (traverse_)
import DatraLanguage.AST
  ( Expression (..) )
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

type HoleMatches = SyntaxHoleKind String -> Expression -> Bool

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
    (SyntaxTemplateFederation rules) expressionValue = do
  let phrase = applicationPhrase expressionValue
      applicable = filter (prefixMatches phrase) rules
      successful =
        [ SuccessfulMatch rule captures remaining
        | rule <- applicable
        , consumed <- reverse
            [minimumRequiredValues (rulePieces rule) .. length phrase]
        , let (candidate, remaining) = splitAt consumed phrase
        , captures <- matchPieces holeMatches (rulePieces rule) candidate
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
    matchesLiteral literal = (== literal) . renderSourceExpression

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
    renderPiece (SyntaxHole ExpressionSyntaxHole) = "$_Expr"
    renderPiece (SyntaxHole BlockSyntaxHole) = "$_Block"
    renderPiece (SyntaxHole IdentifierExpressionSyntaxHole) = "$_IdenExp"
    renderPiece (SyntaxHole (ValueSyntaxHole kind)) = '$' : kind

rulePieces :: SyntaxRule -> [SyntaxPiece String]
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
  :: HoleMatches
  -> [SyntaxPiece String]
  -> [Expression]
  -> [[Expression]]
matchPieces _ [] [] = [[]]
matchPieces _ [] _ = []
matchPieces holeMatches (SyntaxLiteral literal : pieces) (value : values)
  | renderSourceExpression value == literal =
      matchPieces holeMatches pieces values
matchPieces _ (SyntaxLiteral _ : _) _ = []
matchPieces holeMatches (SyntaxHole kind : pieces) values =
  [ capture : captures
  | count <- reverse [1 .. maximumCaptureLength pieces values]
  , let (captured, remaining) = splitAt count values
  , let capture = applicationFrom captured
  , holeMatches kind capture
  , captures <- matchPieces holeMatches pieces remaining
  ]

maximumCaptureLength :: [SyntaxPiece String] -> [Expression] -> Int
maximumCaptureLength remaining values =
  max 0 (length values - minimumRequiredValues remaining)

minimumRequiredValues :: [SyntaxPiece String] -> Int
minimumRequiredValues = length

applicationFrom :: [Expression] -> Expression
applicationFrom [] = AtlasMap []
applicationFrom (first : remaining) =
  foldl FunctionApplication first remaining
