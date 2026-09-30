-- | Match declared syntax templates against an already parsed AST.
--
-- Matching is deliberately independent of source layout.  The input is an
-- application AST, literals are compared by canonical source spelling, and
-- holes receive reconstructed AST subexpressions.  A caller supplies the
-- membership decision for each hole so value holes can use Datra's ordinary
-- string-template/value matching rather than a second parser-side type system.
module SyntaxTemplateMatching
  ( SyntaxTemplateMatchFailure (..)
  , canonicalSyntaxTemplate
  , matchSyntaxTemplates
  ) where

import Data.List (nubBy)
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
  )
import DatraLanguage.Diagnostics.Application
  ( SyntaxExpansionFailure )

data SyntaxTemplateMatchFailure
  = NotSyntaxApplication
  | NoMatchingSyntaxTemplate
  | SyntaxTemplateExpansionFailure SyntaxExpansionFailure
  deriving (Eq, Show)

type HoleMatches = SyntaxHoleKind -> Expression -> Bool

data SuccessfulMatch = SuccessfulMatch
  { successfulRule :: SyntaxRule
  , successfulCaptures :: [Expression]
  , successfulConsumed :: Int
  , successfulRemaining :: [Expression]
  }

-- | Match within one application spine. Its explicit head identifier first
-- selects one binding, so only rules attached to that name participate. Rules
-- try the longest prefix available inside that context; holes likewise try
-- their longest available sequence and backtrack when membership or the
-- remaining pieces fail. Unconsumed arguments are reapplied to the rewritten
-- prefix. Matching never descends through another AST node to enlarge the
-- context. More than one distinct match consuming the same longest prefix
-- violates the declaration federation's disjointness invariant.
matchSyntaxTemplates
  :: HoleMatches
  -> [SyntaxRule]
  -> Expression
  -> Either SyntaxTemplateMatchFailure Expression
matchSyntaxTemplates holeMatches rules expressionValue = do
  (name, arguments) <- maybe (Left NotSyntaxApplication) Right
    (applicationPhrase expressionValue)
  let applicable = filter ((== name) . syntaxName) rules
      successful =
        [ SuccessfulMatch rule captures consumed remaining
        | rule <- applicable
        , consumed <- reverse
            [minimumRequiredValues (rulePieces rule) .. length arguments]
        , let (candidate, remaining) = splitAt consumed arguments
        , captures <- matchPieces holeMatches (rulePieces rule) candidate
        ]
  matched <- chooseSuccessful successful
  expanded <- either
    (Left . SyntaxTemplateExpansionFailure)
    Right
    (expandSyntax (successfulRule matched) (successfulCaptures matched))
  pure (foldl FunctionApplication expanded (successfulRemaining matched))

chooseSuccessful
  :: [SuccessfulMatch]
  -> Either SyntaxTemplateMatchFailure SuccessfulMatch
chooseSuccessful [] = Left NoMatchingSyntaxTemplate
chooseSuccessful matches =
  case distinctLongest of
    [matched] -> Right matched
    ambiguous -> error
      ("internal error: syntax template federation admitted overlapping "
        <> "branches: "
        <> show
          (map (canonicalSyntaxTemplate . successfulRule) ambiguous))
  where
    longest = maximum (map successfulConsumed matches)
    distinctLongest = nubBy
      (\left right ->
        successfulRule left == successfulRule right
          && successfulCaptures left == successfulCaptures right)
      (filter ((== longest) . successfulConsumed) matches)

canonicalSyntaxTemplate :: SyntaxRule -> String
canonicalSyntaxTemplate rule = unwords
  (syntaxName rule : map renderPiece (rulePieces rule))
  where
    renderPiece (SyntaxLiteral literal) = literal
    renderPiece (SyntaxHole ExpressionSyntaxHole) = "$_Expr"
    renderPiece (SyntaxHole BlockSyntaxHole) = "$_Block"
    renderPiece (SyntaxHole IdentifierExpressionSyntaxHole) = "$_IdenExp"
    renderPiece (SyntaxHole (ValueSyntaxHole kind)) = '$' : kind

rulePieces :: SyntaxRule -> [SyntaxPiece]
rulePieces = syntaxTemplatePieces . syntaxTemplate

applicationPhrase :: Expression -> Maybe (String, [Expression])
applicationPhrase expressionValue =
  case applicationSpine expressionValue of
    (IdentifierReference (IdentifierString name), arguments) ->
      Just (name, arguments)
    _ -> Nothing

applicationSpine :: Expression -> (Expression, [Expression])
applicationSpine = go []
  where
    go arguments (FunctionApplication function argument) =
      go (argument : arguments) function
    go arguments function = (function, arguments)

matchPieces
  :: HoleMatches
  -> [SyntaxPiece]
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

maximumCaptureLength :: [SyntaxPiece] -> [Expression] -> Int
maximumCaptureLength remaining values =
  max 0 (length values - minimumRequiredValues remaining)

minimumRequiredValues :: [SyntaxPiece] -> Int
minimumRequiredValues = length

applicationFrom :: [Expression] -> Expression
applicationFrom [] = AtlasMap []
applicationFrom (first : remaining) =
  foldl FunctionApplication first remaining
