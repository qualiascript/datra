-- | Mode-specific declarative matching over an already parsed AST. Each
-- matcher owns its candidate projection; only typed capture validation is
-- shared after a match has been produced.
module StringInterpolation.Matching
  ( ExpressionParser (..)
  , SyntaxMatch (..)
  , DeclarativeMatch (..)
  , enumerateSyntaxRulesSelections
  , enumerateSyntaxRuleSelections
  ) where

import Data.Functor.Identity (runIdentity)
import DatraLanguage.Application
  ( applicationSelections
  , rawApplicationPhrase
  , unresolvedApplicationFrom
  )
import DatraLanguage.AST
  ( Expression (..) )
import DatraLanguage.AST.Source (renderSourceExpression)
import StringInterpolation
  ( DeclarativeMatcherPlan (..)
  , DeclarativeCapture (..)
  , IdentifierApplicationPattern (..)
  , LiteralExpressionPattern (..)
  , LiteralExpressionPatternPart (..)
  , StringExpression (..)
  , SyntaxRule (..)
  , TemplateSelection (..)
  )
import StringInterpolation.Exact (matchExactSegments)

newtype ExpressionParser = ExpressionParser
  { parseExpressionText :: String -> Maybe Expression
  }

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
  , let captured = unresolvedApplicationFrom operands
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
      ExpressionString {} -> parsed
      BlockString {} -> parsed
      FunctionBodyString {} -> parsed
      DeclarationString {} -> parsed
      DependentArgumentString {} -> parsed
      IdentifierExpressionString {} -> parsed
      ValueString {} -> parsed
      where
        parsed = case parseExpressionText parser sourceText of
          Just expressionValue -> [expressionValue]
          Nothing -> []
