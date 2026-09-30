-- | Structured syntax attached to a function type. The hole payload is
-- parameterized so the parsed form can carry identifier names while the
-- evaluated form carries the corresponding resolved Datra values.
module DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  , FunctionSyntax (..)
  , parseSyntaxTemplate
  , traverseSyntaxTemplate
  , renderSyntaxTemplate
  ) where

import DatraLanguage.Identifier (isIdentifierCharacter)

data SyntaxHoleKind value
  = ExpressionSyntaxHole
  | BlockSyntaxHole
  | IdentifierExpressionSyntaxHole
  | ValueSyntaxHole value
  deriving (Eq, Show)

data SyntaxPiece value
  = SyntaxLiteral String
  | SyntaxHole (SyntaxHoleKind value)
  deriving (Eq, Show)

newtype SyntaxTemplate value = SyntaxTemplate
  { syntaxTemplatePieces :: [SyntaxPiece value]
  } deriving (Eq, Show)

newtype FunctionSyntax value = FunctionSyntax
  { functionSyntaxTemplates :: [SyntaxTemplate value]
  } deriving (Eq, Show)

parseSyntaxTemplate :: (String -> value) -> String -> SyntaxTemplate value
parseSyntaxTemplate valueReference =
  SyntaxTemplate . concatMap tokenPieces . words
  where
    tokenPieces [] = []
    tokenPieces ('$' : remaining)
      | not (null holeName) = hole holeName : tokenPieces suffix
      | otherwise = SyntaxLiteral "$" : tokenPieces remaining
      where
        (holeName, suffix) = span isIdentifierCharacter remaining
    tokenPieces token =
      let (literal, remaining) = break (== '$') token
      in SyntaxLiteral literal : tokenPieces remaining

    hole "_Expr" = SyntaxHole ExpressionSyntaxHole
    hole "_Block" = SyntaxHole BlockSyntaxHole
    hole "_IdenExp" = SyntaxHole IdentifierExpressionSyntaxHole
    hole kind = SyntaxHole (ValueSyntaxHole (valueReference kind))

traverseSyntaxTemplate
  :: Applicative f
  => (source -> f target)
  -> SyntaxTemplate source
  -> f (SyntaxTemplate target)
traverseSyntaxTemplate transform (SyntaxTemplate pieces) =
  SyntaxTemplate <$> traverse traversePiece pieces
  where
    traversePiece (SyntaxLiteral literal) = pure (SyntaxLiteral literal)
    traversePiece (SyntaxHole ExpressionSyntaxHole) =
      pure (SyntaxHole ExpressionSyntaxHole)
    traversePiece (SyntaxHole BlockSyntaxHole) =
      pure (SyntaxHole BlockSyntaxHole)
    traversePiece (SyntaxHole IdentifierExpressionSyntaxHole) =
      pure (SyntaxHole IdentifierExpressionSyntaxHole)
    traversePiece (SyntaxHole (ValueSyntaxHole value)) =
      SyntaxHole . ValueSyntaxHole <$> transform value

renderSyntaxTemplate :: (value -> String) -> SyntaxTemplate value -> String
renderSyntaxTemplate renderValue (SyntaxTemplate pieces) =
  unwords (map renderPiece pieces)
  where
    renderPiece (SyntaxLiteral literal) = literal
    renderPiece (SyntaxHole ExpressionSyntaxHole) = "$_Expr"
    renderPiece (SyntaxHole BlockSyntaxHole) = "$_Block"
    renderPiece (SyntaxHole IdentifierExpressionSyntaxHole) = "$_IdenExp"
    renderPiece (SyntaxHole (ValueSyntaxHole value)) = '$' : renderValue value
