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
  , invalidSyntaxTemplateCharacter
  , isSymbolicSyntaxCharacter
  ) where

import Data.Maybe (listToMaybe)
import DatraLanguage.Identifier
  ( isAsciiCharacter
  , isIdentifierCharacter
  )

data SyntaxHoleKind value
  = ExpressionSyntaxHole value
  | BlockSyntaxHole value
  | IdentifierExpressionSyntaxHole value
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

    hole "_Expr" = SyntaxHole (ExpressionSyntaxHole (valueReference "_Expr"))
    hole "_Block" = SyntaxHole (BlockSyntaxHole (valueReference "_Block"))
    hole "_IdenExp" =
      SyntaxHole (IdentifierExpressionSyntaxHole (valueReference "_IdenExp"))
    hole kind = SyntaxHole (ValueSyntaxHole (valueReference kind))

-- | Return the first literal character that the neutral source parser cannot
-- retain as part of a declared syntax phrase. This validation is intentionally
-- separate from 'parseSyntaxTemplate': template strings remain ordinary valid
-- values until a syntax type operator asks to install one as surface syntax.
invalidSyntaxTemplateCharacter :: SyntaxTemplate value -> Maybe Char
invalidSyntaxTemplateCharacter (SyntaxTemplate pieces) = listToMaybe
  [ character
  | SyntaxLiteral literal <- pieces
  , character <- literal
  , not
      (isIdentifierCharacter character
        || isSymbolicSyntaxCharacter character)
  ]

isSymbolicSyntaxCharacter :: Char -> Bool
isSymbolicSyntaxCharacter character =
  isAsciiCharacter character
    && not (isIdentifierCharacter character)
    -- These characters are structural delimiters, string/comment introducers,
    -- or escapes in source. The neutral reader cannot preserve them as an
    -- opaque symbolic literal for the later declared-syntax pass.
    && character `notElem` (" \t\r\n(){}[];,.\"#$\\" :: String)

traverseSyntaxTemplate
  :: Applicative f
  => (source -> f target)
  -> SyntaxTemplate source
  -> f (SyntaxTemplate target)
traverseSyntaxTemplate transform (SyntaxTemplate pieces) =
  SyntaxTemplate <$> traverse traversePiece pieces
  where
    traversePiece (SyntaxLiteral literal) = pure (SyntaxLiteral literal)
    traversePiece (SyntaxHole (ExpressionSyntaxHole value)) =
      SyntaxHole . ExpressionSyntaxHole <$> transform value
    traversePiece (SyntaxHole (BlockSyntaxHole value)) =
      SyntaxHole . BlockSyntaxHole <$> transform value
    traversePiece (SyntaxHole (IdentifierExpressionSyntaxHole value)) =
      SyntaxHole . IdentifierExpressionSyntaxHole <$> transform value
    traversePiece (SyntaxHole (ValueSyntaxHole value)) =
      SyntaxHole . ValueSyntaxHole <$> transform value

renderSyntaxTemplate :: (value -> String) -> SyntaxTemplate value -> String
renderSyntaxTemplate renderValue (SyntaxTemplate pieces) =
  unwords (map renderPiece pieces)
  where
    renderPiece (SyntaxLiteral literal) = literal
    renderPiece (SyntaxHole ExpressionSyntaxHole {}) = "$_Expr"
    renderPiece (SyntaxHole BlockSyntaxHole {}) = "$_Block"
    renderPiece (SyntaxHole IdentifierExpressionSyntaxHole {}) = "$_IdenExp"
    renderPiece (SyntaxHole (ValueSyntaxHole value)) = '$' : renderValue value
