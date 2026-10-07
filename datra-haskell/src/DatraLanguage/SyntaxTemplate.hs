-- | Structured syntax attached to a function type. The hole payload is
-- parameterized so the parsed form can carry identifier names while the
-- evaluated form carries the corresponding resolved Datra values.
module DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind (..)
  , syntaxHoleValue
  , mapSyntaxHoleKind
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  , FunctionSyntax (..)
  , literalSyntaxTemplate
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

syntaxHoleValue :: SyntaxHoleKind value -> value
syntaxHoleValue (ExpressionSyntaxHole value) = value
syntaxHoleValue (BlockSyntaxHole value) = value
syntaxHoleValue (IdentifierExpressionSyntaxHole value) = value
syntaxHoleValue (ValueSyntaxHole value) = value

mapSyntaxHoleKind
  :: (source -> target)
  -> SyntaxHoleKind source
  -> SyntaxHoleKind target
mapSyntaxHoleKind transform kind = case kind of
  ExpressionSyntaxHole value -> ExpressionSyntaxHole (transform value)
  BlockSyntaxHole value -> BlockSyntaxHole (transform value)
  IdentifierExpressionSyntaxHole value ->
    IdentifierExpressionSyntaxHole (transform value)
  ValueSyntaxHole value -> ValueSyntaxHole (transform value)

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

-- | Split one literal chunk into the whitespace-delimited pieces consumed by
-- declared-syntax matching. Holes are represented by source string
-- interpolation nodes and are therefore compiled separately from literal
-- text; in particular, an escaped percent sign can never become a hole here.
literalSyntaxTemplate :: String -> SyntaxTemplate value
literalSyntaxTemplate = SyntaxTemplate . map SyntaxLiteral . words

-- | Return the first literal character that the neutral source parser cannot
-- retain as part of a declared syntax phrase. This validation is intentionally
-- separate from 'literalSyntaxTemplate': template strings remain ordinary valid
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
    renderPiece (SyntaxHole ExpressionSyntaxHole {}) = "%_Expr"
    renderPiece (SyntaxHole BlockSyntaxHole {}) = "%_Block"
    renderPiece (SyntaxHole IdentifierExpressionSyntaxHole {}) = "%_IdenExp"
    renderPiece (SyntaxHole (ValueSyntaxHole value)) = '%' : renderValue value
