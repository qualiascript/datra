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
  , TemplateSelection (..)
  , templateSelectionProjection
  , literalSyntaxTemplate
  , traverseSyntaxTemplate
  , renderSyntaxTemplate
  ) where

data SyntaxHoleKind value
  = ExpressionSyntaxHole value
  | BlockSyntaxHole value
  | FunctionBodySyntaxHole value
  | DeclarationSyntaxHole value
  | DependentIdentifierSyntaxHole value
  | ValueSyntaxHole value
  deriving (Eq, Show)

syntaxHoleValue :: SyntaxHoleKind value -> value
syntaxHoleValue (ExpressionSyntaxHole value) = value
syntaxHoleValue (BlockSyntaxHole value) = value
syntaxHoleValue (FunctionBodySyntaxHole value) = value
syntaxHoleValue (DeclarationSyntaxHole value) = value
syntaxHoleValue (DependentIdentifierSyntaxHole value) = value
syntaxHoleValue (ValueSyntaxHole value) = value

mapSyntaxHoleKind
  :: (source -> target)
  -> SyntaxHoleKind source
  -> SyntaxHoleKind target
mapSyntaxHoleKind transform kind = case kind of
  ExpressionSyntaxHole value -> ExpressionSyntaxHole (transform value)
  BlockSyntaxHole value -> BlockSyntaxHole (transform value)
  FunctionBodySyntaxHole value -> FunctionBodySyntaxHole (transform value)
  DeclarationSyntaxHole value -> DeclarationSyntaxHole (transform value)
  DependentIdentifierSyntaxHole value ->
    DependentIdentifierSyntaxHole (transform value)
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

-- | The evidence retained by any successful dependent presentation match.
-- Position zero is the complete presented value; the remaining positions are
-- the payload selected by its interpolation holes.
data TemplateSelection whole capture = TemplateSelection
  { templateSelectionWhole :: whole
  , templateSelectionCaptures :: [capture]
  } deriving (Eq, Show)

templateSelectionProjection :: TemplateSelection value value -> [value]
templateSelectionProjection selection =
  templateSelectionWhole selection : templateSelectionCaptures selection

-- | Split one literal chunk into the whitespace-delimited pieces consumed by
-- declared-syntax matching. Holes are represented by source string
-- interpolation nodes and are therefore compiled separately from literal
-- text; in particular, an escaped percent sign can never become a hole here.
literalSyntaxTemplate :: String -> SyntaxTemplate value
literalSyntaxTemplate = SyntaxTemplate . map SyntaxLiteral . words

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
    traversePiece (SyntaxHole (FunctionBodySyntaxHole value)) =
      SyntaxHole . FunctionBodySyntaxHole <$> transform value
    traversePiece (SyntaxHole (DeclarationSyntaxHole value)) =
      SyntaxHole . DeclarationSyntaxHole <$> transform value
    traversePiece (SyntaxHole (DependentIdentifierSyntaxHole value)) =
      SyntaxHole . DependentIdentifierSyntaxHole <$> transform value
    traversePiece (SyntaxHole (ValueSyntaxHole value)) =
      SyntaxHole . ValueSyntaxHole <$> transform value

renderSyntaxTemplate :: (value -> String) -> SyntaxTemplate value -> String
renderSyntaxTemplate renderValue (SyntaxTemplate pieces) =
  unwords (map renderPiece pieces)
  where
    renderPiece (SyntaxLiteral literal) = literal
    renderPiece (SyntaxHole ExpressionSyntaxHole {}) = "%_Expr"
    renderPiece (SyntaxHole BlockSyntaxHole {}) = "%_Block"
    renderPiece (SyntaxHole FunctionBodySyntaxHole {}) = "%_FunctionBody"
    renderPiece (SyntaxHole DeclarationSyntaxHole {}) =
      "%_DependentDeclaration"
    renderPiece (SyntaxHole DependentIdentifierSyntaxHole {}) =
      "%_DependentIdentifier"
    renderPiece (SyntaxHole (ValueSyntaxHole value)) = '%' : renderValue value
