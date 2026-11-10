-- | String-producing expressions used by declared syntax. A declaration is a
-- source-order concatenation of literal strings and typed string expressions.
module DatraLanguage.StringExpression
  ( StringExpression (..)
  , stringExpressionValue
  , mapStringExpression
  , StringTemplatePart (..)
  , StringInterpolationTemplate
  , FunctionSyntax (..)
  , TemplateSelection (..)
  , templateSelectionProjection
  , literalStringInterpolationTemplate
  , traverseStringInterpolationTemplate
  , renderStringInterpolationTemplate
  ) where

import DatraLanguage.StringTemplate (StringTemplatePart (..))

data StringExpression value
  = ExpressionString value
  | BlockString value
  | FunctionBodyString value
  | DeclarationString value
  | DependentArgumentString value
  | IdentifierExpressionString value
  | StringLiteralString value
  | ValueString value
  deriving (Eq, Show)

stringExpressionValue :: StringExpression value -> value
stringExpressionValue expression = case expression of
  ExpressionString value -> value
  BlockString value -> value
  FunctionBodyString value -> value
  DeclarationString value -> value
  DependentArgumentString value -> value
  IdentifierExpressionString value -> value
  StringLiteralString value -> value
  ValueString value -> value

mapStringExpression
  :: (source -> target)
  -> StringExpression source
  -> StringExpression target
mapStringExpression transform expression = case expression of
  ExpressionString value -> ExpressionString (transform value)
  BlockString value -> BlockString (transform value)
  FunctionBodyString value -> FunctionBodyString (transform value)
  DeclarationString value -> DeclarationString (transform value)
  DependentArgumentString value -> DependentArgumentString (transform value)
  IdentifierExpressionString value ->
    IdentifierExpressionString (transform value)
  StringLiteralString value -> StringLiteralString (transform value)
  ValueString value -> ValueString (transform value)

type StringInterpolationTemplate value =
  [StringTemplatePart (StringExpression value)]

newtype FunctionSyntax value = FunctionSyntax
  { functionStringInterpolationTemplates
      :: [StringInterpolationTemplate value]
  } deriving (Eq, Show)

-- | The evidence retained by any successful dependent presentation match.
-- Position zero is the complete presented value; the remaining positions are
-- the payload selected by its interpolation expressions.
data TemplateSelection whole capture = TemplateSelection
  { templateSelectionWhole :: whole
  , templateSelectionCaptures :: [capture]
  } deriving (Eq, Show)

templateSelectionProjection :: TemplateSelection value value -> [value]
templateSelectionProjection selection =
  templateSelectionWhole selection : templateSelectionCaptures selection

literalStringInterpolationTemplate :: String -> StringInterpolationTemplate value
literalStringInterpolationTemplate = map StringTemplateLiteral . words

traverseStringInterpolationTemplate
  :: Applicative f
  => (source -> f target)
  -> StringInterpolationTemplate source
  -> f (StringInterpolationTemplate target)
traverseStringInterpolationTemplate transform = traverse traversePart
  where
    traversePart (StringTemplateLiteral literal) =
      pure (StringTemplateLiteral literal)
    traversePart (StringTemplateInterpolation expression) =
      StringTemplateInterpolation
        <$> traverseStringExpression expression
    traverseStringExpression expression = case expression of
      ExpressionString value -> ExpressionString <$> transform value
      BlockString value -> BlockString <$> transform value
      FunctionBodyString value -> FunctionBodyString <$> transform value
      DeclarationString value -> DeclarationString <$> transform value
      DependentArgumentString value ->
        DependentArgumentString <$> transform value
      IdentifierExpressionString value ->
        IdentifierExpressionString <$> transform value
      StringLiteralString value -> StringLiteralString <$> transform value
      ValueString value -> ValueString <$> transform value

renderStringInterpolationTemplate
  :: (value -> String)
  -> StringInterpolationTemplate value
  -> String
renderStringInterpolationTemplate renderValue = unwords . map renderPart
  where
    renderPart (StringTemplateLiteral literal) = literal
    renderPart (StringTemplateInterpolation expression) =
      case expression of
        ExpressionString {} -> "%_Expr"
        BlockString {} -> "%_Block"
        FunctionBodyString {} -> "%_FunctionBody"
        DeclarationString {} -> "%_DependentDeclaration"
        DependentArgumentString {} -> "%_DependentArgument"
        IdentifierExpressionString value -> '%' : renderValue value
        StringLiteralString value -> '%' : renderValue value
        ValueString value -> '%' : renderValue value
