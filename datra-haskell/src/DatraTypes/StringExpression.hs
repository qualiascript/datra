-- | String-producing expressions used by declared syntax. A declaration is a
-- source-order concatenation of literal strings and typed string expressions.
module StringExpression
  ( StringExpression (..)
  , stringExpressionValue
  , mapStringExpression
  , StringTemplateInterpolation (..)
  , StringInterpolationTemplate
  , FunctionSyntax (..)
  , TemplateSelection (..)
  , templateSelectionProjection
  , literalStringInterpolationTemplate
  , traverseStringInterpolationTemplate
  ) where

import DatraLanguage.StringTemplate (StringTemplateInterpolation (..))

data StringExpression value
  = LiteralString String
  | ExpressionString value
  | BlockString value
  | FunctionBodyString value
  | DeclarationString value
  | DependentArgumentString value
  | IdentifierExpressionString value
  | StringLiteralString value
  | ValueString value
  deriving (Eq, Show)

stringExpressionValue :: StringExpression value -> Maybe value
stringExpressionValue expression = case expression of
  LiteralString {} -> Nothing
  ExpressionString value -> Just value
  BlockString value -> Just value
  FunctionBodyString value -> Just value
  DeclarationString value -> Just value
  DependentArgumentString value -> Just value
  IdentifierExpressionString value -> Just value
  StringLiteralString value -> Just value
  ValueString value -> Just value

mapStringExpression
  :: (source -> target)
  -> StringExpression source
  -> StringExpression target
mapStringExpression transform expression = case expression of
  LiteralString value -> LiteralString value
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
  [StringTemplateInterpolation (StringExpression value)]

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
literalStringInterpolationTemplate =
  map (StringTemplateInterpolation . LiteralString) . words

traverseStringInterpolationTemplate
  :: Applicative f
  => (source -> f target)
  -> StringInterpolationTemplate source
  -> f (StringInterpolationTemplate target)
traverseStringInterpolationTemplate transform = traverse traversePart
  where
    traversePart (StringTemplateInterpolation expression) =
      StringTemplateInterpolation
        <$> traverseStringExpression expression
    traverseStringExpression expression = case expression of
      LiteralString value -> pure (LiteralString value)
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
