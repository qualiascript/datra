module DatraLanguage.StringTemplate
  ( StringTemplatePart (..)
  ) where

-- | One source-order component of a quoted string template. Literal chunks
-- are decoded by the parser; interpolations retain their expressions.
data StringTemplatePart expression
  = StringTemplateLiteral String
  | StringTemplateInterpolation expression
  deriving (Eq, Ord, Show)
