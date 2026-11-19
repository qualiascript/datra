module DatraLanguage.StringTemplate
  ( StringTemplateInterpolation (..)
  ) where

-- | One source-order expression in a quoted string template. Literal chunks
-- are ordinary string-literal expressions, so every component has the same
-- representation.
newtype StringTemplateInterpolation expression = StringTemplateInterpolation
  { stringTemplateInterpolationExpression :: expression
  }
  deriving (Eq, Ord, Show)
