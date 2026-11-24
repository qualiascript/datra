-- | Identifier expressions mark ordinary string-producing expressions for
-- identifier-family interpretation.
module DatraLanguage.IdentifierExpression
  ( SimpleIdentifierString (..)
  , SymbolLiteral (..)
  , IdentifierExpression (..)
  , traverseIdentifierExpression
  , mapIdentifierExpression
  ) where

import Data.Functor.Identity (Identity (..))

newtype SimpleIdentifierString = SimpleIdentifierString
  { simpleIdentifierStringText :: String
  }
  deriving (Eq, Ord, Show)

newtype SymbolLiteral = SymbolLiteral
  { symbolLiteralText :: String
  }
  deriving (Eq, Ord, Show)

-- | A non-empty identifier-string family represented by its required family
-- expression. Literal strings are ordinary expressions in this same family;
-- they are not a separate semantic case.
newtype IdentifierExpression expression = IdentifierExpressionBody expression
  deriving (Eq, Ord, Show)

traverseIdentifierExpression
  :: Applicative f
  => (left -> f right)
  -> IdentifierExpression left
  -> f (IdentifierExpression right)
traverseIdentifierExpression visit identifier = case identifier of
  IdentifierExpressionBody body -> IdentifierExpressionBody <$> visit body

mapIdentifierExpression
  :: (left -> right)
  -> IdentifierExpression left
  -> IdentifierExpression right
mapIdentifierExpression visit = runIdentity
  . traverseIdentifierExpression (Identity . visit)
