-- | Identifier-expression syntax shared by literal expressions and literal
-- templates. This module owns syntactic composition; dependent declarations
-- are only one consumer of identifier expressions.
module DatraLanguage.IdentifierExpression
  ( SimpleIdentifierString (..)
  , SymbolLiteral (..)
  , LiteralTemplateLiteral (..)
  , IdentifierExpressionComposition (..)
  , LiteralTemplate (..)
  , LiteralTemplateSequence (..)
  , LiteralTemplateAtom (..)
  , IdentifierExpression (..)
  , traverseLiteralTemplate
  , mapLiteralTemplate
  , literalTemplateNullable
  ) where

import Data.Functor.Identity (Identity (..))
import Data.List.NonEmpty (NonEmpty)

newtype SimpleIdentifierString = SimpleIdentifierString
  { simpleIdentifierStringText :: String
  }
  deriving (Eq, Ord, Show)

newtype SymbolLiteral = SymbolLiteral
  { symbolLiteralText :: String
  }
  deriving (Eq, Ord, Show)

data LiteralTemplateLiteral
  = IdentifierTemplateLiteral SimpleIdentifierString
  | SymbolTemplateLiteral SymbolLiteral
  deriving (Eq, Ord, Show)

-- | Either and optional composition within an identifier expression. The
-- payload fixes the admissible leaf type, so a literal template cannot contain
-- an arbitrary expression where a template sequence or atom is required.
data IdentifierExpressionComposition value
  = IdentifierComposition value
  | EitherExpression
      (IdentifierExpressionComposition value)
      (IdentifierExpressionComposition value)
  | OptionalExpression (IdentifierExpressionComposition value)
  deriving (Eq, Ord, Show)

newtype LiteralTemplate expression = LiteralTemplate
  { literalTemplateExpression
      :: IdentifierExpressionComposition
          (LiteralTemplateSequence expression)
  }
  deriving (Eq, Ord, Show)

newtype LiteralTemplateSequence expression = LiteralTemplateSequence
  { literalTemplateParts
      :: NonEmpty
          (IdentifierExpressionComposition (LiteralTemplateAtom expression))
  }
  deriving (Eq, Ord, Show)

data LiteralTemplateAtom expression
  = LiteralTemplateLiteralAtom LiteralTemplateLiteral
  | LiteralTemplateCaptureAtom expression
  | LiteralTemplateGroupAtom (LiteralTemplate expression)
  deriving (Eq, Ord, Show)

-- | The identifier-expression families which can name a binding.
data IdentifierExpression expression
  = IdentifierExpressionBody expression
  | LiteralTemplateIdentifier (LiteralTemplate expression)
  deriving (Eq, Ord, Show)

traverseIdentifierComposition
  :: Applicative f
  => (left -> f right)
  -> IdentifierExpressionComposition left
  -> f (IdentifierExpressionComposition right)
traverseIdentifierComposition visit expressionValue = case expressionValue of
  IdentifierComposition value -> IdentifierComposition <$> visit value
  EitherExpression left right -> EitherExpression
    <$> traverseIdentifierComposition visit left
    <*> traverseIdentifierComposition visit right
  OptionalExpression value ->
    OptionalExpression <$> traverseIdentifierComposition visit value

traverseLiteralTemplate
  :: Applicative f
  => (left -> f right)
  -> LiteralTemplate left
  -> f (LiteralTemplate right)
traverseLiteralTemplate visit (LiteralTemplate body) =
  LiteralTemplate <$> traverseIdentifierComposition traverseSequence body
  where
    traverseSequence (LiteralTemplateSequence parts) =
      LiteralTemplateSequence <$>
        traverse (traverseIdentifierComposition traverseAtom) parts
    traverseAtom atom = case atom of
      LiteralTemplateLiteralAtom literal ->
        pure (LiteralTemplateLiteralAtom literal)
      LiteralTemplateCaptureAtom target ->
        LiteralTemplateCaptureAtom <$> visit target
      LiteralTemplateGroupAtom group ->
        LiteralTemplateGroupAtom <$> traverseLiteralTemplate visit group

mapLiteralTemplate
  :: (left -> right)
  -> LiteralTemplate left
  -> LiteralTemplate right
mapLiteralTemplate visit = runIdentity . traverseLiteralTemplate
  (Identity . visit)

-- | Whether a literal template admits a match with no source components.
-- Captures always consume at least one parsed expression; literals always
-- consume their literal. Groups inherit the nested template's nullability.
literalTemplateNullable :: LiteralTemplate expression -> Bool
literalTemplateNullable (LiteralTemplate body) =
  compositionNullable sequenceNullable body
  where
    sequenceNullable (LiteralTemplateSequence parts) =
      all (compositionNullable atomNullable) parts
    atomNullable atom = case atom of
      LiteralTemplateLiteralAtom _ -> False
      LiteralTemplateCaptureAtom _ -> False
      LiteralTemplateGroupAtom group -> literalTemplateNullable group

compositionNullable
  :: (value -> Bool)
  -> IdentifierExpressionComposition value
  -> Bool
compositionNullable nullable composition = case composition of
  IdentifierComposition value -> nullable value
  EitherExpression left right ->
    compositionNullable nullable left || compositionNullable nullable right
  OptionalExpression _ -> True
