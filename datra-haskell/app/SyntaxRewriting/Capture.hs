module SyntaxRewriting.Capture
  ( prepareStructuralCapture
  ) where

import DatraLanguage.Application (applicationPhrase)
import DatraLanguage.AST
  ( Expression (..)
  )
import DatraLanguage.DependentDeclaration
  ( dependentDeclarationCandidate )
import StringExpression
  ( StringExpression (..)
  )
import StringInterpolation
  ( DeclarativeCapture (..)
  )

-- | Validate and normalize capture categories whose contracts are purely
-- structural. Semantic value captures are typed by the rewrite stack and
-- deliberately have no fallback here.
prepareStructuralCapture
  :: DeclarativeCapture
  -> Expression
  -> Maybe Expression
prepareStructuralCapture kind captured = case kind of
  StringExpressionCapture stringKind -> case stringKind of
    LiteralString literal -> case captured of
      AsciiStringLiteral actual
        | actual == literal -> Just captured
      _ -> Nothing
    ExpressionString {} -> Just captured
    BlockString {} -> case captured of
      AtlasMap {} -> Just captured
      MapSequence {} -> Just captured
      _ -> Just (AtlasMap (applicationPhrase captured))
    FunctionBodyString {} -> case captured of
      FunctionBody {} -> Just captured
      _ -> Nothing
    DeclarationString {}
      | dependentDeclarationCandidate captured -> Just captured
      | otherwise -> Nothing
    DependentArgumentString {} -> dependentArgument captured
    IdentifierExpressionString {} -> case captured of
      IdentifierReference {} -> Just captured
      _ -> Nothing
    ValueString {} -> Nothing
  where
    dependentArgument value = case value of
      IdentifierReference {} -> Just value
      AsciiStringLiteral {} -> Just value
      StringTemplate {} -> Just value
      DependentArgument {} -> Just value
      OptionalType inner -> OptionalType <$> dependentArgument inner
      _ -> Nothing
