module Interpreting.Syntax
  ( assembleImplicitSyntaxResource
  , sourceSyntaxRuleSets
  ) where

import Control.Applicative ((<|>))
import DatraLanguage.AST
  ( DependentDeclaration
  , Expression (..)
  , SimpleIdentifierString (..)
  , dependentArgumentExpression
  , literalIdentifierName
  )
import DatraLanguage.DependentDeclaration
  ( dependentDeclaration
  , invalidDependentDeclarationModifiers
  )
import DatraLanguage.Diagnostics.Application
  ( SyntaxRewriteFailure (..)
  )
import StringInterpolation
  ( SyntaxRule
  , declarationRules
  )

assembleImplicitSyntaxResource
  :: [Expression]
  -> Either SyntaxRewriteFailure Expression
assembleImplicitSyntaxResource expressions = case reverse expressions of
  [] -> Right (Begin [] (AtlasMap []))
  result : reversedDeclarations -> do
    declarations <- lowerSyntaxDeclarations (reverse reversedDeclarations)
    Right (Begin declarations result)

lowerSyntaxDeclarations
  :: [Expression]
  -> Either SyntaxRewriteFailure [DependentDeclaration Expression]
lowerSyntaxDeclarations = traverse lower
  where
    lower expressionValue = case dependentDeclaration expressionValue of
      Nothing -> Left (ExpectedDependentDeclaration expressionValue)
      Just declaration -> case
          invalidDependentDeclarationModifiers declaration of
        Just (written, correct) -> Left
          (InvalidDependentDeclarationModifiers written correct)
        Nothing -> Right declaration

-- | Compile the parser catalog from the rewritten module AST. Runtime module
-- values and their presentation metadata are deliberately not consulted.
sourceSyntaxRuleSets :: Expression -> [(String, [SyntaxRule])]
sourceSyntaxRuleSets = bindings . resourceBody
  where
    resourceBody value = case value of
      SyntaxBoundary inner -> resourceBody inner
      ScopedExpression _ body -> resourceBody body
      WithScopes _ body -> resourceBody body
      Begin _ result -> result
      _ -> value

    bindings value = case value of
      AtlasMap members -> concatMap bindings members
      MapSequence members -> concatMap bindings members
      MapConcatenation left right -> bindings left <> bindings right
      SyntaxBoundary inner -> bindings inner
      _ -> case dependentArgumentExpression value of
        Just (nameExpression, annotation, given)
          | Just (SimpleIdentifierString name) <-
              literalIdentifierName nameExpression ->
                [(name, rulesIn (maybe value id (given <|> annotation)))]
        _ -> []

    rulesIn value = case value of
      Begin declarations result ->
        concatMap (declarationRules . DeclarationExpression) declarations <>
          rulesIn result
      FunctionBody declarations result ->
        concatMap (declarationRules . DeclarationExpression) declarations <>
          rulesIn result
      AtlasMap members -> concatMap rulesIn members
      MapSequence members -> concatMap rulesIn members
      MapConcatenation left right -> rulesIn left <> rulesIn right
      SyntaxBoundary inner -> rulesIn inner
      _ -> declarationRules value
