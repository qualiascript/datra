{-# LANGUAGE LambdaCase #-}

module DatraHost.Syntax
  ( letSyntaxInsertion
  , defSyntaxInsertion
  , valSyntaxInsertion
  , parseNaturalSyntaxInsertion
  , beginSyntaxInsertion
  , doSyntaxInsertion
  , funSyntaxInsertion
  , ifSyntaxInsertion
  , withSyntaxInsertion
  ) where

import DatraLanguage.AST
import DatraLanguage.DependentDeclaration
  ( applyDeclarationModifier
  )
import DatraLanguage.Identifier
  ( identifierNaturalValue )
import DatraTypes
  ( SyntaxFunctionExpansion (..)
  , SyntaxFunctionInsertion (..)
  )

letSyntaxInsertion :: SyntaxFunctionInsertion
letSyntaxInsertion = modifierInsertion DeclarationLet

defSyntaxInsertion :: SyntaxFunctionInsertion
defSyntaxInsertion = modifierInsertion DeclarationDef

valSyntaxInsertion :: SyntaxFunctionInsertion
valSyntaxInsertion = modifierInsertion DeclarationVal

parseNaturalSyntaxInsertion :: SyntaxFunctionInsertion
parseNaturalSyntaxInsertion = (expressionInsertion
    (\case
      [IdentifierReference (SimpleIdentifierString name)] ->
        EllipsisNatural <$> identifierNaturalValue name
      _ -> Nothing))
    { syntaxFunctionValidatedCaptures = [0] }

beginSyntaxInsertion :: SyntaxFunctionInsertion
beginSyntaxInsertion = SyntaxFunctionInsertion
    (\case
      [entries, result] -> Just
        (SyntaxBegin (blockExpressions entries) result)
      [result] -> Just (SyntaxBegin [] result)
      _ -> Nothing)
    []

doSyntaxInsertion :: SyntaxFunctionInsertion
doSyntaxInsertion = SyntaxFunctionInsertion
    (\case
      [entries, result] -> Just
        (SyntaxFunctionBody (blockExpressions entries) result)
      [result] -> Just (SyntaxFunctionBody [] result)
      _ -> Nothing)
    []

funSyntaxInsertion :: SyntaxFunctionInsertion
funSyntaxInsertion = expressionInsertion
    (\case
      [entry] -> Just (Fun entry)
      _ -> Nothing)

ifSyntaxInsertion :: SyntaxFunctionInsertion
ifSyntaxInsertion = expressionInsertion
    (\case
      [condition, yes, no] -> Just (Conditional condition yes no)
      [condition, yes] -> Just
        (Conditional condition yes (AtlasMap []))
      _ -> Nothing)

withSyntaxInsertion :: SyntaxFunctionInsertion
withSyntaxInsertion = expressionInsertion
    (\case
      [modules, FunctionBody bindings result] -> Just
        (WithScopes
          (withModuleOperands modules)
          (Begin bindings result))
      _ -> Nothing)

modifierInsertion :: DeclarationModifier -> SyntaxFunctionInsertion
modifierInsertion modifier = expressionInsertion
  (\case
    [entry] -> applyDeclarationModifier modifier
      (absorbAssignedConcatenation entry)
    _ -> Nothing)

expressionInsertion
  :: ([Expression] -> Maybe Expression)
  -> SyntaxFunctionInsertion
expressionInsertion apply = SyntaxFunctionInsertion
  (fmap SyntaxExpression . apply)
  []

blockExpressions :: Expression -> [Expression]
blockExpressions value = case value of
  AtlasMap entries -> entries
  MapSequence entries -> entries
  SyntaxBoundary inner -> blockExpressions inner
  _ -> [value]

withModuleOperands :: Expression -> [Expression]
withModuleOperands value = case value of
  AtlasMap modules -> modules
  MapSequence modules -> modules
  MapConcatenation left right ->
    withModuleOperands left <> withModuleOperands right
  SyntaxBoundary inner -> withModuleOperands inner
  _ -> [value]

absorbAssignedConcatenation :: Expression -> Expression
absorbAssignedConcatenation value = case value of
  MapConcatenation
      (MapSpecification given (DependentArgument name Nothing)) right ->
        MapSpecification (MapConcatenation given right)
          (DependentArgument name Nothing)
  _ -> value
