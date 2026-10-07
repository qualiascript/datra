-- | AST capture supplied by explicitly declared syntax-category types.
module Evaluation.SyntaxCapture
  ( captureSyntaxExpression
  , specializeSyntaxHoleKind
  ) where

import DatraLanguage.AST
  ( Expression (AsciiStringLiteral, AtlasMap, IdentifierReference, OptionalType)
  )
import DatraLanguage.SyntaxTemplate (SyntaxHoleKind (..))
import Evaluation.Value
  ( ASTMetaCategory (..)
  , BuiltinMetaType (ASTMetaType)
  , InterpretedValue
  , ValueForm (BuiltinMetaTypeForm)
  , interpretedForm
  )
import IdentifierValueType (isIdentifierValue)

captureSyntaxExpression
  :: InterpretedValue
  -> Expression
  -> Maybe Expression
captureSyntaxExpression target captured =
  case interpretedForm target of
    BuiltinMetaTypeForm (ASTMetaType AnyAST) -> Just captured
    BuiltinMetaTypeForm (ASTMetaType ExpressionAST) -> Just captured
    BuiltinMetaTypeForm (ASTMetaType BlockAST) ->
      case captured of
        AtlasMap {} -> Just captured
        _ -> Nothing
    BuiltinMetaTypeForm (ASTMetaType IdentifierExpressionAST) ->
      identifierExpression captured
    _ -> Nothing
  where
    identifierExpression value = case value of
      IdentifierReference {} -> Just value
      OptionalType IdentifierReference {} -> Just value
      AsciiStringLiteral name
        | isIdentifierValue name -> Just value
      OptionalType (AsciiStringLiteral name)
        | isIdentifierValue name -> Just value
      _ -> Nothing

-- | Give a typed interpolation the parser capability owned by its evaluated
-- target type. Ordinary types remain value captures; AST category types carry
-- the few structural capabilities required by syntax rewriting.
specializeSyntaxHoleKind
  :: InterpretedValue
  -> SyntaxHoleKind value
  -> SyntaxHoleKind value
specializeSyntaxHoleKind target hole = case (interpretedForm target, hole) of
  (BuiltinMetaTypeForm (ASTMetaType AnyAST), ValueSyntaxHole value) ->
    ExpressionSyntaxHole value
  (BuiltinMetaTypeForm (ASTMetaType ExpressionAST), ValueSyntaxHole value) ->
    ExpressionSyntaxHole value
  (BuiltinMetaTypeForm (ASTMetaType BlockAST), ValueSyntaxHole value) ->
    BlockSyntaxHole value
  ( BuiltinMetaTypeForm (ASTMetaType IdentifierExpressionAST)
    , ValueSyntaxHole value
    ) -> IdentifierExpressionSyntaxHole value
  _ -> hole
