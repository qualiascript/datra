-- | AST capture supplied by explicitly declared syntax-category types.
module Evaluation.SyntaxCapture (captureSyntaxExpression) where

import DatraLanguage.AST
  ( Expression (AsciiStringLiteral, AtlasMap, IdentifierReference, OptionalType)
  )
import Evaluation.Value
  ( BuiltinMetaType (ASTMetaType)
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
    BuiltinMetaTypeForm (ASTMetaType Nothing) -> Just captured
    BuiltinMetaTypeForm (ASTMetaType (Just "Expr")) -> Just captured
    BuiltinMetaTypeForm (ASTMetaType (Just "Block")) ->
      case captured of
        AtlasMap {} -> Just captured
        _ -> Nothing
    BuiltinMetaTypeForm (ASTMetaType (Just "IdenExp")) ->
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
