-- | AST capture supplied by explicitly declared syntax-category types.
module Evaluation.SyntaxCapture
  ( captureSyntaxExpression
  , specializeSyntaxHoleKind
  ) where

import Control.Applicative ((<|>))
import DatraLanguage.AST
  ( Expression
      ( AsciiStringLiteral
      , AtlasMap
      , FunctionBody
      , IdentifierOperation
      , IdentifierReference
      , IdentifierTemplateOperation
      , MapConcatenation
      , MapSequence
      , OptionalType
      , StringTemplate
      , SyntaxBoundary
      )
  , isDeclarationExpression
  )
import DatraLanguage.SyntaxTemplate (SyntaxHoleKind (..))
import DatraOrdinal (finiteOrdinal)
import Evaluation.IdentifierErasure (stripOuterIdentifierType)
import Evaluation.Value
  ( ASTMetaCategory (..)
  , BuiltinMetaType (ASTMetaType)
  , EvaluatedEither (..)
  , InterpretedValue
  , ValueForm (BuiltinMetaTypeForm, EitherForm)
  , interpretedForm
  , interpretedMap
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  )

captureSyntaxExpression
  :: InterpretedValue
  -> Expression
  -> Maybe Expression
captureSyntaxExpression target captured =
  case syntaxListElement normalized of
    Just element -> captureSyntaxList element captured
    Nothing -> captureAtomicSyntaxExpression normalized captured
  where
    normalized = syntaxCategoryTarget target

captureAtomicSyntaxExpression
  :: InterpretedValue
  -> Expression
  -> Maybe Expression
captureAtomicSyntaxExpression target captured =
  case interpretedForm target of
    BuiltinMetaTypeForm (ASTMetaType ExpressionAST) -> Just captured
    BuiltinMetaTypeForm (ASTMetaType BlockAST) ->
      case captured of
        AtlasMap {} -> Just captured
        _ -> Nothing
    BuiltinMetaTypeForm (ASTMetaType FunctionBodyAST) ->
      case captured of
        FunctionBody {} -> Just captured
        _ -> Nothing
    BuiltinMetaTypeForm (ASTMetaType DeclarationAST)
      | isDeclarationExpression captured -> Just captured
    BuiltinMetaTypeForm (ASTMetaType DependentIdentifierAST) ->
      dependentIdentifier captured
    _ -> Nothing
  where
    dependentIdentifier value = case value of
      IdentifierReference {} -> Just value
      AsciiStringLiteral {} -> Just value
      StringTemplate {} -> Just value
      IdentifierOperation _ _ Nothing -> Just value
      IdentifierTemplateOperation _ _ Nothing -> Just value
      OptionalType inner -> OptionalType <$> dependentIdentifier inner
      _ -> Nothing

captureSyntaxList
  :: InterpretedValue
  -> Expression
  -> Maybe Expression
captureSyntaxList element captured = case captured of
  SyntaxBoundary inner -> SyntaxBoundary <$> captureSyntaxList element inner
  AtlasMap members -> AtlasMap <$> traverse captureMember members
  MapSequence members -> MapSequence <$> traverse captureMember members
  MapConcatenation left right ->
    MapConcatenation
      <$> captureSyntaxList element left
      <*> captureSyntaxList element right
  _ -> captureMember captured
  where
    captureMember = captureSyntaxExpression element

syntaxListElement :: InterpretedValue -> Maybe InterpretedValue
syntaxListElement target = direct target <|> do
  unwrapped <- either (const Nothing) Just (stripOuterIdentifierType target)
  syntaxListElement unwrapped
  where
    direct value = case interpretedForm value of
      EitherForm alternatives
        | emptyBranch left -> listBranch right
        | emptyBranch right -> listBranch left
        | otherwise -> Nothing
        where
          left = evaluatedEitherLeft alternatives
          right = evaluatedEitherRight alternatives
      _ -> Nothing
    listBranch branch
      = interpretedMapValueAt branchMap (finiteOrdinal 0) >>= syntaxElement
      where
        branchMap = interpretedMap branch
    emptyBranch branch =
      interpretedMapFinalOrderType (interpretedMap branch) == finiteOrdinal 0
    syntaxElement value = case interpretedForm value of
      BuiltinMetaTypeForm (ASTMetaType _) -> Just value
      _ -> syntaxListElement value <|> do
        unwrapped <- either
          (const Nothing) Just (stripOuterIdentifierType value)
        syntaxElement unwrapped

syntaxCategoryTarget :: InterpretedValue -> InterpretedValue
syntaxCategoryTarget target = case stripOuterIdentifierType target of
  Right unwrapped -> syntaxCategoryTarget unwrapped
  Left _ -> target

-- | Give a typed interpolation the parser capability owned by its evaluated
-- target type. Ordinary types remain value captures; AST category types carry
-- the few structural capabilities required by syntax rewriting.
specializeSyntaxHoleKind
  :: InterpretedValue
  -> SyntaxHoleKind value
  -> SyntaxHoleKind value
specializeSyntaxHoleKind target hole =
  case (interpretedForm normalized, hole) of
  (BuiltinMetaTypeForm (ASTMetaType ExpressionAST), ValueSyntaxHole value) ->
    ExpressionSyntaxHole value
  (BuiltinMetaTypeForm (ASTMetaType BlockAST), ValueSyntaxHole value) ->
    BlockSyntaxHole value
  (BuiltinMetaTypeForm (ASTMetaType FunctionBodyAST), ValueSyntaxHole value) ->
    FunctionBodySyntaxHole value
  (BuiltinMetaTypeForm (ASTMetaType DeclarationAST), ValueSyntaxHole value) ->
    DeclarationSyntaxHole value
  ( BuiltinMetaTypeForm (ASTMetaType DependentIdentifierAST)
    , ValueSyntaxHole value
    ) -> DependentIdentifierSyntaxHole value
  (_, ValueSyntaxHole value)
    | Just _ <- syntaxListElement normalized -> ExpressionSyntaxHole value
  _ -> hole
  where
    normalized = syntaxCategoryTarget target
