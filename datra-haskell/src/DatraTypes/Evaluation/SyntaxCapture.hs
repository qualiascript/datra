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
      , DependentArgument
      , IdentifierReference
      , MapConcatenation
      , MapSequence
      , OptionalType
      , StringTemplate
      , SyntaxBoundary
      )
  )
import DatraLanguage.DependentDeclaration (dependentDeclarationCandidate)
import DatraLanguage.SyntaxTemplate (SyntaxHoleKind (..))
import DatraOrdinal (finiteOrdinal)
import Evaluation.IdentifierErasure (stripOuterIdentifierType)
import Evaluation.Specification.String (valueProducesStrings)
import Evaluation.Value
  ( SyntaxCategory (..)
  , PrimitiveType (SyntaxPrimitive)
  , EvaluatedEither (..)
  , InterpretedValue
  , ValueForm (PrimitiveTypeForm, EitherForm)
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
    PrimitiveTypeForm (SyntaxPrimitive ExpressionAST) -> Just captured
    PrimitiveTypeForm (SyntaxPrimitive BlockAST) ->
      case captured of
        AtlasMap {} -> Just captured
        _ -> Nothing
    PrimitiveTypeForm (SyntaxPrimitive FunctionBodyAST) ->
      case captured of
        FunctionBody {} -> Just captured
        _ -> Nothing
    PrimitiveTypeForm (SyntaxPrimitive DeclarationAST)
      | dependentDeclarationCandidate captured -> Just captured
    PrimitiveTypeForm (SyntaxPrimitive DependentArgumentAST) ->
      dependentArgument captured
    PrimitiveTypeForm (SyntaxPrimitive IdentifierExpressionAST) ->
      case captured of
        IdentifierReference {} -> Just captured
        _ -> Nothing
    _ -> Nothing
  where
    dependentArgument value = case value of
      IdentifierReference {} -> Just value
      AsciiStringLiteral {} -> Just value
      StringTemplate {} -> Just value
      DependentArgument {} -> Just value
      OptionalType inner -> OptionalType <$> dependentArgument inner
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
      PrimitiveTypeForm (SyntaxPrimitive _) -> Just value
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
  (PrimitiveTypeForm (SyntaxPrimitive ExpressionAST), ValueSyntaxHole value) ->
    ExpressionSyntaxHole value
  (PrimitiveTypeForm (SyntaxPrimitive BlockAST), ValueSyntaxHole value) ->
    BlockSyntaxHole value
  (PrimitiveTypeForm (SyntaxPrimitive FunctionBodyAST), ValueSyntaxHole value) ->
    FunctionBodySyntaxHole value
  (PrimitiveTypeForm (SyntaxPrimitive DeclarationAST), ValueSyntaxHole value) ->
    DeclarationSyntaxHole value
  ( PrimitiveTypeForm (SyntaxPrimitive DependentArgumentAST)
    , ValueSyntaxHole value
    ) -> DependentArgumentSyntaxHole value
  ( PrimitiveTypeForm (SyntaxPrimitive IdentifierExpressionAST)
    , ValueSyntaxHole value
    ) -> IdentifierExpressionSyntaxHole value
  (_, ValueSyntaxHole value)
    | valueProducesStrings normalized -> StringLiteralSyntaxHole value
  (_, ValueSyntaxHole value)
    | Just _ <- syntaxListElement normalized -> ExpressionSyntaxHole value
  _ -> hole
  where
    normalized = syntaxCategoryTarget target
