-- | AST capture supplied by explicitly declared syntax-category types.
module Evaluation.SyntaxCapture
  ( captureSyntaxExpression
  , specializeStringExpression
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
import StringExpression (StringExpression (..))
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
specializeStringExpression
  :: InterpretedValue
  -> StringExpression value
  -> StringExpression value
specializeStringExpression target hole =
  case (interpretedForm normalized, hole) of
  (PrimitiveTypeForm (SyntaxPrimitive ExpressionAST), ValueString value) ->
    ExpressionString value
  (PrimitiveTypeForm (SyntaxPrimitive BlockAST), ValueString value) ->
    BlockString value
  (PrimitiveTypeForm (SyntaxPrimitive FunctionBodyAST), ValueString value) ->
    FunctionBodyString value
  (PrimitiveTypeForm (SyntaxPrimitive DeclarationAST), ValueString value) ->
    DeclarationString value
  ( PrimitiveTypeForm (SyntaxPrimitive DependentArgumentAST)
    , ValueString value
    ) -> DependentArgumentString value
  ( PrimitiveTypeForm (SyntaxPrimitive IdentifierExpressionAST)
    , ValueString value
    ) -> IdentifierExpressionString value
  (_, ValueString value)
    | valueProducesStrings normalized -> StringLiteralString value
  (_, ValueString value)
    | Just _ <- syntaxListElement normalized -> ExpressionString value
  _ -> hole
  where
    normalized = syntaxCategoryTarget target
