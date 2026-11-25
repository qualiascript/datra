module Evaluation.Identifier
  ( interpretIdentifierExpression
  , scopeSelectorName
  , interpretSimpleDependentArgument
  , transparentEitherAlias
  ) where

import DatraLanguage.AST
import DatraTypes
import DatraTypes.Evaluation (Interpreter)
import Evaluation.Scope.Protection (runProtectedOperation)

interpretIdentifierExpression
  :: Interpreter
  -> Expression
  -> Either InterpretingError InterpretedValue
interpretIdentifierExpression interpret body = case body of
  AsciiStringLiteral name ->
    Right (makeIdentifierExpression (SimpleIdentifierString name))
  _ -> do
    rendered <- interpret body
    case asciiStringFromInterpretedMap (interpretedMap rendered) of
      Just name -> Right
        (makeIdentifierExpression (SimpleIdentifierString name))
      Nothing -> Left (LookupRequiresString (interpretedValueKind rendered))

scopeSelectorName
  :: Interpreter
  -> IdentifierExpression Expression
  -> Either InterpretingError String
scopeSelectorName interpret selector = case literalIdentifierName selector of
  Just (SimpleIdentifierString name) -> Right name
  Nothing -> case selector of
    IdentifierExpressionBody body -> do
      identifier <- interpretIdentifierExpression interpret body
      case asciiStringFromInterpretedMap (interpretedMap identifier) of
        Just name | not (null name) -> Right name
        Just _ -> Left (UnknownIdentifier "")
        Nothing -> Left
          (LookupRequiresString (interpretedValueKind identifier))

interpretSimpleDependentArgument
  :: ScopeActivation
  -> String
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
interpretSimpleDependentArgument protection identifierString typeAnnotation =
  runProtectedOperation protection [typeAnnotation] $ \actuals ->
    case actuals of
      [actualAnnotation]
        | identifierString == "False"
        , interpretedValueKind actualAnnotation == NaturalValueKind
        , interpretedInteger actualAnnotation == Just 0 ->
            Right (booleanValue False)
        | identifierString == "True"
        , interpretedValueKind actualAnnotation == NaturalValueKind
        , interpretedInteger actualAnnotation == Just 1 ->
            Right (booleanValue True)
        | otherwise -> Right
            (simpleIdentifierTypeValue identifierString actualAnnotation)
      _ -> Right neverValue

transparentEitherAlias
  :: InterpretedValue
  -> Either InterpretingError InterpretedValue
transparentEitherAlias value =
  case stripOuterIdentifierType value of
    Right underlying
      | interpretedValueKind underlying == EitherValueKind -> Right underlying
    _ -> Right value
