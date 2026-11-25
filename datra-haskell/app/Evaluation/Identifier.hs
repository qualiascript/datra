module Evaluation.Identifier
  ( interpretIdentifierExpression
  , interpretSimpleDependentArgument
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
