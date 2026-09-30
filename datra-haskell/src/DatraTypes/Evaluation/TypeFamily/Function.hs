-- | Fundamental typing operations for pure function values.
module Evaluation.TypeFamily.Function
  ( specifyFunction
  , validateFunctionInput
  , decideFunctionSubfederation
  ) where

import DatraLanguage.SyntaxTemplate (FunctionSyntax)
import Evaluation.Error
  ( FunctionFailure (..)
  , InterpretingError (FunctionEvaluationFailed)
  )
import Evaluation.Specification.Decision
  ( Decision (..)
  , decideAll
  , mapDecision
  )
import Evaluation.Value

specifyFunction
  :: (InterpretedValue -> InterpretedValue -> Decision ())
  -> (InterpretedValue
      -> InterpretedValue
      -> Either InterpretingError InterpretedValue)
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyFunction decideSubfederation specify source target =
  case (interpretedFunction source, interpretedFunction target) of
    (Just original, Just signature) ->
      case decideSubfederation source target of
        DecisionProved () -> Right (makeFunctionValue signature
          { functionSource = case functionSource original of
              Nothing -> Nothing
              Just sourceText
                | interpretedCanonicalResult (functionDomain original) == interpretedCanonicalResult (functionDomain signature)
                , interpretedCanonicalResult (functionCodomain original) == interpretedCanonicalResult (functionCodomain signature) -> Just sourceText
              Just sourceText -> Just
                ("(" <> sourceText <> ") ~> (" <> functionSignatureSource signature <> ")")
          , functionPrepare = Just (\argument -> do
              prepared <- case functionPrepare original of
                Just prepare -> prepare argument
                Nothing -> do
                  validateFunctionInput
                    decideSubfederation specify argument
                    (functionDomain original)
                  pure argument
              validateFunctionInput
                decideSubfederation specify prepared
                (functionDomain signature)
              pure prepared)
          , functionInvoke = functionInvoke original
          })
        DecisionRefuted -> Left (FunctionEvaluationFailed
          FunctionSignatureVarianceViolation)
        DecisionUndecidable -> Left (FunctionEvaluationFailed
          (FunctionSpecificationUndecidable
            (show (interpretedCanonicalResult source))
            (show (interpretedCanonicalResult target))))
    _ -> Left (FunctionEvaluationFailed ExpectedFunctionValue)

validateFunctionInput
  :: (InterpretedValue -> InterpretedValue -> Decision ())
  -> (InterpretedValue
      -> InterpretedValue
      -> Either InterpretingError InterpretedValue)
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError ()
validateFunctionInput decideSubfederation specify input domain =
  case decideSubfederation input domain of
    DecisionProved () -> Right ()
    _ -> () <$ specify input domain

decideFunctionSubfederation
  :: (InterpretedValue -> InterpretedValue -> Decision ())
  -> InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideFunctionSubfederation decideSubfederation source target
  | Just sourceFunction <- interpretedFunction source
  , Just targetFunction <- interpretedFunction target =
      if not
          (patternCompatible
            (functionSyntax sourceFunction)
            (functionSyntax targetFunction))
        then DecisionRefuted
      else if interpretedCanonicalResult source
          == interpretedCanonicalResult target
        then DecisionProved ()
      else case functionSource targetFunction of
        Just _ -> DecisionUndecidable
        Nothing -> mapDecision (const ()) (decideAll
          [ decideSubfederation
              (functionDomain targetFunction)
              (functionDomain sourceFunction)
          , decideSubfederation
              (functionCodomain sourceFunction)
              (functionCodomain targetFunction)
          ])
  | interpretedCanonicalResult source == interpretedCanonicalResult target = DecisionProved ()
  | BuiltinMetaTypeForm _ <- interpretedForm source = DecisionRefuted
  | otherwise = DecisionRefuted

patternCompatible
  :: Maybe (FunctionSyntax InterpretedValue)
  -> Maybe (FunctionSyntax InterpretedValue)
  -> Bool
patternCompatible _ Nothing = True
patternCompatible (Just source) (Just target) =
  functionSyntaxEquivalent source target
patternCompatible Nothing (Just _) = False
