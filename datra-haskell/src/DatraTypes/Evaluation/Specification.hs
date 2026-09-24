-- | Central compile-time dispatch for the specification operator.
--
-- Each Datra type family owns its specification behavior; this module only
-- handles cross-family function alternatives and routes recursive operations.
module Evaluation.Specification
  ( validateFunctionInput
  , specifyValues
  , assignIdentifierValues
  ) where

import Control.Monad (foldM)
import Evaluation.Arguments (argumentAlternatives)
import Evaluation.Boolean (makeBoolean)
import Evaluation.Either (makeEitherValue)
import Evaluation.Error (InterpretingError (FunctionError))
import Evaluation.Specification.Decision (Decision (DecisionProved))
import Evaluation.Specification.Subfederation
  ( decideValueSubfederation
  )
import Evaluation.TypeFamily
  ( TypeFamilyOperations (specifyTypeFamily)
  , typeFamilyOperations
  )
import Evaluation.TypeFamily.Function qualified as Function
import Evaluation.TypeFamily.Structural qualified as Structural
import Evaluation.Value

specifyValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyValues source target
  | EitherForm _ <- interpretedForm source
  , isFunctionFamily source = do
      specified <- traverse (`specifyValues` target) (argumentAlternatives source)
      case specified of
        first:rest -> foldM makeEitherValue first rest
        [] -> Left (FunctionError "empty function sum")
  | Just _ <- interpretedFunction source
  , EitherForm _ <- interpretedForm target =
      case [ signature
           | isFunctionFamily target
           , signature <- functionAlternatives target
           , DecisionProved () <-
               [decideValueSubfederation source (makeFunctionValue signature)]
           ] of
        [signature] -> specifyValues source (makeFunctionValue signature)
        [] ->
          Left (FunctionError
            "no matching alternative in function specification")
        _ -> Left (FunctionError "ambiguous function specification")
  | otherwise =
      specifyTypeFamily
        (typeFamilyOperations
          (datraTypeFamily (interpretedDatraType target)))
        decideValueSubfederation
        specifyValues
        source
        target

assignIdentifierValues
  :: String
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
assignIdentifierValues =
  Structural.assignIdentifierValues
    makeBoolean specifyValues decideValueSubfederation

validateFunctionInput
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError ()
validateFunctionInput =
  Function.validateFunctionInput decideValueSubfederation specifyValues
