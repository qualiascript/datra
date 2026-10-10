-- | Central compile-time dispatch for the specification operator.
--
-- Each Datra type family owns its specification behavior; this module only
-- handles cross-family function alternatives and routes recursive operations.
module Evaluation.Specification
  ( validateFunctionInput
  , specifyValues
  , contextuallySpecifyValues
  , assignIdentifierValues
  ) where

import Control.Monad (foldM)
import Evaluation.Arguments (argumentAlternatives)
import Evaluation.Boolean (makeBoolean)
import Evaluation.Either (makeEitherValue)
import Evaluation.Error
  ( AtlasMapFederationRefutation
      (AtlasMapFederationSpecificationHasNoMatchingMember)
  , FunctionFailure (..)
  , InterpretingError
      ( AtlasMapFederationOperationRefuted
      , FunctionEvaluationFailed
      )
  )
import Evaluation.Identifier (inferredIdentifierAssignmentValue)
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
  | NeverForm <- interpretedForm source
  , NeverForm <- interpretedForm target = Right neverValue
  | NeverForm <- interpretedForm source = Left
      (FunctionEvaluationFailed NoApplicableFunctionAlternative)
  | NeverForm <- interpretedForm target = Left
      (FunctionEvaluationFailed NoApplicableFunctionAlternative)
  -- Generic functions retain an existential-package view for application,
  -- but function specification must continue to compare their signatures.
  -- Otherwise the target's auxiliary dependent-sum view incorrectly treats
  -- the source function itself as an existential package.
  | Just _ <- interpretedFunction source
  , Just _ <- interpretedFunction target =
      specifyTypeFamily
        (typeFamilyOperations
          (datraTypeFamily (interpretedDatraType target)))
        decideValueSubfederation
        specifyValues
        source
        target
  | Just dependent <- dependentSumView target =
      evaluatedDependentSumSpecify dependent source
  | EitherForm _ <- interpretedForm target
  , any isDependentSum (argumentAlternatives target) =
      case
          [ prepared
          | alternative <- argumentAlternatives target
          , Right prepared <- [specifyValues source alternative]
          ] of
        [prepared] -> Right prepared
        _ -> Left (FunctionEvaluationFailed
          NoMatchingFunctionSpecificationAlternative)
  | EitherForm _ <- interpretedForm source
  , isFunctionFamily source = do
      specified <- traverse (`specifyValues` target) (argumentAlternatives source)
      case specified of
        first:rest -> foldM makeEitherValue first rest
        [] -> Left (FunctionEvaluationFailed EmptyFunctionSum)
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
          Left (FunctionEvaluationFailed
            NoMatchingFunctionSpecificationAlternative)
        _ -> Left (FunctionEvaluationFailed AmbiguousFunctionSpecification)
  | otherwise =
      specifyTypeFamily
        (typeFamilyOperations
          (datraTypeFamily (interpretedDatraType target)))
        decideValueSubfederation
        specifyValues
        source
        target

-- | Apply an expected type as inference context. Ordinary specification keeps
-- its explicit semantics; this extension is only for a surrounding construct
-- whose target makes exactly one named alternative possible.
contextuallySpecifyValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
contextuallySpecifyValues source target =
  case specifyValues source target of
    Right prepared -> Right prepared
    Left original ->
      case interpretedForm target of
        DependentIdentifierTypeForm identifier
          | sourceHasNoIdentifier source
          , SimpleIdentifierDependency name <-
              evaluatedIdentifierDependency identifier -> do
              let underlying = evaluatedIdentifierUnderlying identifier
              prepared <- contextuallySpecifyValues source underlying
              let given = case decideValueSubfederation source underlying of
                    DecisionProved () -> source
                    _ -> prepared
              pure (inferredIdentifierAssignmentValue name given)
        EitherForm _ ->
          case
              [ prepared
              | alternative <- argumentAlternatives target
              , Right prepared <-
                  [contextuallySpecifyValues source alternative]
              ] of
            [prepared] -> Right prepared
            _ -> Left (AtlasMapFederationOperationRefuted
              AtlasMapFederationSpecificationHasNoMatchingMember)
        _ -> Left original

sourceHasNoIdentifier :: InterpretedValue -> Bool
sourceHasNoIdentifier source =
  case interpretedForm source of
    AssignmentForm _ -> False
    DependentIdentifierTypeForm _ -> False
    SpecificationForm specification ->
      sourceHasNoIdentifier (evaluatedSpecificationSourceValue specification)
    _ -> True

isDependentSum :: InterpretedValue -> Bool
isDependentSum value =
  case dependentSumView value of
    Just _ -> True
    Nothing -> False

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
