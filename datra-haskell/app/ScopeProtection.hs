module ScopeProtection
  ( EvaluationProtectionContext
  , initialProtectionContext
  , enterProtectionScope
  , currentProtectionLabel
  , authorizeProtectedValue
  , runProtectedOperation
  , protectWithPoliciesOf
  , valueIsScopeProtected
  ) where

import Data.IORef
import Data.List (nub, sort)
import Data.List.NonEmpty (NonEmpty (..))
import Numeric.Natural (Natural)
import System.IO.Unsafe (unsafePerformIO)

import DatraTypes

data EvaluationProtectionContext = EvaluationProtectionContext
  { protectionLabelSupply :: IORef Natural
  , activeProtectionLabels :: NonEmpty DynamicScopeLabel
  }

-- Labels are evaluator-internal and never affect canonical identity.  Each
-- top-level pure evaluation owns one private monotonic supply; the small local
-- reference avoids threading allocation state through every existing checked
-- DatraTypes operation.
initialProtectionContext :: salt -> EvaluationProtectionContext
initialProtectionContext salt = unsafePerformIO $ do
  salt `seq` pure ()
  supply <- newIORef 1
  pure (EvaluationProtectionContext supply (DynamicScopeLabel 0 :| []))
{-# NOINLINE initialProtectionContext #-}

enterProtectionScope
  :: salt
  -> EvaluationProtectionContext
  -> (DynamicScopeLabel, EvaluationProtectionContext)
enterProtectionScope salt context = unsafePerformIO $ do
  salt `seq` pure ()
  next <- atomicModifyIORef' (protectionLabelSupply context)
    (\label -> (label + 1, label))
  let label = DynamicScopeLabel next
  pure
    ( label
    , context
        { activeProtectionLabels =
            label :| toList (activeProtectionLabels context)
        }
    )
  where
    toList (first :| remaining) = first : remaining
{-# NOINLINE enterProtectionScope #-}

currentProtectionLabel
  :: EvaluationProtectionContext
  -> DynamicScopeLabel
currentProtectionLabel = headNonEmpty . activeProtectionLabels
  where
    headNonEmpty (label :| _) = label

authorizeProtectedValue
  :: EvaluationProtectionContext
  -> InterpretedValue
  -> Either InterpretedValue InterpretedValue
authorizeProtectedValue context value =
  case interpretedScopeProtection value of
    Nothing -> Right value
    Just protection
      | scopeProtectionLabel protection
          `elem` nonEmptyToList (activeProtectionLabels context) ->
              Right (withoutScopeProtection value)
      | otherwise -> Left neverValue
  where
    nonEmptyToList (first :| remaining) = first : remaining

runProtectedOperation
  :: EvaluationProtectionContext
  -> [InterpretedValue]
  -> ([InterpretedValue] -> Either InterpretingError InterpretedValue)
  -> Either InterpretingError InterpretedValue
runProtectedOperation context operands operation =
  case traverse (authorizeProtectedValue context) operands of
    Left inaccessible -> Right inaccessible
    Right actuals -> do
      result <- operation actuals
      pure (case normalizedPolicies operands of
        [] -> result
        _ -> protectWithPoliciesOf context (result : operands) result)

protectWithPoliciesOf
  :: EvaluationProtectionContext
  -> [InterpretedValue]
  -> InterpretedValue
  -> InterpretedValue
protectWithPoliciesOf context operands result =
  case normalizedPolicies operands of
    [] -> result
    first : remaining ->
      protectInterpretedValue
        (currentProtectionLabel context)
        (first :| remaining)
        result

valueIsScopeProtected :: InterpretedValue -> Bool
valueIsScopeProtected = maybe False (const True) . interpretedScopeProtection

normalizedPolicies :: [InterpretedValue] -> [ScopeProtectionPolicy]
normalizedPolicies = sort . nub . concatMap policies
  where
    policies value =
      case interpretedScopeProtection value of
        Nothing -> []
        Just protection ->
          case scopeProtectionPolicies protection of
            first :| remaining -> first : remaining
