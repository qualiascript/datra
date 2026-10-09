module ScopeProtection
  ( initialScopeActivation
  , enterScopeActivation
  , currentScopeLabel
  , authorizeProtectedValue
  , runProtectedOperation
  , protectWithPoliciesOf
  , valueIsScopeProtected
  , ScopeHandoffDecision (..)
  , handoffProtectedValue
  ) where

import Data.IORef (atomicModifyIORef', newIORef)
import Data.List (nub, sort)
import Data.List.NonEmpty (NonEmpty (..))
import System.IO.Unsafe (unsafePerformIO)

import DatraTypes

-- Labels are evaluator-internal and never affect canonical identity.  Each
-- top-level pure evaluation owns one private monotonic supply.  Activated
-- lexical scopes carry the resulting ancestry; the local reference only
-- allocates fresh labels without imposing an evaluator-wide state monad.
initialScopeActivation :: salt -> ScopeActivation
initialScopeActivation salt = unsafePerformIO $ do
  salt `seq` pure ()
  supply <- newIORef 1
  pure (ScopeActivation supply (DynamicScopeLabel 0) Nothing)
{-# NOINLINE initialScopeActivation #-}

enterScopeActivation
  :: salt
  -> ScopeActivation
  -> ScopeActivation
enterScopeActivation salt activation = unsafePerformIO $ do
  salt `seq` pure ()
  next <- atomicModifyIORef' (scopeActivationLabelSupply activation)
    (\label -> (label + 1, label))
  let label = DynamicScopeLabel next
  pure (ScopeActivation
    (scopeActivationLabelSupply activation)
    label
    (Just activation))
{-# NOINLINE enterScopeActivation #-}

currentScopeLabel
  :: ScopeActivation
  -> DynamicScopeLabel
currentScopeLabel = scopeActivationLabel

authorizeProtectedValue
  :: ScopeActivation
  -> InterpretedValue
  -> Either InterpretedValue InterpretedValue
authorizeProtectedValue context value =
  case interpretedScopeProtection value of
    Nothing -> Right value
    Just protection
      | scopeProtectionLabel protection
          `elem` activationLabels context ->
              Right (withoutScopeProtection value)
      | otherwise -> Left neverValue

runProtectedOperation
  :: ScopeActivation
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
  :: ScopeActivation
  -> [InterpretedValue]
  -> InterpretedValue
  -> InterpretedValue
protectWithPoliciesOf context operands result =
  case normalizedPolicies operands of
    [] -> result
    first : remaining ->
      protectInterpretedValue
        (currentScopeLabel context)
        (first :| remaining)
        result

valueIsScopeProtected :: InterpretedValue -> Bool
valueIsScopeProtected = maybe False (const True) . interpretedScopeProtection

data ScopeHandoffDecision
  = PreserveScopeProtection
  | TransferScopeProtection
  | RejectScopeProtection
  deriving (Eq, Show)

-- | Hand a value from one lexical-scope activation to another without ever
-- exposing its payload.  Every carried policy must choose the same
-- disposition; preservation additionally requires the old label to remain in
-- the receiver's ancestry.
handoffProtectedValue
  :: ScopeActivation
  -> ScopeActivation
  -> (ScopeProtectionPolicy -> ScopeHandoffDecision)
  -> InterpretedValue
  -> InterpretedValue
handoffProtectedValue source receiver decide value =
  case interpretedScopeProtection value of
    Nothing -> value
    Just protection ->
      case authorizeProtectedValue source value of
        Left _ -> neverValue
        Right actual ->
          case nub (map decide policies) of
            [PreserveScopeProtection]
              | scopeProtectionLabel protection `elem` receiverLabels -> value
              | otherwise -> neverValue
            [TransferScopeProtection]
              | scopeProtectionLabel protection `elem` receiverLabels -> value
              | otherwise -> protectInterpretedValue
                  (currentScopeLabel receiver)
                  (scopeProtectionPolicies protection)
                  actual
            _ -> neverValue
      where
        policies = nonEmptyToList (scopeProtectionPolicies protection)
        receiverLabels = activationLabels receiver
  where
    nonEmptyToList (first :| remaining) = first : remaining

activationLabels :: ScopeActivation -> [DynamicScopeLabel]
activationLabels activation =
  scopeActivationLabel activation
    : maybe [] activationLabels (scopeActivationParent activation)

normalizedPolicies :: [InterpretedValue] -> [ScopeProtectionPolicy]
normalizedPolicies = sort . nub . concatMap policies
  where
    policies value =
      case interpretedScopeProtection value of
        Nothing -> []
        Just protection ->
          case scopeProtectionPolicies protection of
            first :| remaining -> first : remaining
