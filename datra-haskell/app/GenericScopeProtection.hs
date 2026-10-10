-- | The scope-protection policy used by generic sums.  The shared substrate
-- deliberately knows nothing about why this policy is introduced or which
-- future operations may eliminate it.
module GenericScopeProtection
  ( protectGenericExistential
  , genericOperationResultDecision
  , genericContinuationHandoff
  , genericDomainToBodyHandoff
  , genericFunctionReturnHandoff
  ) where

import Data.List.NonEmpty (NonEmpty (..))
import DatraTypes
import ScopeProtection

protectGenericExistential
  :: DynamicScopeLabel
  -> InterpretedValue
  -> InterpretedValue
protectGenericExistential label =
  protectInterpretedValue label (GenericExistentialProtection :| [])

genericOperationResultDecision
  :: ScopeProtectionPolicy
  -> InterpretedValue
  -> Decision ()
genericOperationResultDecision GenericExistentialProtection =
  decideClosedPublicResultContract

genericContinuationHandoff
  :: ScopeProtectionPolicy
  -> ScopeHandoffDecision
genericContinuationHandoff GenericExistentialProtection =
  TransferScopeProtection

genericDomainToBodyHandoff
  :: ScopeProtectionPolicy
  -> ScopeHandoffDecision
genericDomainToBodyHandoff GenericExistentialProtection =
  TransferScopeProtection

genericFunctionReturnHandoff
  :: ScopeProtectionPolicy
  -> ScopeHandoffDecision
genericFunctionReturnHandoff GenericExistentialProtection =
  PreserveScopeProtection
