-- | The scope-protection policy used by generic sums.  The shared substrate
-- deliberately knows nothing about why this policy is introduced or which
-- future operations may eliminate it.
module GenericScopeProtection
  ( protectGenericExistential
  ) where

import Data.List.NonEmpty (NonEmpty (..))
import DatraTypes

protectGenericExistential
  :: DynamicScopeLabel
  -> InterpretedValue
  -> InterpretedValue
protectGenericExistential label =
  protectInterpretedValue label (GenericExistentialProtection :| [])
