-- | Fundamental typing operations for retained begin/yield blocks.
module Evaluation.TypeFamily.TotalBlock
  ( specifyTotalBlock
  , decideTotalBlockSubfederation
  ) where

import Evaluation.Error
  ( AtlasMapFederationRefutation
      (AtlasMapFederationSpecificationHasNoMatchingMember)
  , InterpretingError
      (AtlasMapFederationOperationRefuted)
  )
import Evaluation.Specification.Decision (Decision (..))
import Evaluation.Value

specifyTotalBlock
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
specifyTotalBlock source target
  | interpretedCanonicalResult source == interpretedCanonicalResult target =
      -- Prefer the block presentation so its canonical rendering continues
      -- to retain both the block and its yielded value.
      Right target
  | otherwise = Left
      (AtlasMapFederationOperationRefuted
        AtlasMapFederationSpecificationHasNoMatchingMember)

decideTotalBlockSubfederation
  :: InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideTotalBlockSubfederation source target
  | interpretedCanonicalResult source == interpretedCanonicalResult target =
      DecisionProved ()
  | otherwise = DecisionRefuted
