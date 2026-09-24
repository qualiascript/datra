-- | Structural Datra-type relations.
--
-- Specification and subfederation are separate responsibilities, re-exported
-- here to keep the existing family-level API stable.
module Evaluation.TypeFamily.Structural
  ( assignIdentifierValues
  , decideStructuralSubfederation
  , specifyStructural
  ) where

import Evaluation.TypeFamily.Structural.Specification
  ( assignIdentifierValues
  , specifyStructural
  )
import Evaluation.TypeFamily.Structural.Subfederation
  ( decideStructuralSubfederation
  )
