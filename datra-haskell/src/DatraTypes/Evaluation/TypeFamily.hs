-- | The paired operations owned by every runtime Datra type family.
--
-- Keeping the two fundamental relations in one registry means adding a type
-- family cannot accidentally provide specification without subfederation (or
-- vice versa).  Recursive calls remain arguments so the family modules stay
-- independent of the central evaluators.
module Evaluation.TypeFamily
  ( SpecifyValues
  , DecideSubfederation
  , TypeFamilyOperations (..)
  , typeFamilyOperations
  ) where

import Evaluation.DatraType (DatraTypeFamily (..))
import Evaluation.Error (InterpretingError)
import Evaluation.Specification.Decision (Decision)
import Evaluation.TypeFamily.BuiltinMeta qualified as BuiltinMeta
import Evaluation.TypeFamily.Function qualified as Function
import Evaluation.TypeFamily.Structural qualified as Structural
import Evaluation.TypeFamily.TotalBlock qualified as TotalBlock
import Evaluation.Value (InterpretedValue)

type SpecifyValues =
  InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue

type DecideSubfederation =
  InterpretedValue
  -> InterpretedValue
  -> Decision ()

data TypeFamilyOperations = TypeFamilyOperations
  { specifyTypeFamily
      :: DecideSubfederation
      -> SpecifyValues
      -> SpecifyValues
  , decideTypeFamilySubfederation
      :: DecideSubfederation
      -> DecideSubfederation
  }

typeFamilyOperations :: DatraTypeFamily -> TypeFamilyOperations
typeFamilyOperations family =
  case family of
    BuiltinMetaTypeFamily kind -> TypeFamilyOperations
      { specifyTypeFamily = \decide _ ->
          BuiltinMeta.specifyBuiltinMetaType decide kind
      , decideTypeFamilySubfederation = \_ source _ ->
          BuiltinMeta.decideBuiltinMetaSubfederation source kind
      }
    FunctionTypeFamily -> TypeFamilyOperations
      { specifyTypeFamily = Function.specifyFunction
      , decideTypeFamilySubfederation =
          Function.decideFunctionSubfederation
      }
    StructuralTypeFamily -> TypeFamilyOperations
      { specifyTypeFamily = \decide specify ->
          Structural.specifyStructural specify decide
      , decideTypeFamilySubfederation =
          Structural.decideStructuralSubfederation
      }
    TotalBlockTypeFamily -> TypeFamilyOperations
      { specifyTypeFamily = \_ _ -> TotalBlock.specifyTotalBlock
      , decideTypeFamilySubfederation = \_ ->
          TotalBlock.decideTotalBlockSubfederation
      }
