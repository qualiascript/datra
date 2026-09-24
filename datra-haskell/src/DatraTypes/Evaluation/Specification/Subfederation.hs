-- | Central dispatch for inclusion between evaluated Datra types.
module Evaluation.Specification.Subfederation
  ( decideValueSubfederation
  ) where

import Evaluation.Specification.Decision
import Evaluation.TypeFamily.BuiltinMeta qualified as BuiltinMeta
import Evaluation.TypeFamily.Function qualified as Function
import Evaluation.TypeFamily.Structural qualified as Structural
import Evaluation.TypeFamily.TotalBlock qualified as TotalBlock
import Evaluation.Value

decideValueSubfederation
  :: InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideValueSubfederation source target
  | EitherForm alternatives <- interpretedForm source
  , isFunctionFamily source =
      decideAllEitherAlternatives alternatives target
  | EitherForm alternatives <- interpretedForm target
  , isFunctionFamily target =
      decideAnyEitherAlternative source alternatives
  | otherwise =
      case datraTypeFamily (interpretedDatraType target) of
        BuiltinMetaTypeFamily kind ->
          BuiltinMeta.decideBuiltinMetaSubfederation source kind
        FunctionTypeFamily ->
          Function.decideFunctionSubfederation
            decideValueSubfederation source target
        StructuralTypeFamily ->
          Structural.decideStructuralSubfederation
            decideValueSubfederation source target
        TotalBlockTypeFamily ->
          TotalBlock.decideTotalBlockSubfederation source target

-- Function alternatives are handled before family dispatch because the
-- enclosing Either is structural while every member has function behavior.
decideAllEitherAlternatives
  :: EvaluatedEither
  -> InterpretedValue
  -> Decision ()
decideAllEitherAlternatives source target =
  mapDecision
    (const ())
    (decideAll
      [ decideValueSubfederation (evaluatedEitherLeft source) target
      , decideValueSubfederation (evaluatedEitherRight source) target
      ])

decideAnyEitherAlternative
  :: InterpretedValue
  -> EvaluatedEither
  -> Decision ()
decideAnyEitherAlternative source target =
  decideAny
    [ decideValueSubfederation source (evaluatedEitherLeft target)
    , decideValueSubfederation source (evaluatedEitherRight target)
    ]
