-- | Central dispatch for inclusion between evaluated Datra types.
module Evaluation.Specification.Subfederation
  ( decideValueSubfederation
  ) where

import Evaluation.Specification.Decision
import Evaluation.TypeFamily
  ( TypeFamilyOperations (decideTypeFamilySubfederation)
  , typeFamilyOperations
  )
import Evaluation.Value

decideValueSubfederation
  :: InterpretedValue
  -> InterpretedValue
  -> Decision ()
decideValueSubfederation source target
  | DependentSumForm dependent <- interpretedForm target =
      case evaluatedDependentSumSpecify dependent source of
        Right _ -> DecisionProved ()
        Left _ -> DecisionRefuted
  | EitherForm alternatives <- interpretedForm source
  , isFunctionFamily source =
      decideAllEitherAlternatives alternatives target
  | EitherForm alternatives <- interpretedForm target
  , isFunctionFamily target =
      decideAnyEitherAlternative source alternatives
  | otherwise =
      decideTypeFamilySubfederation
        (typeFamilyOperations
          (datraTypeFamily (interpretedDatraType target)))
        decideValueSubfederation
        source
        target

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
