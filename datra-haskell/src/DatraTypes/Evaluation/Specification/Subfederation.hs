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
  | EitherForm alternatives <- interpretedForm target
  , eitherContainsDependentSum alternatives =
      decideAny
        [ decideValueSubfederation source alternative
        | alternative <- flattenEither target
        ]
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

eitherContainsDependentSum :: EvaluatedEither -> Bool
eitherContainsDependentSum alternatives =
  any isDependentSum
    (flattenEither (evaluatedEitherLeft alternatives)
      <> flattenEither (evaluatedEitherRight alternatives))
  where
    isDependentSum value =
      case interpretedForm value of
        DependentSumForm _ -> True
        _ -> False

flattenEither :: InterpretedValue -> [InterpretedValue]
flattenEither value =
  case interpretedForm value of
    EitherForm alternatives ->
      flattenEither (evaluatedEitherLeft alternatives)
        <> flattenEither (evaluatedEitherRight alternatives)
    _ -> [value]

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
