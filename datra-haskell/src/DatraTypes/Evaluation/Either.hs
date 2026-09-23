-- | Disjoint federation composition for Datra's surface @|@ operator.
module Evaluation.Either
  ( makeEitherValue
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (PrimitiveAtlasMapFederation) )
import Evaluation.Value

-- | Build a non-total federation whose members come from either operand.
-- Selection supplies a Datra-Boolean injection tag; nested Eithers retain a
-- path of tags through nested 'EvaluatedEitherMember' witnesses.
makeEitherValue :: InterpretedValue -> InterpretedValue -> InterpretedValue
makeEitherValue left right =
  buildEither (eitherMembers left <> eitherMembers right)
  where
    buildEither [member] = member
    buildEither (member : members) = rawEither member (buildEither members)
    buildEither [] = rawEither left right

    eitherMembers value =
      case interpretedForm value of
        EitherForm alternatives ->
          eitherMembers (evaluatedEitherLeft alternatives)
            <> eitherMembers (evaluatedEitherRight alternatives)
        _ -> [value]

rawEither :: InterpretedValue -> InterpretedValue -> InterpretedValue
rawEither left right =
  makeInterpretedValue
    (EitherForm alternatives)
    NoInsertion
    emptyInterpretedMap
    (PrimitiveAtlasMapFederation
      (EitherAtlasMapFederation alternatives))
    NonTotalInterpretedMap
    (EitherSemantics
      (interpretedSemantics left)
      (interpretedSemantics right))
  where
    alternatives = EvaluatedEither left right
