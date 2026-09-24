-- | Argument maps are unions of ordered maps. Distribute optional names and
-- other Either slots before permuting, so repeated unnamed alternatives are
-- identified instead of being assigned artificial distinguishing tags.
module Evaluation.Arguments
  ( makeArgumentMap
  , makeDistinctUnion
  , argumentAlternatives
  ) where

import Control.Monad (foldM)
import Data.List (nubBy, permutations)
import Evaluation.Either (makeEitherValue)
import Evaluation.Error (InterpretingError)
import Evaluation.Map (makeAtlasMap, hasConcreteSource)
import Evaluation.Access.Federation (federationIsCoalition)
import Evaluation.Value

makeArgumentMap :: [InterpretedValue] -> Either InterpretingError InterpretedValue
makeArgumentMap [] = Right (makeAtlasMap 0 [])
makeArgumentMap [value] = Right value
makeArgumentMap members = do
  union <- makeDistinctUnion
    [ makeAtlasMap 2 ordering
    | choices <- sequence (map argumentAlternatives members)
    , ordering <- permutations choices
    ]
  pure
    (makeInterpretedValue
      (ArgumentMapForm members union)
      NoInsertion
      (interpretedMap union)
      (interpretedAtlasMapFederation union)
      (if interpretedValueHasTotalMap union
        then TotalInterpretedMap else NonTotalInterpretedMap)
      (ArgumentMapSemantics
        (all totalPage members) (map interpretedSemantics members)))
  where
    totalPage member =
      hasConcreteSource member
        || federationIsCoalition (interpretedAtlasMapFederation member)

-- The existing Either constructor still checks separation between different
-- members. Only identical alternatives are removed here.
makeDistinctUnion
  :: [InterpretedValue] -> Either InterpretingError InterpretedValue
makeDistinctUnion values =
  case nubBy sameValue (concatMap argumentAlternatives values) of
    [] -> Right (makeAtlasMap 0 [])
    first : rest -> foldM makeEitherValue first rest
  where
    sameValue left right =
      interpretedCanonicalResult left == interpretedCanonicalResult right

argumentAlternatives :: InterpretedValue -> [InterpretedValue]
argumentAlternatives value =
  case interpretedForm value of
    EitherForm alternatives ->
      argumentAlternatives (evaluatedEitherLeft alternatives)
        <> argumentAlternatives (evaluatedEitherRight alternatives)
    _ -> [value]
