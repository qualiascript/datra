-- | Internal decision type shared by specification procedures.
module Evaluation.Specification.Decision
  ( Decision (..)
  , decideAll
  , decideAny
  , mapDecision
  , prependDecision
  ) where

data Decision proof
  = DecisionProved proof
  | DecisionRefuted
  | DecisionUndecidable

decideAll :: [Decision proof] -> Decision [proof]
decideAll decisions
  | any isRefuted decisions = DecisionRefuted
  | any isUndecidable decisions = DecisionUndecidable
  | otherwise = DecisionProved [proof | DecisionProved proof <- decisions]

decideAny :: [Decision proof] -> Decision proof
decideAny decisions =
  case [proof | DecisionProved proof <- decisions] of
    proof : _ -> DecisionProved proof
    []
      | any isUndecidable decisions -> DecisionUndecidable
      | otherwise -> DecisionRefuted

mapDecision :: (left -> right) -> Decision left -> Decision right
mapDecision transform decision =
  case decision of
    DecisionProved proof -> DecisionProved (transform proof)
    DecisionRefuted -> DecisionRefuted
    DecisionUndecidable -> DecisionUndecidable

prependDecision
  :: Decision value
  -> Decision [value]
  -> Decision [value]
prependDecision (DecisionProved value) (DecisionProved values) =
  DecisionProved (value : values)
prependDecision DecisionRefuted _ = DecisionRefuted
prependDecision _ DecisionRefuted = DecisionRefuted
prependDecision _ _ = DecisionUndecidable

isRefuted :: Decision proof -> Bool
isRefuted DecisionRefuted = True
isRefuted _ = False

isUndecidable :: Decision proof -> Bool
isUndecidable DecisionUndecidable = True
isUndecidable _ = False
