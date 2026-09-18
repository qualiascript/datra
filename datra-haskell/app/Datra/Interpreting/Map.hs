-- | Syntax-sensitive Atlas-map assembly.
module Datra.Interpreting.Map
  ( interpretAtlasMapWith
  ) where

import Datra.AST (Expression (..))
import DatraTypes
  ( InterpretedValue
  , InterpretingError
  , interpretedMap
  , interpretedMapCardinality
  , makeAtlasMap
  )
import Numeric.Natural (Natural)

interpretAtlasMapWith
  :: (Expression -> Either InterpretingError InterpretedValue)
  -> [Expression]
  -> Either InterpretingError InterpretedValue
interpretAtlasMapWith interpret expressions = do
  values <- traverse interpret expressions
  let nestingDepths =
        zipWith expressionNestingDepth expressions values
      mapDepth
        | null expressions = 0
        | otherwise = 1 + maximum nestingDepths
      cardinality
        | mapDepth == 0 = 0
        | otherwise = mapDepth + 1
  pure (makeAtlasMap cardinality values)

expressionNestingDepth :: Expression -> InterpretedValue -> Natural
expressionNestingDepth expressionValue value =
  case expressionValue of
    AtlasMap _ ->
      let cardinality = interpretedMapCardinality (interpretedMap value)
      in if cardinality == 0 then 0 else cardinality - 1
    _ -> 0
