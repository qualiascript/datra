-- | Atlas-map assembly and map/range concatenation.
module Evaluation.Map
  ( makeAtlasMap
  , concatenateValues
  ) where

import DatraOrdinal (finiteOrdinal)
import DatraLanguage.Diagnostics.Interpreter (InterpretingError)
import Evaluation.Range
  ( canonicalizeRanges
  , concatenateRangeCapability
  , interpretedRangeValue
  )
import Evaluation.Value
import Numeric.Natural (Natural)

makeAtlasMap :: Natural -> [InterpretedValue] -> InterpretedValue
makeAtlasMap cardinality values =
  InterpretedValue
    MapForm
    NoInsertion
    (InterpretedMap cardinality finalValues components)
    canonical
  where
    finalValues =
      foldl'
        appendOrdinalOrderedValues
        emptyOrdinalOrderedValues
        (map (interpretedMapFinalValues . interpretedMap) values)
    components =
      concatMap (interpretedMapComponents . interpretedMap) values
    canonical = CanonicalMap cardinality components

concatenateValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
concatenateValues left right = do
  normalizedRanges <-
    traverse canonicalizeRanges (concatenatedRanges left right)
  let insertionCapability =
        maybe NoInsertion concatenateRangeCapability normalizedRanges
      (form, finalValues, components, canonical) =
        case normalizedRanges of
          Just ranges ->
            ( canonicalRangeForm ranges
            , foldl'
                appendOrdinalOrderedValues
                emptyOrdinalOrderedValues
                (map
                  (interpretedMapFinalValues
                    . interpretedMap
                    . interpretedRangeValue)
                  ranges)
            , [canonicalRanges ranges]
            , canonicalRanges ranges
            )
          Nothing ->
            ( MapForm
            , appendOrdinalOrderedValues
                (interpretedMapFinalValues (interpretedMap left))
                (interpretedMapFinalValues (interpretedMap right))
            , interpretedMapComponents (interpretedMap left)
                <> interpretedMapComponents (interpretedMap right)
            , CanonicalMap
                2
                ( interpretedMapComponents (interpretedMap left)
                    <> interpretedMapComponents (interpretedMap right)
                )
            )
      cardinality
        | ordinalOrderedValuesOrderType finalValues == finiteOrdinal 0 = 0
        | otherwise = 2
      resultCanonical =
        case canonical of
          CanonicalMap _ mapComponents ->
            CanonicalMap cardinality mapComponents
          _ -> canonical
  pure
    (InterpretedValue
      form
      insertionCapability
      (InterpretedMap cardinality finalValues components)
      resultCanonical)

canonicalRangeForm :: [EvaluatedRange] -> ValueForm
canonicalRangeForm [valueRange] = RangeForm valueRange
canonicalRangeForm ranges = RangeConcatenationForm ranges

canonicalRanges :: [EvaluatedRange] -> CanonicalResult
canonicalRanges [valueRange] = CanonicalRange (rangeDescription valueRange)
canonicalRanges ranges =
  CanonicalRangeConcatenation (map rangeDescription ranges)

concatenatedRanges
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe [EvaluatedRange]
concatenatedRanges left right = do
  leftRanges <- valueRanges left
  rightRanges <- valueRanges right
  pure (leftRanges <> rightRanges)
