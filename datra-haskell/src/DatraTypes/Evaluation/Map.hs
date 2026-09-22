-- | Atlas-map assembly and map/range concatenation.
module Evaluation.Map
  ( makeAtlasMap
  , makeAtlasExpansion
  , concatenateValues
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (..)
  , atlasMapFederationExpressionIsSingleton
  )
import DatraOrdinal (finiteOrdinal)
import Evaluation.Error (InterpretingError)
import Evaluation.Federation
  ( decideFederationConcatenation
  , requireFederationDecision
  )
import Evaluation.Construction (makeAsciiString)
import Evaluation.Range
  ( canonicalizeRanges
  , concatenateRangeCapability
  , interpretedRangeValue
  )
import Evaluation.Value
import Numeric.Natural (Natural)

makeAtlasMap :: Natural -> [InterpretedValue] -> InterpretedValue
makeAtlasMap _ [value]
  | SpecificationForm _ <- interpretedForm value = value
makeAtlasMap cardinality values =
  makeProductMap cardinality values SequentialAtlasMapFederation

makeAtlasExpansion
  :: Natural
  -> [InterpretedValue]
  -> InterpretedValue
makeAtlasExpansion cardinality values =
  makeProductMap cardinality values expansionFederation
  where
    expansionFederation [left, right] =
      ExpansionAtlasMapFederation left right
    expansionFederation members = SequentialAtlasMapFederation members

makeProductMap
  :: Natural
  -> [InterpretedValue]
  -> ([InterpretedAtlasMapFederation]
      -> InterpretedAtlasMapFederation)
  -> InterpretedValue
makeProductMap cardinality values productFederation = value
  where
    finalValues =
      foldl'
        appendOrdinalOrderedValues
        emptyOrdinalOrderedValues
        (map (interpretedMapFinalValues . interpretedMap) values)
    components =
      concatMap (interpretedMapComponents . interpretedMap) values
    semantics = MapSemantics cardinality components
    valueMap = InterpretedMap cardinality finalValues components
    memberFederations = map interpretedAtlasMapFederation values
    federation
      | [memberFederation] <- memberFederations = memberFederation
      | all atlasMapFederationExpressionIsSingleton memberFederations =
          SingletonAtlasMapFederation valueMap
      | otherwise = productFederation memberFederations
    value =
      makeInterpretedValue
        MapForm
        NoInsertion
        valueMap
        federation
        (if all interpretedValueHasTotalMap values
              && atlasMapFederationExpressionIsSingleton federation
          then TotalInterpretedMap
          else NonTotalInterpretedMap)
        semantics

concatenateValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
concatenateValues left right = do
  requireFederationDecision
    (decideFederationConcatenation
      (interpretedAtlasMapFederation left)
      (interpretedAtlasMapFederation right))
  normalizedRanges <-
    traverse canonicalizeRanges (concatenatedRanges left right)
  let insertionCapability =
        maybe NoInsertion concatenateRangeCapability normalizedRanges
      (form, finalValues, components, semantics) =
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
            , [rangeSemantics ranges]
            , rangeSemantics ranges
            )
          Nothing ->
            ( MapForm
            , appendOrdinalOrderedValues
                (interpretedMapFinalValues (interpretedMap left))
                (interpretedMapFinalValues (interpretedMap right))
            , interpretedMapComponents (interpretedMap left)
                <> interpretedMapComponents (interpretedMap right)
            , MapSemantics
                2
                ( interpretedMapComponents (interpretedMap left)
                    <> interpretedMapComponents (interpretedMap right)
                )
            )
      cardinality
        | ordinalOrderedValuesOrderType finalValues == finiteOrdinal 0 = 0
        | otherwise = 2
      resultSemantics =
        case semantics of
          MapSemantics _ mapComponents ->
            MapSemantics cardinality mapComponents
          _ -> semantics
      baseResultMap = InterpretedMap cardinality finalValues components
      resultFederation
        | atlasMapFederationExpressionIsSingleton
            (interpretedAtlasMapFederation left)
            && atlasMapFederationExpressionIsSingleton
              (interpretedAtlasMapFederation right) =
            SingletonAtlasMapFederation resultMap
        | otherwise =
            ConcatenatedAtlasMapFederation
              (interpretedAtlasMapFederation left)
              (interpretedAtlasMapFederation right)
      preserveFederationSyntax =
        semanticsContainsNaturalRange
          (interpretedSemantics left)
          || semanticsContainsNaturalRange
            (interpretedSemantics right)
      preservedSemantics =
        ConcatenationSemantics
          (concatenationMembers
            (interpretedSemantics left)
            <> concatenationMembers (interpretedSemantics right))
      finalSemantics
        | preserveFederationSyntax = preservedSemantics
        | otherwise = resultSemantics
      resultMap
        | preserveFederationSyntax =
            baseResultMap
              { interpretedMapComponents = [preservedSemantics] }
        | otherwise = baseResultMap
      ordinaryResult =
        makeInterpretedValue
          form
          insertionCapability
          resultMap
          resultFederation
          (if operandsAreTotal
                && atlasMapFederationExpressionIsSingleton resultFederation
            then TotalInterpretedMap
            else NonTotalInterpretedMap)
          finalSemantics
  pure
    (case (interpretedForm left, interpretedForm right) of
      (AsciiStringForm _, AsciiStringForm _) ->
        maybe ordinaryResult makeAsciiString
          (asciiStringFromInterpretedMap resultMap)
      _ -> ordinaryResult)
  where
    operandsAreTotal =
      isTotal left && isTotal right
    isTotal = interpretedValueHasTotalMap

semanticsContainsNaturalRange :: ValueSemantics -> Bool
semanticsContainsNaturalRange (NaturalRangeSemantics _ _) = True
semanticsContainsNaturalRange (ValuedNaturalRangeSemantics _ _) = True
semanticsContainsNaturalRange NaturalTypeSemantics = True
semanticsContainsNaturalRange (ConcatenationSemantics members) =
  any semanticsContainsNaturalRange members
semanticsContainsNaturalRange (MapSemantics _ members) =
  any semanticsContainsNaturalRange members
semanticsContainsNaturalRange _ = False

concatenationMembers :: ValueSemantics -> [ValueSemantics]
concatenationMembers (ConcatenationSemantics members) = members
concatenationMembers value = [value]

canonicalRangeForm :: [EvaluatedRange] -> ValueForm
canonicalRangeForm [valueRange] = RangeForm valueRange
canonicalRangeForm ranges = RangeConcatenationForm ranges

rangeSemantics :: [EvaluatedRange] -> ValueSemantics
rangeSemantics [valueRange] = RangeSemantics (rangeDescription valueRange)
rangeSemantics ranges =
  RangeConcatenationSemantics (map rangeDescription ranges)

concatenatedRanges
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe [EvaluatedRange]
concatenatedRanges left right = do
  leftRanges <- valueRanges left
  rightRanges <- valueRanges right
  pure (leftRanges <> rightRanges)
