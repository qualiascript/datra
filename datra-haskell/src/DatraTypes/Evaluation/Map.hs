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
import Evaluation.Access.Federation (federationIsCoalition)
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
makeAtlasMap _ [value] = value
makeAtlasMap cardinality values =
  makeProductMap
    SequentialProduct
    cardinality
    values
    SequentialAtlasMapFederation

makeAtlasExpansion
  :: Natural
  -> [InterpretedValue]
  -> InterpretedValue
makeAtlasExpansion cardinality values =
  makeProductMap
    ExpansionProduct
    cardinality
    values
    expansionFederation
  where
    expansionFederation [left, right] =
      ExpansionAtlasMapFederation left right
    expansionFederation members = SequentialAtlasMapFederation members

data ProductForm
  = SequentialProduct
  | ExpansionProduct

makeProductMap
  :: ProductForm
  -> Natural
  -> [InterpretedValue]
  -> ([InterpretedAtlasMapFederation]
      -> InterpretedAtlasMapFederation)
  -> InterpretedValue
makeProductMap productForm cardinality values productFederation = value
  where
    -- Both sequence and expansion preserve every operand structurally. A
    -- nonempty sequence made entirely of coalitions additionally shares the
    -- canonical semantics of its explicit concatenation.
    finalValues =
      foldl'
        appendOrdinalOrderedValues
        emptyOrdinalOrderedValues
        (map singletonOrdinalOrderedValues values)
    components =
      map interpretedSemantics values
    semantics =
      case productForm of
        SequentialProduct
          | not (null memberFederations)
          , all federationIsCoalition memberFederations ->
              ConcatenationSemantics components
        _ -> MapSemantics cardinality components
    valueMap = InterpretedMap cardinality finalValues components
    memberFederations = map interpretedAtlasMapFederation values
    federation
      | [memberFederation] <- memberFederations = memberFederation
      | all atlasMapFederationExpressionIsSingleton memberFederations =
          SingletonAtlasMapFederation valueMap
      | otherwise = productFederation memberFederations
    value =
      makeInterpretedValue
        (case productForm of
          SequentialProduct -> SequentialMapForm
          ExpansionProduct ->
            case values of
              [left, right] -> ExpansionMapForm left right
              _ -> MapForm)
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
            ( canonicalRangeForm left right ranges
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
            ( ConcatenatedMapForm left right
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
          || preservesConcatenationBoundary left
          || preservesConcatenationBoundary right
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
      hasConcreteSource left && hasConcreteSource right

-- A specification retains the certified total map that originally selected
-- its target. When it is embedded in a concatenation, that concrete source is
-- still available as data even though the standalone specification itself is
-- intentionally non-total.
hasConcreteSource :: InterpretedValue -> Bool
hasConcreteSource value
  | interpretedValueHasTotalMap value = True
  | otherwise =
      case interpretedForm value of
        AssignmentForm _ -> True
        _ -> False

-- Tagged alternatives and identifier specifications are semantic components,
-- not merely the final-page entries of their representative maps. Flattening
-- those entries would erase Either injections or turn @b := 23@ into @$b, 23@.
preservesConcatenationBoundary :: InterpretedValue -> Bool
preservesConcatenationBoundary value =
  case interpretedForm value of
    EitherForm _ -> True
    IdentifierTypeForm _ -> True
    AssignmentForm _ -> True
    SpecificationForm _ -> True
    _ -> False

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

canonicalRangeForm
  :: InterpretedValue
  -> InterpretedValue
  -> [EvaluatedRange]
  -> ValueForm
canonicalRangeForm left right [valueRange]
  | atlasMapFederationExpressionIsSingleton
      (interpretedAtlasMapFederation left)
      && atlasMapFederationExpressionIsSingleton
        (interpretedAtlasMapFederation right) =
      RangeForm valueRange
canonicalRangeForm left right ranges =
  RangeConcatenationForm ranges (Just (left, right))

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
