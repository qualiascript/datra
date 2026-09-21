-- | Atlas-map assembly and map/range concatenation.
module Evaluation.Map
  ( makeAtlasMap
  , makeAtlasExpansion
  , concatenateValues
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationDecision (..)
  , AtlasMapFederationExpression (..)
  , atlasMapFederationExpressionIsSingleton
  )
import DatraOrdinal (finiteOrdinal)
import DatraLanguage.Diagnostics.Interpreter
  ( AtlasMapFederationOperation (AtlasMapFederationConcatenation)
  , AtlasMapFederationRefutation
      (AtlasMapFederationConcatenationCollision)
  , AtlasMapFederationUncertainty
      (NoAtlasMapFederationDecisionProcedure)
  , InterpretingError (..)
  )
import Evaluation.Construction (makeAsciiString)
import Evaluation.Range
  ( canonicalizeRanges
  , concatenateRangeCapability
  , interpretedRangeValue
  )
import Evaluation.Value
import Numeric.Natural (Natural)
import NaturalRange qualified
import ValuedNaturalRange qualified

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
    canonical = CanonicalMap cardinality components
    valueMap = InterpretedMap cardinality finalValues components
    memberFederations = map interpretedAtlasMapFederation values
    federation
      | [memberFederation] <- memberFederations = memberFederation
      | all atlasMapFederationExpressionIsSingleton memberFederations =
          SingletonAtlasMapFederation valueMap
      | otherwise = productFederation memberFederations
    value =
      InterpretedValue
        { interpretedForm = MapForm
        , interpretedInsertionCapability = NoInsertion
        , interpretedMap = valueMap
        , interpretedAtlasMapFederation = federation
        , interpretedTotalAtlasMap =
            if all hasTotalMap values
                && atlasMapFederationExpressionIsSingleton federation
              then Just (InterpretedTotalAtlasMap valueMap)
              else Nothing
        , interpretedCanonicalResult = canonical
        }
    hasTotalMap = maybe False (const True) . interpretedTotalAtlasMap

concatenateValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
concatenateValues left right = do
  case decideFederationConcatenation
      (interpretedAtlasMapFederation left)
      (interpretedAtlasMapFederation right) of
    AtlasMapFederationRefuted refutation ->
      Left (AtlasMapFederationOperationRefuted refutation)
    AtlasMapFederationUndecidable uncertainty ->
      Left (AtlasMapFederationOperationUndecidable uncertainty)
    AtlasMapFederationProved () -> pure ()
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
        canonicalContainsNaturalRange
          (interpretedCanonicalResult left)
          || canonicalContainsNaturalRange
            (interpretedCanonicalResult right)
      preservedCanonical =
        CanonicalConcatenation
          (canonicalConcatenationMembers
            (interpretedCanonicalResult left)
            <> canonicalConcatenationMembers
              (interpretedCanonicalResult right))
      finalCanonical
        | preserveFederationSyntax = preservedCanonical
        | otherwise = resultCanonical
      resultMap
        | preserveFederationSyntax =
            baseResultMap
              { interpretedMapComponents = [preservedCanonical] }
        | otherwise = baseResultMap
      ordinaryResult =
        InterpretedValue
          { interpretedForm = form
          , interpretedInsertionCapability = insertionCapability
          , interpretedMap = resultMap
          , interpretedAtlasMapFederation = resultFederation
          , interpretedTotalAtlasMap =
              if operandsAreTotal
                  && atlasMapFederationExpressionIsSingleton resultFederation
                then Just (InterpretedTotalAtlasMap resultMap)
                else Nothing
          , interpretedCanonicalResult = finalCanonical
          }
  pure
    (case (interpretedForm left, interpretedForm right) of
      (AsciiStringForm _, AsciiStringForm _) ->
        maybe ordinaryResult makeAsciiString
          (asciiStringFromInterpretedMap resultMap)
      _ -> ordinaryResult)
  where
    operandsAreTotal =
      isTotal left && isTotal right
    isTotal = maybe False (const True) . interpretedTotalAtlasMap

decideFederationConcatenation
  :: InterpretedAtlasMapFederation
  -> InterpretedAtlasMapFederation
  -> AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
decideFederationConcatenation left right
  | atlasMapFederationExpressionIsSingleton left =
      AtlasMapFederationProved ()
  | atlasMapFederationExpressionIsSingleton right =
      AtlasMapFederationProved ()
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (NaturalRangeAtlasMapFederation
        (EvaluatedNaturalRange leftRange)))
    (PrimitiveAtlasMapFederation
      (NaturalRangeAtlasMapFederation
        (EvaluatedNaturalRange rightRange))) =
  case NaturalRange.naturalRangeOverlapWitness leftRange rightRange of
    Nothing -> AtlasMapFederationProved ()
    Just witness ->
      AtlasMapFederationRefuted
        (AtlasMapFederationConcatenationCollision witness)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (ValuedNaturalRangeAtlasMapFederation
        (EvaluatedValuedNaturalRange leftRange)))
    (PrimitiveAtlasMapFederation
      (ValuedNaturalRangeAtlasMapFederation
        (EvaluatedValuedNaturalRange rightRange))) =
  overlapDecision
    (ValuedNaturalRange.valuedNaturalRangesOverlapWitness
      leftRange rightRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (NaturalRangeAtlasMapFederation
        (EvaluatedNaturalRange naturalRange)))
    (PrimitiveAtlasMapFederation
      (ValuedNaturalRangeAtlasMapFederation
        (EvaluatedValuedNaturalRange valuedRange))) =
  overlapDecision
    (ValuedNaturalRange.valuedNaturalRangeOverlapNaturalRange
      valuedRange naturalRange)
decideFederationConcatenation
    (PrimitiveAtlasMapFederation
      (ValuedNaturalRangeAtlasMapFederation
        (EvaluatedValuedNaturalRange valuedRange)))
    (PrimitiveAtlasMapFederation
      (NaturalRangeAtlasMapFederation
        (EvaluatedNaturalRange naturalRange))) =
  overlapDecision
    (ValuedNaturalRange.valuedNaturalRangeOverlapNaturalRange
      valuedRange naturalRange)
decideFederationConcatenation _ _ =
  AtlasMapFederationUndecidable
    (NoAtlasMapFederationDecisionProcedure
      AtlasMapFederationConcatenation)

overlapDecision
  :: Maybe Natural
  -> AtlasMapFederationDecision
       AtlasMapFederationRefutation
       AtlasMapFederationUncertainty
       ()
overlapDecision Nothing = AtlasMapFederationProved ()
overlapDecision (Just witness) =
  AtlasMapFederationRefuted
    (AtlasMapFederationConcatenationCollision witness)

canonicalContainsNaturalRange :: CanonicalResult -> Bool
canonicalContainsNaturalRange (CanonicalNaturalRange _ _) = True
canonicalContainsNaturalRange (CanonicalValuedNaturalRange _ _) = True
canonicalContainsNaturalRange CanonicalNaturalType = True
canonicalContainsNaturalRange (CanonicalConcatenation members) =
  any canonicalContainsNaturalRange members
canonicalContainsNaturalRange (CanonicalMap _ members) =
  any canonicalContainsNaturalRange members
canonicalContainsNaturalRange _ = False

canonicalConcatenationMembers :: CanonicalResult -> [CanonicalResult]
canonicalConcatenationMembers (CanonicalConcatenation members) = members
canonicalConcatenationMembers value = [value]

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
