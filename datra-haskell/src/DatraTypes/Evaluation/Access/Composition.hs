-- | Access decisions for constructed Atlas-map federations.
module Evaluation.Access.Composition
  ( FederationAccess (..)
  , accessMapFor
  , decideFederationAccess
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (..)
  )
import Data.Either (isRight)
import Data.List (sortOn)
import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  , naturalAtOrdinal
  , omegaPower
  , ordinalLT
  )
import Evaluation.Access.Federation
import Evaluation.Access.RangeSelection
  ( DescribedRange (describedRangeDescription)
  , accessSelection
  )
import Evaluation.Error
import Evaluation.Value
import MapOperators.AccessOperator (validateAccessSelection)
import SuperEllipsisInsertion
  ( someSuperEllipsisInsertionOrderType
  , someSuperEllipsisInsertionPositionAt
  , someSuperEllipsisInsertionRank
  )
import SuperEllipsisRange.Description qualified as RangeDescription

decideFederationAccess
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError FederationAccess
decideFederationAccess mapValue insertionValue =
  case decideAtomicFederationAccess mapValue insertionValue of
    Just decision -> decision
    Nothing -> decideCompositeFederationAccess mapValue insertionValue

decideCompositeFederationAccess
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError FederationAccess
decideCompositeFederationAccess mapValue insertionValue = do
  insertion <- requireInsertion insertionValue
  if someSuperEllipsisInsertionOrderType insertion == finiteOrdinal 0
    then Right EmptyFederationAccess
    else
      case interpretedAtlasMapFederation mapValue of
        SequentialAtlasMapFederation _ ->
          decideDirectFederationAccess insertionValue
        ConcatenatedAtlasMapFederation _ _ ->
          decideFlattenedFederationAccess mapValue insertionValue insertion
        ExpansionAtlasMapFederation _ _ ->
          decideFlattenedFederationAccess mapValue insertionValue insertion
        SingletonAtlasMapFederation _ ->
          decideDirectFederationAccess insertionValue
        PrimitiveAtlasMapFederation _ ->
          undecidableAccess

decideFlattenedFederationAccess
  :: InterpretedValue
  -> InterpretedValue
  -> SomeSuperEllipsisInsertion
  -> Either InterpretingError FederationAccess
decideFlattenedFederationAccess mapValue insertionValue insertion
  | federationHasKnownEmptyMap
      (interpretedAtlasMapFederation mapValue) =
      emptyMapAccessCounterexample
  | selectionCoveredByRegions
      (accessLayoutAccessibleRegions (accessLayout mapValue))
      insertionValue
      insertion =
      case naturalRangeFederation insertionValue of
        Just selectionRange ->
          Right (NaturalRangeSelectionAccess selectionRange)
        Nothing -> Right (SingletonFederationAccess insertion)
  | otherwise = undecidableAccess

-- | Compose atomic layouts through retained evaluation structure. This is the
-- single lifting point for flattened access: extending 'atomicAccessLayout'
-- automatically extends concatenations and expansions built from that leaf.
accessLayout :: InterpretedValue -> AccessLayout
accessLayout value =
  case atomicAccessLayout value of
    Just layout -> layout
    Nothing ->
      case interpretedForm value of
        SequentialMapForm -> fixedLayout (interpretedMap value)
        ConcatenatedMapForm left right -> combinedLayout left right
        RangeConcatenationForm _ (Just (left, right)) ->
          combinedLayout left right
        ExpansionMapForm left right -> combinedLayout left right
        _ ->
          AccessLayout
            { accessLayoutRepresentativeMap = interpretedMap value
            , accessLayoutFixedOrderType = Nothing
            , accessLayoutAccessibleRegions = []
            }
  where
    fixedLayout valueMap =
      let orderType = interpretedMapFinalOrderType valueMap
      in AccessLayout valueMap (Just orderType) (fullRegion orderType)

    combinedLayout left right =
      let leftLayout = accessLayout left
          rightLayout = accessLayout right
          representativeMap =
            appendAccessMaps
              (accessLayoutRepresentativeMap leftLayout)
              (accessLayoutRepresentativeMap rightLayout)
          fixedOrderType =
            addOrdinals
              <$> accessLayoutFixedOrderType leftLayout
              <*> accessLayoutFixedOrderType rightLayout
          accessibleRegions =
            case accessLayoutFixedOrderType leftLayout of
              Just leftOrderType ->
                accessLayoutAccessibleRegions leftLayout
                  <> map
                    (translateRegion leftOrderType)
                    (accessLayoutAccessibleRegions rightLayout)
              Nothing ->
                accessLayoutAccessibleRegions leftLayout
      in AccessLayout representativeMap fixedOrderType accessibleRegions

    fullRegion orderType
      | orderType == finiteOrdinal 0 = []
      | otherwise =
          [AccessibleOrdinalRegion (finiteOrdinal 0) orderType]

    translateRegion offset region =
      AccessibleOrdinalRegion
        (addOrdinals offset (accessibleRegionLowerBound region))
        (addOrdinals offset (accessibleRegionUpperBound region))

accessMapFor :: InterpretedValue -> InterpretedMap
accessMapFor = accessLayoutRepresentativeMap . accessLayout

appendAccessMaps :: InterpretedMap -> InterpretedMap -> InterpretedMap
appendAccessMaps left right =
  InterpretedMap
    (if finalOrderType == finiteOrdinal 0 then 0 else 2)
    finalValues
    (interpretedMapComponents left <> interpretedMapComponents right)
  where
    finalValues =
      appendOrdinalOrderedValues
        (interpretedMapFinalValues left)
        (interpretedMapFinalValues right)
    finalOrderType = ordinalOrderedValuesOrderType finalValues

selectionCoveredByRegions
  :: [AccessibleOrdinalRegion]
  -> InterpretedValue
  -> SomeSuperEllipsisInsertion
  -> Bool
selectionCoveredByRegions regions selectionValue insertion =
  case accessSelection selectionValue of
    Just describedRanges ->
      all describedRangeIsCovered describedRanges
    Nothing -> insertionCoveredByRegions regions insertion
  where
    describedRangeIsCovered described =
      case RangeDescription.rangeDescriptionImageBounds
          (describedRangeDescription described) of
        Nothing -> True
        Just bounds -> intervalIsCovered regions bounds

insertionCoveredByRegions
  :: [AccessibleOrdinalRegion]
  -> SomeSuperEllipsisInsertion
  -> Bool
insertionCoveredByRegions regions insertion =
  case naturalAtOrdinal (someSuperEllipsisInsertionOrderType insertion) of
    Just cardinality -> all selectedPositionIsAccessible (positions cardinality)
    Nothing ->
      isRight
        (validateAccessSelection
          (omegaPower (someSuperEllipsisInsertionRank insertion))
          (someSuperEllipsisInsertionOrderType insertion)
          (accessiblePrefixOrderType regions)
          (someSuperEllipsisInsertionPositionAt insertion))
  where
    selectedPositionIsAccessible position =
      case someSuperEllipsisInsertionPositionAt
          insertion
          (finiteOrdinal position) of
        Nothing -> True
        Just selected -> any (regionContains selected) regions

    regionContains position region =
      not (ordinalLT position (accessibleRegionLowerBound region))
        && ordinalLT position (accessibleRegionUpperBound region)

    positions 0 = []
    positions cardinality = [0 .. cardinality - 1]

intervalIsCovered
  :: [AccessibleOrdinalRegion]
  -> (Ordinal, Ordinal)
  -> Bool
intervalIsCovered regions (lower, upper) =
  go lower (sortOn accessibleRegionLowerBound regions)
  where
    go coveredUntil _
      | not (ordinalLT coveredUntil upper) = True
    go _ [] = False
    go coveredUntil (region : remaining)
      | not (ordinalLT
          coveredUntil
          (accessibleRegionUpperBound region)) =
          go coveredUntil remaining
      | ordinalLT coveredUntil (accessibleRegionLowerBound region) = False
      | otherwise =
          go
            (max coveredUntil (accessibleRegionUpperBound region))
            remaining

accessiblePrefixOrderType :: [AccessibleOrdinalRegion] -> Ordinal
accessiblePrefixOrderType =
  go (finiteOrdinal 0) . sortOn accessibleRegionLowerBound
  where
    go prefix [] = prefix
    go prefix (region : remaining)
      | ordinalLT prefix (accessibleRegionLowerBound region) = prefix
      | otherwise =
          go (max prefix (accessibleRegionUpperBound region)) remaining

-- NaturalRange contains the empty map. A flattened construction whose every
-- operand can be empty also contains an empty map, refuting nonempty access.
federationHasKnownEmptyMap :: InterpretedAtlasMapFederation -> Bool
federationHasKnownEmptyMap federation =
  case federation of
    PrimitiveAtlasMapFederation (NaturalRangeAtlasMapFederation _) -> True
    ConcatenatedAtlasMapFederation left right ->
      federationHasKnownEmptyMap left && federationHasKnownEmptyMap right
    ExpansionAtlasMapFederation left right ->
      federationHasKnownEmptyMap left && federationHasKnownEmptyMap right
    _ -> False

undecidableAccess :: Either InterpretingError result
undecidableAccess =
  Left
    (AtlasMapFederationOperationUndecidable
      (NoAtlasMapFederationDecisionProcedure AtlasMapFederationAccess))
