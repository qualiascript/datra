-- | Atlas-map assembly and map/range concatenation.
module Evaluation.Map
  ( makeAtlasMap
  , makeAtlasMapPreservingSingleton
  , hasConcreteSource
  , isEmptyMap
  , makeAtlasExpansion
  , concatenateValues
  , concatenateValuesWithEquivalenceView
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (..)
  , atlasMapFederationExpressionIsSingleton
  )
import DatraOrdinal (Ordinal, finiteOrdinal, ordinalLT, subtractOrdinal)
import Evaluation.Error (InterpretingError)
import Evaluation.Federation
  ( decideValueConcatenation
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
  makeAtlasMapPreservingSingleton cardinality values

-- | Construct an Atlas map while retaining a singleton outer boundary.
-- Function-body argument aggregates require this because @_it[0]@ selects the
-- first written parameter even when it is the only parameter.
makeAtlasMapPreservingSingleton
  :: Natural
  -> [InterpretedValue]
  -> InterpretedValue
makeAtlasMapPreservingSingleton cardinality values =
  makeProductMap
    SequentialProduct
    True
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
    False
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
  -> Bool
  -> Natural
  -> [InterpretedValue]
  -> ([InterpretedAtlasMapFederation]
      -> InterpretedAtlasMapFederation)
  -> InterpretedValue
makeProductMap productForm preserveSingleton cardinality values productFederation = value
  where
    -- Both sequence and expansion preserve every operand structurally.
    finalValues =
      foldl'
        appendOrdinalOrderedValues
        emptyOrdinalOrderedValues
        (map singletonOrdinalOrderedValues values)
    components =
      map interpretedSemantics values
    semantics = MapSemantics cardinality components
    valueMap = InterpretedMap cardinality finalValues
      (Right . ordinalOrderedValueAt finalValues)
      components
    memberFederations = map interpretedAtlasMapFederation values
    federation
      | preserveSingleton
      , [_] <- memberFederations = SingletonAtlasMapFederation valueMap
      | [memberFederation] <- memberFederations = memberFederation
      | all atlasMapFederationExpressionIsSingleton memberFederations =
          SingletonAtlasMapFederation valueMap
      | otherwise = productFederation memberFederations
    value =
      withOrderedAtlasMapView (makeInterpretedValue
        (composedStructuralDatraType
          (map interpretedDatraType values))
        (case productForm of
          SequentialProduct -> SequentialMapForm
          ExpansionProduct ->
            case values of
              [left, right] -> ExpansionMapForm left right
              _ -> MapForm)
        NoInsertion
        valueMap
        federation
        (if all hasConcreteSource values
              && atlasMapFederationExpressionIsSingleton federation
          then TotalInterpretedMap
          else NonTotalInterpretedMap)
        semantics)

concatenateValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
concatenateValues left right =
  fst <$> concatenateValuesWithEquivalenceView left right

-- | Evaluate concatenation and also return the same result without syntax-
-- preserving comma boundaries. The interpreter uses the latter only to decide
-- whether a written comma changes the denoted Atlas-map federation.
concatenateValuesWithEquivalenceView
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError (InterpretedValue, InterpretedValue)
concatenateValuesWithEquivalenceView sourceLeft sourceRight = do
  (result, equivalence) <- concatenateProjectedValues left right
  pure (retainCoalizedView result, retainCoalizedView equivalence)
  where
    hasCoalizedOperand =
      maybe False (const True) (interpretedCoalizedMapView sourceLeft)
        || maybe False (const True) (interpretedCoalizedMapView sourceRight)
    retainCoalizedView result
      | hasCoalizedOperand = withCoalizedMapView result result
      | otherwise = result
    left = maybe sourceLeft coalizedMapOrdinalValue
      (interpretedCoalizedMapView sourceLeft)
    right = maybe sourceRight coalizedMapOrdinalValue
      (interpretedCoalizedMapView sourceRight)

concatenateProjectedValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError (InterpretedValue, InterpretedValue)
concatenateProjectedValues left right
  | isEmptyMap left
  , hasConcreteSource right = Right (right, right)
  | isEmptyMap right
  , hasConcreteSource left = Right (left, left)
concatenateProjectedValues left right = do
  requireFederationDecision
    (decideValueConcatenation left right)
  normalizedRanges <-
    traverse canonicalizeRanges (concatenatedRanges left right)
  let insertionCapability =
        maybe
          (concatenateInsertionCapabilities left right)
          concatenateRangeCapability
          normalizedRanges
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
      checkedSourceMaps = case normalizedRanges of
        Just ranges -> map
          (interpretedMap . interpretedRangeValue)
          ranges
        Nothing -> map interpretedMap [left, right]
      baseResultMap = InterpretedMap cardinality finalValues
        (checkedMapValueAt checkedSourceMaps)
        components
      resultFederation valueMap
        | operandsAreTotal
        , atlasMapFederationExpressionIsSingleton
            (interpretedAtlasMapFederation left)
        , atlasMapFederationExpressionIsSingleton
              (interpretedAtlasMapFederation right) =
            SingletonAtlasMapFederation valueMap
        | otherwise =
            ConcatenatedAtlasMapFederation
              (interpretedAtlasMapFederation left)
              (interpretedAtlasMapFederation right)
      preserveFederationSyntax =
        isEmptyMap left
          || isEmptyMap right
          || semanticsContainsRange
            (interpretedSemantics left)
          || semanticsContainsRange
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
      makeResult valueMap federation valueSemantics =
        makeInterpretedValue
          (composedStructuralDatraType
            (map interpretedDatraType [left, right]))
          form
          insertionCapability
          valueMap
          federation
          (if operandsAreTotal
                && atlasMapFederationExpressionIsSingleton federation
            then TotalInterpretedMap
            else NonTotalInterpretedMap)
          valueSemantics
      ordinaryResult =
        makeResult resultMap (resultFederation resultMap) finalSemantics
      equivalenceResult =
        makeResult
          baseResultMap
          (resultFederation baseResultMap)
          resultSemantics
      finish result valueMap =
        preserveNamedMapView (withOrderedAtlasMapView
          (case (interpretedForm left, interpretedForm right) of
          (AsciiStringForm _, AsciiStringForm _) ->
            maybe result makeAsciiString
              (asciiStringFromInterpretedMap valueMap)
          _ -> result))
      preserveNamedMapView result =
        maybe result (`withNamedMapView` result) concatenatedNamedMapView
      concatenatedNamedMapView =
        case (namedMapViewForValue left, namedMapViewForValue right) of
          (Just leftView, Just rightView) ->
            Just (appendNamedMapViews leftView rightView)
          (Just leftView, Nothing)
            | isEmptyMap right -> Just leftView
          (Nothing, Just rightView)
            | isEmptyMap left -> Just rightView
          _ -> Nothing
  pure
    ( finish ordinaryResult resultMap
    , finish equivalenceResult baseResultMap
    )
  where
    operandsAreTotal =
      hasConcreteSource left && hasConcreteSource right

-- | Append checked ordinal callbacks with the same ordinal arithmetic used by
-- 'appendOrdinalOrderedValues'. Keeping this separate from the unchecked
-- structural view lets concatenation stay lazy without erasing a producer's
-- failure.
checkedMapValueAt
  :: [InterpretedMap]
  -> Ordinal
  -> Either InterpretingError (Maybe InterpretedValue)
checkedMapValueAt [] _ = Right Nothing
checkedMapValueAt (valueMap : remaining) position
  | position `ordinalLT` orderType =
      interpretedMapValueAtChecked valueMap position
  | otherwise = case subtractOrdinal orderType position of
      Just relative -> checkedMapValueAt remaining relative
      Nothing -> Right Nothing
  where
    orderType = interpretedMapFinalOrderType valueMap

concatenateInsertionCapabilities
  :: InterpretedValue
  -> InterpretedValue
  -> InsertionCapability
concatenateInsertionCapabilities left right =
  case
      ( interpretedInsertionCapability left
      , interpretedInsertionCapability right
      ) of
    (ValidInsertion leftInsertion, ValidInsertion rightInsertion) ->
      ValidInsertion
        (appendSomeSuperEllipsisInsertion leftInsertion rightInsertion)
    (RejectedInsertion rejection, _) -> RejectedInsertion rejection
    (_, RejectedInsertion rejection) -> RejectedInsertion rejection
    _ -> NoInsertion

isEmptyMap :: InterpretedValue -> Bool
isEmptyMap value =
  case interpretedForm value of
    SequentialMapForm ->
      interpretedMapCardinality (interpretedMap value) == 0
        && interpretedSemanticResult value == CanonicalMap 0 []
    _ -> False

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
    DependentArgumentTypeForm _ -> True
    IdentifierValueTypeForm -> True
    ToStringForm -> True
    TemplateForm _ -> True
    AssignmentForm _ -> True
    SpecificationForm _ -> True
    _ -> False

semanticsContainsRange :: ValueSemantics -> Bool
semanticsContainsRange (PresentedSemantics _ _ semantics) =
  semanticsContainsRange semantics
semanticsContainsRange (NaturalRangeSemantics _ _) = True
semanticsContainsRange (ValuedNaturalRangeSemantics _ _) = True
semanticsContainsRange (IntegerRangeSemantics _ _) = True
semanticsContainsRange (ValuedIntegerRangeSemantics _ _) = True
semanticsContainsRange (IntegerLimitRangeSemantics _ _) = True
semanticsContainsRange NaturalTypeSemantics = True
semanticsContainsRange IntegerTypeSemantics = True
semanticsContainsRange (ConcatenationSemantics members) =
  any semanticsContainsRange members
semanticsContainsRange (MapSemantics _ members) =
  any semanticsContainsRange members
semanticsContainsRange _ = False

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
