-- | Checked access through an evaluated insertion capability.
module Evaluation.Access
  ( accessValues
  ) where

import DatraOrdinal
  ( finiteOrdinal
  , naturalAtOrdinal
  , omegaPower
  )
import Data.Bifunctor qualified as Bifunctor
import DatraLanguage.Diagnostics.Interpreter (InterpretingError (..))
import Evaluation.Construction (makeAsciiString)
import Evaluation.Value
import NaturalRange qualified
import MapOperators.AccessOperator
  ( validateAccessSelection )
import SuperEllipsisInsertion
  ( eraseSuperEllipsisInsertion
  , someSuperEllipsisInsertionOrderType
  , someSuperEllipsisInsertionPositionAt
  , someSuperEllipsisInsertionRank
  )
import SuperEllipsisRange qualified as Range

accessValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
accessValues mapValue insertionValue =
  case interpretedForm insertionValue of
    NaturalRangeForm naturalRange ->
      accessNaturalRange mapValue naturalRange
    _ -> do
      insertion <- requireInsertion insertionValue
      accessWithInsertion mapValue insertion

accessNaturalRange
  :: InterpretedValue
  -> EvaluatedNaturalRange
  -> Either InterpretingError InterpretedValue
accessNaturalRange mapValue (EvaluatedNaturalRange valueRange) =
  case NaturalRange.naturalSubrangeEllipsisRange selectedRange $ \range ->
      accessWithInsertion
        mapValue
        (eraseSuperEllipsisInsertion
          (Range.superEllipsisRangeInsertion range)) of
    Just result -> result
    Nothing -> finishAccess mapValue emptyInterpretedMap
  where
    sourceOrderType =
      interpretedMapFinalOrderType (interpretedMap mapValue)
    selectedRange =
      case naturalAtOrdinal sourceOrderType of
        Just finiteLimit ->
          NaturalRange.naturalRangeLargestSubrangeBelow
            valueRange finiteLimit
        Nothing -> NaturalRange.naturalRangeFullSubrange valueRange

accessWithInsertion
  :: InterpretedValue
  -> SomeSuperEllipsisInsertion
  -> Either InterpretingError InterpretedValue
accessWithInsertion mapValue insertion = do
  selected <- accessMap (interpretedMap mapValue) insertion
  finishAccess mapValue selected

finishAccess
  :: InterpretedValue
  -> InterpretedMap
  -> Either InterpretingError InterpretedValue
finishAccess mapValue selected =
  let ordinaryResult =
        InterpretedValue
          MapForm
          NoInsertion
          selected
          (CanonicalMap
            (interpretedMapCardinality selected)
            (interpretedMapComponents selected))
  in pure
    (case interpretedForm mapValue of
      AsciiStringForm _ ->
        maybe ordinaryResult makeAsciiString
          (asciiStringFromInterpretedMap selected)
      _ -> ordinaryResult)

requireInsertion
  :: InterpretedValue
  -> Either InterpretingError SomeSuperEllipsisInsertion
requireInsertion value =
  case interpretedInsertionCapability value of
    NoInsertion ->
      Left (ExpectedInsertionOperand (interpretedValueKind value))
    RejectedInsertion rejection ->
      Left (RangeConcatenationRejected rejection)
    ValidInsertion insertion -> Right insertion

accessMap
  :: InterpretedMap
  -> SomeSuperEllipsisInsertion
  -> Either InterpretingError InterpretedMap
accessMap sourceMap insertion
  | sourceOrderType == finiteOrdinal 0 = Right emptyInterpretedMap
  | insertionOrderType == finiteOrdinal 0 = Right emptyInterpretedMap
  | otherwise = do
      Bifunctor.first AccessRejected
        (validateAccessSelection
          rankOrderType
          insertionOrderType
          sourceOrderType
          (someSuperEllipsisInsertionPositionAt insertion))
      let selectedValues =
            OrdinalOrderedValues insertionOrderType $ \position -> do
              selectedPosition <-
                someSuperEllipsisInsertionPositionAt insertion position
              ordinalOrderedValueAt sourceValues selectedPosition
          components = selectedComponents selectedValues insertionOrderType
      Right (InterpretedMap 2 selectedValues components)
  where
    sourceValues = interpretedMapFinalValues sourceMap
    sourceOrderType = ordinalOrderedValuesOrderType sourceValues
    insertionOrderType = someSuperEllipsisInsertionOrderType insertion
    rankOrderType = omegaPower (someSuperEllipsisInsertionRank insertion)

    selectedComponents selectedValues orderType =
      case naturalAtOrdinal orderType of
        Nothing -> [CanonicalSuperEllipsisInsertion]
        Just cardinality ->
          concatMap
            (maybe []
              (interpretedMapComponents . interpretedMap)
              . ordinalOrderedValueAt selectedValues
              . finiteOrdinal)
            [0 .. cardinality - 1]
