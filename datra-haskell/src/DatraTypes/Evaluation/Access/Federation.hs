-- | Access rules for atomic Atlas-map federations.
module Evaluation.Access.Federation
  ( AccessibleOrdinalRegion (..)
  , AccessLayout (..)
  , FederationAccess (..)
  , atomicAccessLayout
  , decideAtomicFederationAccess
  , decideDirectFederationAccess
  , emptyMapAccessCounterexample
  , naturalRangeFederation
  , requireInsertion
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (..)
  )
import DatraOrdinal (Ordinal, finiteOrdinal)
import Evaluation.Error
import Evaluation.Access.RangeSelection (clippableSelectionRange)
import Evaluation.Value
import SuperEllipsisInsertion
  ( someSuperEllipsisInsertionOrderType
  )

data FederationAccess
  = NaturalRangeFederationAccess
      EvaluatedNaturalRange
      EvaluatedNaturalRange
  | NaturalRangeSelectionAccess EvaluatedNaturalRange
  | ClippedRangeFederationAccess EvaluatedRange
  | ClippedRangeSelectionAccess EvaluatedRange
  | EmptyFederationAccess
  | SingletonFederationAccess SomeSuperEllipsisInsertion

-- | The structural facts about an atomic federation needed to lift access
-- through flattened constructions. The representative map preserves a
-- coalition as one position; a fixed order type permits following operands
-- to have stable offsets.
data AccessLayout = AccessLayout
  { accessLayoutRepresentativeMap :: InterpretedMap
  , accessLayoutFixedOrderType :: Maybe Ordinal
  , accessLayoutAccessibleRegions :: [AccessibleOrdinalRegion]
  }

-- | A half-open absolute ordinal interval known to be accessible for every
-- member of a federation.
data AccessibleOrdinalRegion = AccessibleOrdinalRegion
  { accessibleRegionLowerBound :: Ordinal
  , accessibleRegionUpperBound :: Ordinal
  }

data AtomicFederationAccess = AtomicFederationAccess
  { atomicFederationLayout :: AccessLayout
  , atomicFederationDecision
      :: InterpretedValue
      -> Either InterpretingError FederationAccess
  }

atomicAccessLayout :: InterpretedValue -> Maybe AccessLayout
atomicAccessLayout = fmap atomicFederationLayout . atomicFederationAccess

atomicFederationAccess
  :: InterpretedValue
  -> Maybe AtomicFederationAccess
atomicFederationAccess value =
  case interpretedAtlasMapFederation value of
    SingletonAtlasMapFederation _ ->
      Just (directRule (fixedLayout (interpretedMap value)))
    CoalizedAtlasMapFederation _ ->
      Just (directRule (fixedLayout (interpretedMap value)))
    PrimitiveAtlasMapFederation
        (ValuedNaturalRangeAtlasMapFederation _) ->
      let coalitionMap =
            InterpretedMap
              1
              (singletonOrdinalOrderedValues value)
              [interpretedSemantics value]
      in Just (directRule (fixedLayout coalitionMap))
    PrimitiveAtlasMapFederation
        (ValuedIntegerRangeAtlasMapFederation _) ->
      let coalitionMap =
            InterpretedMap
              1
              (singletonOrdinalOrderedValues value)
              [interpretedSemantics value]
      in Just (directRule (fixedLayout coalitionMap))
    PrimitiveAtlasMapFederation
        (NaturalRangeAtlasMapFederation sourceRange) ->
      Just
        AtomicFederationAccess
          { atomicFederationLayout =
              AccessLayout
                { accessLayoutRepresentativeMap = interpretedMap value
                , accessLayoutFixedOrderType = Nothing
                , accessLayoutAccessibleRegions = []
                }
          , atomicFederationDecision =
              decideNaturalRangeAccess sourceRange
          }
    PrimitiveAtlasMapFederation (IntegerRangeAtlasMapFederation _) ->
      Nothing
    PrimitiveAtlasMapFederation (EitherAtlasMapFederation _) -> Nothing
    PrimitiveAtlasMapFederation (DependentIdentifierTypeAtlasMapFederation _) ->
      Nothing
    PrimitiveAtlasMapFederation
        (IdentifierStringProjectionAtlasMapFederation _) ->
      Nothing
    PrimitiveAtlasMapFederation IdentifierValueTypeAtlasMapFederation ->
      Nothing
    PrimitiveAtlasMapFederation (ToStringAtlasMapFederation _ _) -> Nothing
    SequentialAtlasMapFederation _ -> Nothing
    ExpansionAtlasMapFederation _ _ -> Nothing
    ConcatenatedAtlasMapFederation _ _ -> Nothing
  where
    directRule layout =
      AtomicFederationAccess layout decideDirectFederationAccess

    fixedLayout valueMap =
      let orderType = interpretedMapFinalOrderType valueMap
      in AccessLayout valueMap (Just orderType) (fullRegion orderType)

    fullRegion orderType
      | orderType == finiteOrdinal 0 = []
      | otherwise =
          [AccessibleOrdinalRegion (finiteOrdinal 0) orderType]

-- | Decide access for a leaf federation. 'Nothing' delegates a constructed
-- federation to the composition layer without conflating it with an atomic
-- refutation or uncertainty.
decideAtomicFederationAccess
  :: InterpretedValue
  -> InterpretedValue
  -> Maybe (Either InterpretingError FederationAccess)
decideAtomicFederationAccess mapValue insertionValue =
  (\rule -> atomicFederationDecision rule insertionValue)
    <$> atomicFederationAccess mapValue

decideNaturalRangeAccess
  :: EvaluatedNaturalRange
  -> InterpretedValue
  -> Either InterpretingError FederationAccess
decideNaturalRangeAccess sourceRange insertionValue =
  case naturalRangeFederation insertionValue of
    Just selectionRange ->
      Right (NaturalRangeFederationAccess sourceRange selectionRange)
    Nothing ->
      case clippableSelectionRange insertionValue of
        Just selectionRange ->
          Right (ClippedRangeFederationAccess selectionRange)
        Nothing -> do
          insertion <- requireInsertion insertionValue
          if insertionIsEmpty insertion
            then Right EmptyFederationAccess
            else emptyMapAccessCounterexample

decideDirectFederationAccess
  :: InterpretedValue
  -> Either InterpretingError FederationAccess
decideDirectFederationAccess insertionValue =
  case naturalRangeFederation insertionValue of
    Just selectionRange -> Right (NaturalRangeSelectionAccess selectionRange)
    Nothing ->
      case clippableSelectionRange insertionValue of
        Just selectionRange ->
          Right (ClippedRangeSelectionAccess selectionRange)
        Nothing -> do
          insertion <- requireInsertion insertionValue
          Right
            (if insertionIsEmpty insertion
              then EmptyFederationAccess
              else SingletonFederationAccess insertion)

emptyMapAccessCounterexample :: Either InterpretingError result
emptyMapAccessCounterexample =
  Left
    (AtlasMapFederationOperationRefuted
      AtlasMapFederationAccessHasEmptyCounterexample)

naturalRangeFederation
  :: InterpretedValue
  -> Maybe EvaluatedNaturalRange
naturalRangeFederation value =
  case interpretedAtlasMapFederation value of
    PrimitiveAtlasMapFederation
        (NaturalRangeAtlasMapFederation naturalRange) ->
      Just naturalRange
    _ -> Nothing

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

insertionIsEmpty :: SomeSuperEllipsisInsertion -> Bool
insertionIsEmpty insertion =
  someSuperEllipsisInsertionOrderType insertion == finiteOrdinal 0
