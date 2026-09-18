{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | Compilation and evaluation of the parsed Datra AST.
--
-- Values retain the DatraTypes witnesses that justify their numerical and
-- range capabilities. The small runtime layer exists only to hide ranks and
-- fresh range scopes chosen while interpreting source expressions.
module Datra.Interpreting
  ( InterpretedValue
  , CanonicalResult (..)
  , InterpretedValueKind (..)
  , InterpretedMap
  , InterpretingError (..)
  , OperandSide (..)
  , interpretExpression
  , interpretLocatedExpression
  , interpretExpressionReason
  , interpretedValueKind
  , interpretedCanonicalResult
  , interpretedExplicitOrdinal
  , interpretedFormulationLevel
  , interpretedRangeDescription
  , interpretedMap
  , interpretedMapCardinality
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  ) where

import Chain (chainIndex, chainObjectAt, chainOrderType)
import Data.Bifunctor qualified as Bifunctor
import Data.Kind (Type)
import Datra.AST (Expression (..))
import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  , multiplyOrdinals
  , naturalAtOrdinal
  , omegaPower
  , ordinalLT
  , powerOrdinal
  , subtractOrdinal
  )
import Diagnostics
  ( DatraError
  , Located (Located)
  , atSourceSpan
  , withoutSourceSpan
  )
import Diagnostics.Interpreter
  ( InterpretedValueKind (..)
  , InterpretingError (..)
  , OperandSide (..)
  )
import MapOperators.AccessOperator
  ( AccessError
      ( AccessInsertionRankExceedsMap
      , AccessPositionOutOfBounds
      )
  )
import Numeric.Natural (Natural)
import NumericalOperators.NumericalOperand
  ( SomeSuperEllipsis
  , someSuperEllipsis
  , someSuperEllipsisLevel
  , withSomeSuperEllipsis
  )
import StableConfederalData (StableConfederalData)
import SuperEllipsis
  ( SuperEllipsisRank
  , SuperEllipsisTarget
  , superEllipsisTargetRank
  )
import SuperEllipsisInsertion
  ( superEllipsisInsertionChain
  , superEllipsisInsertionPosition
  )
import SuperEllipsisRange qualified as Range
import SuperEllipsisValue
  ( SuperEllipsisValue
  , canonicalSuperEllipsisValue
  , minimumSuperEllipsisValueRank
  , superEllipsisValueOrdinal
  )

data ExplicitOrigin = NaturalOrigin | ComputedOrigin

data EvaluatedExplicit where
  EvaluatedExplicit
    :: Natural
    -> ExplicitOrigin
    -> SuperEllipsisValue target scope
    -> EvaluatedExplicit

data EvaluatedRange where
  EvaluatedRange
    :: Natural
    -> Range.SuperEllipsisRange target scope
    -> EvaluatedRange

data ValueForm
  = ExplicitForm EvaluatedExplicit
  | FormulationForm SomeSuperEllipsis
  | RangeForm EvaluatedRange
  | RangeConcatenationForm [EvaluatedRange]
  | MapForm

data RuntimeInsertion = RuntimeInsertion
  { runtimeInsertionRank :: Natural
  , runtimeInsertionOrderType :: Ordinal
  , runtimeInsertionPositionAt :: Ordinal -> Maybe Ordinal
  }

data InsertionCapability
  = NoInsertion
  | ValidInsertion RuntimeInsertion
  | RejectedInsertion Range.SuperEllipsisRangeConcatError

data OrderedValues = OrderedValues
  { orderedValuesOrderType :: Ordinal
  , orderedValueAt :: Ordinal -> Maybe InterpretedValue
  }

data InterpretedMap = InterpretedMap
  { interpretedMapCardinality :: Natural
  , interpretedMapFinalValues :: OrderedValues
  , interpretedMapComponents :: [CanonicalResult]
  }

-- | A normalized, source-independent presentation of an evaluated value.
-- Maps contain compact final-page components, so an infinite range remains
-- renderable without attempting to enumerate it.
data CanonicalResult
  = CanonicalExplicit Natural Ordinal
  | CanonicalFormulation Natural
  | CanonicalRange Range.SuperEllipsisRangeDescription
  | CanonicalRangeConcatenation [Range.SuperEllipsisRangeDescription]
  | CanonicalMap Natural [CanonicalResult]
  | CanonicalSuperEllipsisInsertion
  deriving (Eq, Show)

data InterpretedValue = InterpretedValue
  { interpretedForm :: ValueForm
  , interpretedInsertionCapability :: InsertionCapability
  , interpretedMap :: InterpretedMap
  , interpretedCanonicalResult :: CanonicalResult
  }

interpretedValueKind :: InterpretedValue -> InterpretedValueKind
interpretedValueKind value =
  case interpretedForm value of
    ExplicitForm (EvaluatedExplicit _ NaturalOrigin _) -> NaturalValueKind
    ExplicitForm _ -> ExplicitOrdinalValueKind
    FormulationForm _ -> FormulationValueKind
    RangeForm _ -> RangeValueKind
    RangeConcatenationForm _ -> RangeConcatenationValueKind
    MapForm -> MapValueKind

interpretedExplicitOrdinal
  :: InterpretedValue
  -> Maybe (Natural, Ordinal)
interpretedExplicitOrdinal value =
  case interpretedForm value of
    ExplicitForm explicitValue -> Just (explicitOrdinal explicitValue)
    _ -> Nothing

interpretedFormulationLevel :: InterpretedValue -> Maybe Natural
interpretedFormulationLevel value =
  case interpretedForm value of
    FormulationForm formulation ->
      Just (someSuperEllipsisLevel formulation)
    _ -> Nothing

interpretedRangeDescription
  :: InterpretedValue
  -> Maybe Range.SuperEllipsisRangeDescription
interpretedRangeDescription value =
  case interpretedForm value of
    RangeForm valueRange -> Just (rangeDescription valueRange)
    _ -> Nothing

interpretedMapFinalOrderType :: InterpretedMap -> Ordinal
interpretedMapFinalOrderType =
  orderedValuesOrderType . interpretedMapFinalValues

interpretedMapValueAt
  :: InterpretedMap
  -> Ordinal
  -> Maybe InterpretedValue
interpretedMapValueAt = orderedValueAt . interpretedMapFinalValues

interpretExpression
  :: Expression
  -> Either (DatraError InterpretingError) InterpretedValue
interpretExpression =
  Bifunctor.first withoutSourceSpan . interpretExpressionReason

interpretLocatedExpression
  :: Located Expression
  -> Either (DatraError InterpretingError) InterpretedValue
interpretLocatedExpression (Located sourceSpan expressionValue) =
  Bifunctor.first (atSourceSpan sourceSpan)
    (interpretExpressionReason expressionValue)

interpretExpressionReason
  :: Expression
  -> Either InterpretingError InterpretedValue
interpretExpressionReason expressionValue =
  case expressionValue of
    EllipsisNatural value -> makeExplicit NaturalOrigin (finiteOrdinal value)
    EllipsisLiteral -> Right (makeFormulation 1)
    AtlasMap expressions -> interpretAtlasMap expressions
    SuperEllipsisRange lower upper -> do
      lowerValue <- interpretExpressionReason lower >>= asExplicit LeftOperand
      upperValue <-
        interpretExpressionReason upper >>= asRangeUpperBoundary RightOperand
      makeBoundedRange lowerValue upperValue
    SuperEllipsisRangePlus lower -> do
      lowerValue <- interpretExpressionReason lower >>= asExplicit LeftOperand
      makeRange lowerValue Range.PlusSign
    SuperEllipsisRangeMinus upper -> do
      upperValue <- interpretExpressionReason upper >>= asExplicit LeftOperand
      makeRange upperValue Range.MinusSign
    Addition left right ->
      interpretNumericalBinary addNumerical left right
    Multiplication left right ->
      interpretNumericalBinary multiplyNumerical left right
    Exponentiation base exponentValue -> do
      baseValue <- interpretExpressionReason base
      interpretedExponent <- interpretExpressionReason exponentValue
      exponentiateValues baseValue interpretedExponent
    MapConcatenation left right -> do
      leftValue <- interpretExpressionReason left
      rightValue <- interpretExpressionReason right
      concatenateValues leftValue rightValue
    MapAccess mapOperand insertionOperand -> do
      mapValue <- interpretExpressionReason mapOperand
      insertionValue <- interpretExpressionReason insertionOperand
      accessValues mapValue insertionValue

interpretNumericalBinary
  :: (NumericalValue -> NumericalValue
      -> Either InterpretingError InterpretedValue)
  -> Expression
  -> Expression
  -> Either InterpretingError InterpretedValue
interpretNumericalBinary operator left right = do
  leftValue <- interpretExpressionReason left >>= asNumerical LeftOperand
  rightValue <- interpretExpressionReason right >>= asNumerical RightOperand
  operator leftValue rightValue

data NumericalValue
  = ExplicitNumericalValue Natural Ordinal
  | FormulationNumericalValue Natural

asNumerical
  :: OperandSide
  -> InterpretedValue
  -> Either InterpretingError NumericalValue
asNumerical side value =
  case interpretedForm value of
    ExplicitForm explicitValue ->
      let (level, ordinalValue) = explicitOrdinal explicitValue
      in Right (ExplicitNumericalValue level ordinalValue)
    FormulationForm formulation ->
      Right
        (FormulationNumericalValue
          (someSuperEllipsisLevel formulation))
    _ -> Left (ExpectedNumericalOperand side (interpretedValueKind value))

asExplicit
  :: OperandSide
  -> InterpretedValue
  -> Either InterpretingError EvaluatedExplicit
asExplicit side value =
  case interpretedForm value of
    ExplicitForm explicitValue -> Right explicitValue
    FormulationForm formulation ->
      let level = someSuperEllipsisLevel formulation
      in makeExplicitValue
          ComputedOrigin
          (omegaPower level)
    _ -> Left (ExpectedNumericalOperand side (interpretedValueKind value))

explicitOrdinal :: EvaluatedExplicit -> (Natural, Ordinal)
explicitOrdinal (EvaluatedExplicit level _ value) =
  (level, superEllipsisValueOrdinal value)

asRangeUpperBoundary
  :: OperandSide
  -> InterpretedValue
  -> Either InterpretingError (Natural, Ordinal)
asRangeUpperBoundary side value =
  case interpretedForm value of
    ExplicitForm explicitValue -> Right (explicitOrdinal explicitValue)
    FormulationForm formulation ->
      let level = someSuperEllipsisLevel formulation
      in Right (level, omegaPower level)
    _ -> Left (ExpectedNumericalOperand side (interpretedValueKind value))

addNumerical
  :: NumericalValue
  -> NumericalValue
  -> Either InterpretingError InterpretedValue
addNumerical left right =
  makeExplicit ComputedOrigin
    (addOrdinals (numericalOrdinal left) (numericalOrdinal right))

multiplyNumerical
  :: NumericalValue
  -> NumericalValue
  -> Either InterpretingError InterpretedValue
multiplyNumerical
    (FormulationNumericalValue leftLevel)
    (FormulationNumericalValue rightLevel) =
  Right (makeFormulation (leftLevel + rightLevel))
multiplyNumerical left right =
  makeExplicit ComputedOrigin
    (multiplyOrdinals (numericalOrdinal left) (numericalOrdinal right))

exponentiateValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
exponentiateValues base exponentValue = do
  naturalPower <- naturalExponent exponentValue
  case interpretedForm base of
    FormulationForm formulation ->
      Right
        (makeFormulation
          (someSuperEllipsisLevel formulation * naturalPower))
    ExplicitForm explicitValue ->
      let (_, ordinalValue) = explicitOrdinal explicitValue
      in makeExplicit
          ComputedOrigin
          (powerOrdinal ordinalValue naturalPower)
    _ ->
      Left
        (ExpectedNumericalOperand
          LeftOperand
          (interpretedValueKind base))

naturalExponent
  :: InterpretedValue
  -> Either InterpretingError Natural
naturalExponent value =
  case interpretedForm value of
    ExplicitForm explicitValue ->
      case explicitOrdinal explicitValue of
        (1, ordinalValue) ->
          case naturalAtOrdinal ordinalValue of
            Just natural -> Right natural
            Nothing -> Left (ExpectedNaturalExponent (interpretedValueKind value))
        _ -> Left (ExpectedNaturalExponent (interpretedValueKind value))
    _ -> Left (ExpectedNaturalExponent (interpretedValueKind value))

numericalOrdinal :: NumericalValue -> Ordinal
numericalOrdinal (ExplicitNumericalValue _ value) = value
numericalOrdinal (FormulationNumericalValue level) = omegaPower level

makeExplicit
  :: ExplicitOrigin
  -> Ordinal
  -> Either InterpretingError InterpretedValue
makeExplicit origin ordinalValue = do
  explicitValue <- makeExplicitValue origin ordinalValue
  pure (explicitInterpretedValue explicitValue)

makeExplicitValue
  :: ExplicitOrigin
  -> Ordinal
  -> Either InterpretingError EvaluatedExplicit
makeExplicitValue origin ordinalValue =
  Right
    (canonicalSuperEllipsisValue ordinalValue $ \value ->
      EvaluatedExplicit level origin value)
  where
    level = minimumSuperEllipsisValueRank ordinalValue

explicitInterpretedValue :: EvaluatedExplicit -> InterpretedValue
explicitInterpretedValue explicitValue = value
  where
    (level, ordinalValue) = explicitOrdinal explicitValue
    insertion = singletonInsertion level ordinalValue
    canonical = CanonicalExplicit level ordinalValue
    value =
      InterpretedValue
        (ExplicitForm explicitValue)
        (ValidInsertion insertion)
        (singletonMap canonical value)
        canonical

makeFormulation :: Natural -> InterpretedValue
makeFormulation level = value
  where
    formulation = someSuperEllipsis level
    insertion = identityInsertion level
    values =
      OrderedValues
        (runtimeInsertionOrderType insertion)
        (\position -> do
          absolute <- runtimeInsertionPositionAt insertion position
          either (const Nothing) Just
            (makeExplicit ComputedOrigin absolute))
    value =
      InterpretedValue
        (FormulationForm formulation)
        (ValidInsertion insertion)
        (InterpretedMap 1 values [canonical])
        canonical
    canonical = CanonicalFormulation level

makeBoundedRange
  :: EvaluatedExplicit
  -> (Natural, Ordinal)
  -> Either InterpretingError InterpretedValue
makeBoundedRange lower (upperLevel, upperOrdinal) =
  let (lowerLevel, lowerOrdinal) = explicitOrdinal lower
      resultLevel = max lowerLevel upperLevel
  in makeRangeAt
      resultLevel
      lowerOrdinal
      (Range.GivenTarget upperOrdinal)

makeRange
  :: EvaluatedExplicit
  -> Range.SuperEllipsisRangeTarget
  -> Either InterpretingError InterpretedValue
makeRange endpoint target =
  let (level, ordinalValue) = explicitOrdinal endpoint
  in makeRangeAt level ordinalValue target

makeRangeAt
  :: Natural
  -> Ordinal
  -> Range.SuperEllipsisRangeTarget
  -> Either InterpretingError InterpretedValue
makeRangeAt level start target =
  interpretedRangeValue <$> makeEvaluatedRangeAt level start target

makeEvaluatedRangeAt
  :: Natural
  -> Ordinal
  -> Range.SuperEllipsisRangeTarget
  -> Either InterpretingError EvaluatedRange
makeEvaluatedRangeAt level start target =
  withRank level $ \valueRank ->
    case Range.superEllipsisRangeEither valueRank start target $ \valueRange ->
        EvaluatedRange level valueRange of
      Left rejection -> Left (RangeConstructionRejected rejection)
      Right value -> Right value

interpretedRangeValue :: EvaluatedRange -> InterpretedValue
interpretedRangeValue evaluatedRange =
  InterpretedValue
    (RangeForm evaluatedRange)
    (ValidInsertion insertion)
    (mapFromInsertion insertion [canonical])
    canonical
  where
    insertion = rangeInsertion evaluatedRange
    canonical = CanonicalRange (rangeDescription evaluatedRange)

rangeDescription
  :: EvaluatedRange
  -> Range.SuperEllipsisRangeDescription
rangeDescription (EvaluatedRange _ valueRange) =
  Range.describeSuperEllipsisRange valueRange

evaluatedRangeLevel :: EvaluatedRange -> Natural
evaluatedRangeLevel (EvaluatedRange level _) = level

rangeInsertion :: EvaluatedRange -> RuntimeInsertion
rangeInsertion (EvaluatedRange level valueRange) =
  RuntimeInsertion
    level
    (chainOrderType insertionChain)
    (\position -> do
      sourceIndex <- chainIndex insertionChain position
      pure
        (superEllipsisInsertionPosition
          insertion
          (chainObjectAt sourceIndex)))
  where
    insertion = Range.superEllipsisRangeInsertion valueRange
    insertionChain = superEllipsisInsertionChain insertion

singletonInsertion :: Natural -> Ordinal -> RuntimeInsertion
singletonInsertion level ordinalValue =
  RuntimeInsertion
    level
    (finiteOrdinal 1)
    (\position ->
      if position == finiteOrdinal 0 then Just ordinalValue else Nothing)

identityInsertion :: Natural -> RuntimeInsertion
identityInsertion level =
  let orderType = omegaPower level
  in RuntimeInsertion
      level
      orderType
      (\position ->
        if ordinalLT position orderType then Just position else Nothing)

mapFromInsertion :: RuntimeInsertion -> [CanonicalResult] -> InterpretedMap
mapFromInsertion insertion components =
  InterpretedMap
    (if isEmpty then 0 else 1)
    (OrderedValues
      (runtimeInsertionOrderType insertion)
      (\position -> do
        absolute <- runtimeInsertionPositionAt insertion position
        either (const Nothing) Just
          (makeExplicit
            ComputedOrigin
            absolute)))
    (if isEmpty then [] else components)
  where
    isEmpty = runtimeInsertionOrderType insertion == finiteOrdinal 0

interpretAtlasMap
  :: [Expression]
  -> Either InterpretingError InterpretedValue
interpretAtlasMap expressions = do
  values <- traverse interpretExpressionReason expressions
  let finalValues =
        foldl'
          appendOrderedValues
          emptyOrderedValues
          (map (interpretedMapFinalValues . interpretedMap) values)
      nestingDepths =
        zipWith expressionNestingDepth expressions values
      mapDepth
        | null expressions = 0
        | otherwise = 1 + maximum nestingDepths
      cardinality
        | mapDepth == 0 = 0
        | otherwise = mapDepth + 1
      components =
        concatMap (interpretedMapComponents . interpretedMap) values
      canonical = CanonicalMap cardinality components
  pure
    (InterpretedValue
      MapForm
      NoInsertion
      (InterpretedMap cardinality finalValues components)
      canonical)

expressionNestingDepth :: Expression -> InterpretedValue -> Natural
expressionNestingDepth expressionValue value =
  case expressionValue of
    AtlasMap _ ->
      let cardinality = interpretedMapCardinality (interpretedMap value)
      in if cardinality == 0 then 0 else cardinality - 1
    _ -> 0

concatenateValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
concatenateValues left right = do
  normalizedRanges <-
    traverse canonicalizeRanges (concatenatedRanges left right)
  insertionCapability <-
    case normalizedRanges of
      Nothing -> Right NoInsertion
      Just ranges -> concatenateRangeCapability ranges
  let (form, finalValues, components, canonical) =
        case normalizedRanges of
          Just ranges ->
            ( canonicalRangeForm ranges
            , foldl'
                appendOrderedValues
                emptyOrderedValues
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
            , appendOrderedValues
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
        | orderedValuesOrderType finalValues == finiteOrdinal 0 = 0
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

valueRanges :: InterpretedValue -> Maybe [EvaluatedRange]
valueRanges value =
  case interpretedForm value of
    RangeForm valueRange -> Just [valueRange]
    RangeConcatenationForm ranges -> Just ranges
    _ -> Nothing

canonicalizeRanges
  :: [EvaluatedRange]
  -> Either InterpretingError [EvaluatedRange]
canonicalizeRanges [] = Right []
canonicalizeRanges (firstRange : rest) = go [firstRange] rest
  where
    go canonical [] = Right canonical
    go [] remaining = canonicalizeRanges remaining
    go canonical nextRanges@(nextRange : remaining) =
      case reverse canonical of
        [] -> go [] nextRanges
        previousRange : reversedPrefix ->
          case analyzeRangePair previousRange nextRange of
            Range.RangeConcatCanonical description -> do
              merged <-
                makeEvaluatedRangeAt
                  (canonicalRangeLevel
                    previousRange nextRange description)
                  (Range.describedRangeStart description)
                  (Range.describedRangeTarget description)
              go (reverse reversedPrefix <> [merged]) remaining
            _ -> go (canonical <> [nextRange]) remaining

canonicalRangeLevel
  :: EvaluatedRange
  -> EvaluatedRange
  -> Range.SuperEllipsisRangeDescription
  -> Natural
canonicalRangeLevel previousRange nextRange description
  | Range.describedRangeRankLimit description
      == Range.describedRangeRankLimit (rangeDescription previousRange) =
      evaluatedRangeLevel previousRange
  | otherwise = evaluatedRangeLevel nextRange

concatenateRangeCapability
  :: [EvaluatedRange]
  -> Either InterpretingError InsertionCapability
concatenateRangeCapability [] = Right NoInsertion
concatenateRangeCapability ranges =
  case firstRangeOverlap ranges of
    Left rejection -> Right (RejectedInsertion rejection)
    Right () ->
      Right
        (ValidInsertion
          (foldl1 appendInsertion (map rangeInsertion ranges)))

firstRangeOverlap
  :: [EvaluatedRange]
  -> Either Range.SuperEllipsisRangeConcatError ()
firstRangeOverlap [] = Right ()
firstRangeOverlap (firstRange : rest) = do
  mapM_ (ensureDisjoint firstRange) rest
  firstRangeOverlap rest

ensureDisjoint
  :: EvaluatedRange
  -> EvaluatedRange
  -> Either Range.SuperEllipsisRangeConcatError ()
ensureDisjoint firstRange secondRange =
  case analyzeRangePair firstRange secondRange of
    Range.RangeConcatOverlapping firstDescription secondDescription lower upper ->
      Left
        (Range.SuperEllipsisRangesOverlap
          firstDescription secondDescription lower upper)
    _ -> Right ()

analyzeRangePair
  :: EvaluatedRange
  -> EvaluatedRange
  -> Range.SuperEllipsisRangeConcatAnalysis
analyzeRangePair firstRange secondRange =
  Range.analyzeSuperEllipsisRangeDescriptions
    (rangeDescription firstRange)
    (rangeDescription secondRange)

appendInsertion :: RuntimeInsertion -> RuntimeInsertion -> RuntimeInsertion
appendInsertion left right =
  RuntimeInsertion
    (max (runtimeInsertionRank left) (runtimeInsertionRank right))
    combinedOrderType
    positionAt
  where
    leftOrderType = runtimeInsertionOrderType left
    combinedOrderType =
      addOrdinals leftOrderType (runtimeInsertionOrderType right)
    positionAt position
      | ordinalLT position leftOrderType =
          runtimeInsertionPositionAt left position
      | otherwise = do
          rightPosition <- subtractOrdinal leftOrderType position
          runtimeInsertionPositionAt right rightPosition

accessValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
accessValues mapValue insertionValue = do
  insertion <-
    case interpretedInsertionCapability insertionValue of
      NoInsertion ->
        Left
          (ExpectedInsertionOperand
            (interpretedValueKind insertionValue))
      RejectedInsertion rejection ->
        Left (RangeConcatenationRejected rejection)
      ValidInsertion valueInsertion -> Right valueInsertion
  selected <- accessMap (interpretedMap mapValue) insertion
  pure
    (InterpretedValue
      MapForm
      NoInsertion
      selected
      (CanonicalMap
        (interpretedMapCardinality selected)
        (interpretedMapComponents selected)))

accessMap
  :: InterpretedMap
  -> RuntimeInsertion
  -> Either InterpretingError InterpretedMap
accessMap sourceMap insertion
  | sourceOrderType == finiteOrdinal 0 = Right emptyInterpretedMap
  | insertionOrderType == finiteOrdinal 0 = Right emptyInterpretedMap
  | otherwise = do
      validateFits
      let selectedValues =
            OrderedValues insertionOrderType $ \position -> do
              selectedPosition <- runtimeInsertionPositionAt insertion position
              orderedValueAt sourceValues selectedPosition
          components = selectedComponents selectedValues insertionOrderType
      Right (InterpretedMap 2 selectedValues components)
  where
    sourceValues = interpretedMapFinalValues sourceMap
    sourceOrderType = orderedValuesOrderType sourceValues
    insertionOrderType = runtimeInsertionOrderType insertion
    rankOrderType = omegaPower (runtimeInsertionRank insertion)

    selectedComponents selectedValues orderType =
      case naturalAtOrdinal orderType of
        Nothing -> [CanonicalSuperEllipsisInsertion]
        Just cardinality ->
          concatMap
            (maybe []
              (interpretedMapComponents . interpretedMap)
              . orderedValueAt selectedValues
              . finiteOrdinal)
            [0 .. cardinality - 1]

    validateFits
      | rankOrderType == sourceOrderType
          || ordinalLT rankOrderType sourceOrderType = Right ()
      | otherwise =
          case naturalAtOrdinal insertionOrderType of
            Nothing ->
              Left
                (AccessRejected
                  (AccessInsertionRankExceedsMap
                    rankOrderType sourceOrderType))
            Just cardinality -> validateFinite 0 cardinality

    validateFinite position cardinality
      | position == cardinality = Right ()
      | otherwise =
          case runtimeInsertionPositionAt insertion (finiteOrdinal position) of
            Nothing -> validateFinite (position + 1) cardinality
            Just selectedPosition
              | ordinalLT selectedPosition sourceOrderType ->
                  validateFinite (position + 1) cardinality
              | otherwise ->
                  Left
                    (AccessRejected
                      (AccessPositionOutOfBounds
                        selectedPosition sourceOrderType))

emptyOrderedValues :: OrderedValues
emptyOrderedValues = OrderedValues (finiteOrdinal 0) (const Nothing)

emptyInterpretedMap :: InterpretedMap
emptyInterpretedMap = InterpretedMap 0 emptyOrderedValues []

singletonMap :: CanonicalResult -> InterpretedValue -> InterpretedMap
singletonMap canonical value =
  InterpretedMap
    1
    (OrderedValues
      (finiteOrdinal 1)
      (\position ->
        if position == finiteOrdinal 0 then Just value else Nothing))
    [canonical]

appendOrderedValues :: OrderedValues -> OrderedValues -> OrderedValues
appendOrderedValues left right =
  OrderedValues combinedOrderType valueAt
  where
    leftOrderType = orderedValuesOrderType left
    combinedOrderType =
      addOrdinals leftOrderType (orderedValuesOrderType right)
    valueAt position
      | ordinalLT position leftOrderType = orderedValueAt left position
      | otherwise = do
          rightPosition <- subtractOrdinal leftOrderType position
          orderedValueAt right rightPosition

withRank
  :: Natural
  -> (forall (target :: Type).
       SuperEllipsisTarget target
       => SuperEllipsisRank target
       -> result)
  -> result
withRank level useRank =
  withSomeSuperEllipsis (someSuperEllipsis level) $
    \(_ :: StableConfederalData target) ->
      useRank (superEllipsisTargetRank @target)
