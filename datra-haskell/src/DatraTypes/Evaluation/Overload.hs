-- | Default-bearing map overloading. The left operand supplies the shape and
-- defaults; the right operand is matched against the same shape with those
-- defaults erased, then replaces only the slots it supplies.
module Evaluation.Overload
  ( overloadValues
  , overloadValuesComplete
  ) where

import Control.Applicative ((<|>))
import Data.List (nubBy, permutations, sortOn)
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import Evaluation.Arguments (argumentRows, makeArgumentMap)
import Evaluation.Either (makeEitherValue)
import Evaluation.Error (InterpretingError (..))
import Evaluation.Identifier (simpleIdentifierTypeValue)
import Evaluation.Map (concatenateValues, makeAtlasMap)
import Evaluation.Specification (assignIdentifierValues, specifyValues)
import Evaluation.Value
import Numeric.Natural (Natural)

data OverloadTemplate
  = OverloadSlot
      Int
      (Maybe String)
      Bool
      InterpretedValue
      (Maybe InterpretedValue)
  | OverloadOrdered Natural [OverloadTemplate]
  | OverloadUnordered [OverloadTemplate]
  | OverloadConcatenated OverloadTemplate OverloadTemplate
  | OverloadEmpty

data Slot = Slot
  { slotIndex :: Int
  , slotName :: Maybe String
  , slotNameOptional :: Bool
  , slotAnnotation :: InterpretedValue
  , slotDefault :: Maybe InterpretedValue
  }

type Replacements = [(Int, InterpretedValue)]

-- | Overload the defaults and supplied values in a runtime value. Missing
-- non-defaulted slots remain types, which makes the operator useful for
-- incrementally constructing argument maps.
overloadValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
overloadValues templateValue supplied = do
  let template = fst (templateFromValue 0 templateValue)
  replacements <- resolveReplacements template supplied
  buildTemplate replacements template

-- | Function application uses the same operation, but additionally requires
-- every slot to have a supplied value, an explicit default, or a total type
-- annotation. The returned bindings contain the unwrapped values seen by the
-- function body.
overloadValuesComplete
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError (InterpretedValue, [(String, InterpretedValue)])
overloadValuesComplete templateValue supplied = do
  let template = fst (templateFromValue 0 templateValue)
  replacements <- resolveReplacements template supplied
  completed <- traverse (completeSlot replacements) (templateSlots template)
  result <- buildTemplate replacements template
  pure (result, [(name, value) | (Just name, value) <- completed])

resolveReplacements
  :: OverloadTemplate
  -> InterpretedValue
  -> Either InterpretingError Replacements
resolveReplacements template supplied = do
  rows <- argumentRows supplied
  let slotOrders = templateSlotOrders template
      routes =
        [ concatMap (`matchInputs` row) slotOrders
        | row <- rows
        ]
  if any null routes
    then Left (OverloadError
      "the right operand does not match the left operand without its defaults")
    else
      case nubBy sameReplacements (concat routes) of
        [] -> Left (OverloadError
          "the right operand does not match the left operand without its defaults")
        [replacements] -> Right replacements
        _ -> Left (OverloadError
          "ambiguous overload; supply identifiers to select the intended slots")
  where
    sameReplacements left right = canonical left == canonical right
    canonical = sortOn fst . map
      (\(index, value) -> (index, interpretedCanonicalResult value))

matchInputs :: [Slot] -> [InterpretedValue] -> [Replacements]
matchInputs _ [] = [[]]
matchInputs [] _ = []
matchInputs (slot : remainingSlots) inputs@(input : remainingInputs) =
  case matchSlot slot input of
    Just value ->
      [ (slotIndex slot, value) : later
      | later <- matchInputs remainingSlots remainingInputs
      ]
    Nothing -> matchInputs remainingSlots inputs

matchSlot :: Slot -> InterpretedValue -> Maybe InterpretedValue
matchSlot slot input = do
  let (inputName, inputValue) = suppliedValue input
  case (slotName slot, inputName) of
    (Just expected, Just actual)
      | expected == actual -> pure ()
      | otherwise -> Nothing
    (Just _, Nothing)
      | slotNameOptional slot -> pure ()
      | otherwise -> Nothing
    (Nothing, Nothing) -> pure ()
    (Nothing, Just _) -> Nothing
  case specifyValues inputValue (slotAnnotation slot) of
    Right _ -> Just inputValue
    Left _ -> Nothing

suppliedValue :: InterpretedValue -> (Maybe String, InterpretedValue)
suppliedValue value =
  case optionalNamedParts value of
    Just (name, _, Just supplied) -> (Just name, supplied)
    _ ->
      case namedParts value of
        Just (name, annotation, supplied) ->
          (Just name, maybe annotation id supplied)
        Nothing -> (Nothing, value)

templateSlots :: OverloadTemplate -> [Slot]
templateSlots template =
  case template of
    OverloadSlot index name optional annotation defaultValue ->
      [Slot index name optional annotation defaultValue]
    OverloadOrdered _ children -> concatMap templateSlots children
    OverloadUnordered children -> concatMap templateSlots children
    OverloadConcatenated left right ->
      templateSlots left <> templateSlots right
    OverloadEmpty -> []

-- Ordered maps retain one slot order. Argument maps contribute every member
-- order, so unnamed values remain ambiguous while named values normalize to
-- one replacement set. Concatenation preserves the order of its segments.
templateSlotOrders :: OverloadTemplate -> [[Slot]]
templateSlotOrders template =
  case template of
    OverloadSlot index name optional annotation defaultValue ->
      [[Slot index name optional annotation defaultValue]]
    OverloadOrdered _ children -> combine children
    OverloadUnordered children ->
      concatMap combine (permutations children)
    OverloadConcatenated left right ->
      [leftSlots <> rightSlots
      | leftSlots <- templateSlotOrders left
      , rightSlots <- templateSlotOrders right
      ]
    OverloadEmpty -> [[]]
  where
    combine children =
      map concat (sequence (map templateSlotOrders children))

templateFromValue :: Int -> InterpretedValue -> (OverloadTemplate, Int)
templateFromValue next value =
  case optionalNamedParts value of
    Just (name, annotation, defaultValue) ->
      ( OverloadSlot next (Just name) True annotation defaultValue
      , next + 1
      )
    Nothing ->
      case namedParts value of
        Just (name, annotation, defaultValue) ->
          ( OverloadSlot next (Just name) False annotation defaultValue
          , next + 1
          )
        Nothing ->
          case interpretedForm value of
            ArgumentMapForm members _ ->
              mapChildren OverloadUnordered next members
            ConcatenatedMapForm left right ->
              let (leftTemplate, afterLeft) = templateFromValue next left
                  (rightTemplate, afterRight) =
                    templateFromValue afterLeft right
              in ( OverloadConcatenated leftTemplate rightTemplate
                 , afterRight
                 )
            SequentialMapForm ->
              case finiteMembers value of
                Just [] -> (OverloadEmpty, next)
                Just members ->
                  let (children, afterChildren) =
                        templatesFromValues next members
                  in ( OverloadOrdered
                         (interpretedMapCardinality (interpretedMap value))
                         children
                     , afterChildren
                     )
                Nothing -> slot
            MapForm
              | Just [] <- finiteMembers value -> (OverloadEmpty, next)
            _ -> slot
  where
    slot = (OverloadSlot next Nothing False value Nothing, next + 1)
    mapChildren constructor start members =
      let (children, afterChildren) = templatesFromValues start members
      in (constructor children, afterChildren)

templatesFromValues
  :: Int
  -> [InterpretedValue]
  -> ([OverloadTemplate], Int)
templatesFromValues next [] = ([], next)
templatesFromValues next (value : remaining) =
  let (template, afterTemplate) = templateFromValue next value
      (templates, finalIndex) =
        templatesFromValues afterTemplate remaining
  in (template : templates, finalIndex)

finiteMembers :: InterpretedValue -> Maybe [InterpretedValue]
finiteMembers value = do
  count <- naturalAtOrdinal
    (interpretedMapFinalOrderType (interpretedMap value))
  traverse
    (interpretedMapValueAt (interpretedMap value) . finiteOrdinal)
    (if count == 0 then [] else [0 .. count - 1])

optionalNamedParts
  :: InterpretedValue
  -> Maybe (String, InterpretedValue, Maybe InterpretedValue)
optionalNamedParts value = do
  alternatives <-
    case interpretedForm value of
      EitherForm eitherValue -> Just eitherValue
      _ -> Nothing
  parts@(_, annotation, _) <-
    namedParts (evaluatedEitherLeft alternatives)
  if interpretedCanonicalResult annotation
      == interpretedCanonicalResult (evaluatedEitherRight alternatives)
    then Just parts
    else Nothing

namedParts
  :: InterpretedValue
  -> Maybe (String, InterpretedValue, Maybe InterpretedValue)
namedParts value =
  case interpretedForm value of
    DependentIdentifierTypeForm identifier -> do
      name <- simpleName (evaluatedIdentifierDependency identifier)
      pure (name, evaluatedIdentifierUnderlying identifier, Nothing)
    AssignmentForm specification -> specificationParts specification
    SpecificationForm specification -> specificationParts specification
    _ -> Nothing
  where
    specificationParts specification = do
      (name, annotation, _) <-
        namedParts (evaluatedSpecificationTarget specification)
      (sourceName, supplied, _) <-
        namedParts (evaluatedSpecificationSourceValue specification)
      if name == sourceName
        then Just (name, annotation, Just supplied)
        else Nothing
    simpleName dependency =
      case dependency of
        SimpleIdentifierDependency name -> Just name
        DependentIdentifierDependency {} -> Nothing

completeSlot
  :: Replacements
  -> Slot
  -> Either InterpretingError (Maybe String, InterpretedValue)
completeSlot replacements slot =
  case lookup (slotIndex slot) replacements
      <|> slotDefault slot of
    Just value -> Right (slotName slot, value)
    Nothing
      | interpretedTypeIsTotal (slotAnnotation slot) ->
          Right (slotName slot, slotAnnotation slot)
      | otherwise -> Left (OverloadError
          "overload leaves a required slot without a value")

buildTemplate
  :: Replacements
  -> OverloadTemplate
  -> Either InterpretingError InterpretedValue
buildTemplate replacements template =
  case template of
    OverloadSlot index name optional annotation defaultValue ->
      buildSlot name optional annotation
        (lookup index replacements <|> defaultValue)
    OverloadOrdered cardinality children ->
      makeAtlasMap cardinality <$> traverse (buildTemplate replacements) children
    OverloadUnordered children ->
      traverse (buildTemplate replacements) children >>= makeArgumentMap
    OverloadConcatenated left right ->
      do
        leftValue <- buildTemplate replacements left
        rightValue <- buildTemplate replacements right
        concatenateValues leftValue rightValue
    OverloadEmpty -> Right (makeAtlasMap 0 [])

buildSlot
  :: Maybe String
  -> Bool
  -> InterpretedValue
  -> Maybe InterpretedValue
  -> Either InterpretingError InterpretedValue
buildSlot Nothing _ annotation supplied =
  Right (maybe annotation id supplied)
buildSlot (Just name) optional annotation supplied = do
  present <-
    case supplied of
      Nothing -> Right (simpleIdentifierTypeValue name annotation)
      Just value ->
        case assignIdentifierValues name annotation value of
          Right assigned -> Right assigned
          Left _ -> do
            -- Some non-total values (notably functions and AST adapters) are
            -- valid members without carrying a total Atlas witness through an
            -- identifier assignment. Preserve their name after validating the
            -- same annotation used during matching.
            _ <- specifyValues value annotation
            Right (simpleIdentifierTypeValue name value)
  if optional
    then makeEitherValue present annotation
    else Right present
