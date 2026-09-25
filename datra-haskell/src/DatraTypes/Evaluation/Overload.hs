-- | Default-bearing map overloading. The left operand supplies the shape and
-- defaults; the right operand is matched against the same shape with those
-- defaults erased, then replaces only the slots it supplies.
module Evaluation.Overload
  ( ArgumentSchema
  , argumentSlotSchema
  , dependentArgumentSlotSchema
  , orderedArgumentSchema
  , unorderedArgumentSchema
  , concatenatedArgumentSchema
  , projectedArgumentSchema
  , argumentSchemaBindings
  , argumentSchemaDomain
  , argumentSchemaPositionalDomain
  , argumentSchemaVariadicElementType
  , argumentSchemaValuesComplete
  , argumentValuesComplete
  , overloadArgumentSchemaComplete
  , overloadValues
  , safeOverloadValues
  , overloadValuesComplete
  ) where

import Control.Applicative ((<|>))
import Control.Monad (foldM)
import Data.Foldable (traverse_)
import Data.List (nubBy, permutations, sortOn)
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import DatraLanguage.Identifier (public)
import Evaluation.Arguments
  ( argumentRows
  , makeArgumentMap
  , makeDistinctUnion
  , overloadArgumentRows
  )
import Evaluation.Access (accessValues)
import Evaluation.Construction (makeNatural)
import Evaluation.Either (makeEitherValue)
import Evaluation.Error
  ( InterpretingError (..)
  , OverloadFailure (..)
  )
import Evaluation.Identifier (simpleIdentifierTypeValue)
import Evaluation.Map (concatenateValues, makeAtlasMap)
import Evaluation.Specification (assignIdentifierValues, specifyValues)
import Evaluation.Value
import Numeric.Natural (Natural)

data ArgumentSchema
  = ArgumentSlotSchema
      Int
      (Maybe String)
      Bool
      Bool
      InterpretedValue
      (Maybe InterpretedValue)
  | OrderedArgumentSchema Natural [ArgumentSchema]
  | UnorderedArgumentSchema [ArgumentSchema]
  | ConcatenatedArgumentSchema ArgumentSchema ArgumentSchema
  | ProjectedArgumentSchema InterpretedValue
  | EmptyArgumentSchema

data Slot = Slot
  { slotIndex :: Int
  , slotName :: Maybe String
  , slotOptionalName :: Bool
  , slotDependentBinder :: Bool
  , slotAnnotation :: InterpretedValue
  , slotDefault :: Maybe InterpretedValue
  }

-- 'Nothing' records an explicit positional @*@.  Keeping it distinct from an
-- absent entry lets complete calls diagnose a skipped required slot while
-- partial overload expressions may still leave that slot as a type.
type Replacements = [(Int, Maybe InterpretedValue)]

-- | Overload the defaults and supplied values in a runtime value. Missing
-- non-defaulted slots remain types, which makes the operator useful for
-- incrementally constructing argument maps.
overloadValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
overloadValues templateValue supplied = do
  let template = normalizeArgumentSchema (argumentSchemaFromValue templateValue)
  replacements <- resolveReplacements template supplied
  buildTemplate replacements template

-- | Overload only slots without defaults, or slots whose supplied value is
-- canonically equal to their existing default. This preserves the partial
-- update behavior of 'overloadValues' while making defaults immutable.
safeOverloadValues
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
safeOverloadValues templateValue supplied = do
  let template = normalizeArgumentSchema (argumentSchemaFromValue templateValue)
      slots = templateSlots template
  replacements <- resolveReplacements template supplied
  traverse_ (preserveDefault slots) replacements
  buildTemplate replacements template

preserveDefault
  :: [Slot]
  -> (Int, Maybe InterpretedValue)
  -> Either InterpretingError ()
preserveDefault slots (index, replacement) =
  case replacement of
    Nothing -> Right ()
    Just replacementValue ->
      case slotDefault =<< findSlot index slots of
        Nothing -> Right ()
        Just defaultValue
          | interpretedCanonicalResult replacementValue
              == interpretedCanonicalResult defaultValue -> Right ()
          | otherwise -> Left (OverloadError OverloadChangedDefault)
  where
    findSlot _ [] = Nothing
    findSlot target (slot : remaining)
      | slotIndex slot == target = Just slot
      | otherwise = findSlot target remaining

-- | Function application uses the same operation, but additionally requires
-- every slot to have a supplied value, an explicit default, or a total type
-- annotation. The returned bindings contain the unwrapped values seen by the
-- function body.
overloadValuesComplete
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError (InterpretedValue, [(String, InterpretedValue)])
overloadValuesComplete templateValue =
  overloadArgumentSchemaComplete (argumentSchemaFromValue templateValue)

resolveReplacements
  :: ArgumentSchema
  -> InterpretedValue
  -> Either InterpretingError Replacements
resolveReplacements template supplied = do
  rows <- overloadArgumentRows supplied
  writtenRows <-
    case interpretedForm supplied of
      ArgumentMapForm members _ ->
        overloadArgumentRows (makeAtlasMap 2 members)
      _ -> pure rows
  let writtenOrder = templateSlots template
      slotOrders = templateSlotOrders template
      writtenRoutes =
        nubBy sameReplacements
          [ replacements
          | row <- writtenRows
          , replacements <- matchInputs writtenOrder row
          ]
      routes =
        [ concat
            [ matchInputs slots orderedInputs
            | slots <- slotOrders
            , orderedInputs <- inputOrders row
            ]
        | row <- rows
        ]
  if any null routes
    then Left (OverloadError OverloadNoMatch)
    else case writtenRoutes of
      -- Written order is the canonical positional interpretation. Prefer it
      -- even when equal annotations also admit other permutations.
      [replacements] -> Right replacements
      [] ->
        case nubBy sameReplacements (concat routes) of
          [] -> Left (OverloadError OverloadNoMatch)
          [replacements] -> Right replacements
          _ -> Left (OverloadError
            OverloadAmbiguousWithoutWrittenOrder)
      _ -> Left (OverloadError OverloadAmbiguousWrittenOrder)
  where
    sameReplacements left right = canonical left == canonical right
    canonical = sortOn fst . map
      (\(index, value) ->
        (index, interpretedCanonicalResult <$> value))
    inputOrders row
      | any hasName row = permutations row
      | otherwise = [row]
    hasName Nothing = False
    hasName (Just value) =
      case suppliedValue value of
        (Just _, _) -> True
        _ -> False

matchInputs :: [Slot] -> [Maybe InterpretedValue] -> [Replacements]
matchInputs _ [] = [[]]
matchInputs [] _ = []
matchInputs [slot] inputs
  | length inputs > 1
  , Just values <- sequence inputs
  , all unnamed values
  , Just grouped <- matchSlot slot (makeAtlasMap 2 values) =
      [[(slotIndex slot, Just grouped)]]
  where
    unnamed value = case suppliedValue value of
      (Nothing, _) -> True
      _ -> False
matchInputs (slot : remainingSlots) (Nothing : remainingInputs) =
  [ (slotIndex slot, Nothing) : later
  | later <- matchInputs remainingSlots remainingInputs
  ]
matchInputs (slot : remainingSlots)
    inputs@(Just input : remainingInputs) =
  case matchSlot slot input of
    Just value ->
      [ (slotIndex slot, Just value) : later
      | later <- matchInputs remainingSlots remainingInputs
      ]
    Nothing -> matchInputs remainingSlots inputs

matchSlot :: Slot -> InterpretedValue -> Maybe InterpretedValue
matchSlot slot input = do
  let (inputName, inputValue) = suppliedValue input
  case (slotName slot, inputName) of
    (Just expected, Just actual)
      | not (isPublicIdentifier expected)
      , not (slotDependentBinder slot) -> Nothing
      | expected == actual
      , not (slotDependentBinder slot) || suppliedAsAssignment input -> pure ()
      | otherwise -> Nothing
    -- A missing source name is positional. Required and optional target names
    -- differ in whether omission is allowed, not in whether a supplied value
    -- may acquire that name through deterministic argument matching.
    (Just _, Nothing)
      | slotDependentBinder slot && not (slotOptionalName slot) -> Nothing
      | otherwise -> pure ()
    (Nothing, Nothing) -> pure ()
    (Nothing, Just _) -> Nothing
  case specifyValues inputValue (slotAnnotation slot) of
    Right prepared
      | DependentSumForm _ <- interpretedForm (slotAnnotation slot) ->
          Just prepared
      | otherwise -> Just inputValue
    Left _ -> Nothing

isPublicIdentifier :: String -> Bool
isPublicIdentifier identifier =
  not (null (public [(identifier, ())]))

suppliedValue :: InterpretedValue -> (Maybe String, InterpretedValue)
suppliedValue value =
  case optionalNamedParts value of
    Just (name, _, Just supplied) -> (Just name, supplied)
    _ ->
      case namedParts value of
        Just (name, annotation, supplied) ->
          (Just name, maybe annotation id supplied)
        Nothing -> (Nothing, value)

suppliedAsAssignment :: InterpretedValue -> Bool
suppliedAsAssignment value =
  case interpretedForm value of
    AssignmentForm _ -> True
    _ -> case interpretedCanonicalResult value of
      CanonicalAssignment {} -> True
      _ -> False

templateSlots :: ArgumentSchema -> [Slot]
templateSlots template =
  case template of
    ArgumentSlotSchema index name optional dependent annotation defaultValue ->
      [Slot index name optional dependent annotation defaultValue]
    OrderedArgumentSchema _ children -> concatMap templateSlots children
    UnorderedArgumentSchema children -> concatMap templateSlots children
    ConcatenatedArgumentSchema left right ->
      templateSlots left <> templateSlots right
    ProjectedArgumentSchema _ -> []
    EmptyArgumentSchema -> []

-- Ordered maps retain one slot order. Argument maps contribute every member
-- order, so unnamed values remain ambiguous while named values normalize to
-- one replacement set. Concatenation preserves the order of its segments.
templateSlotOrders :: ArgumentSchema -> [[Slot]]
templateSlotOrders template =
  case template of
    ArgumentSlotSchema index name optional dependent annotation defaultValue ->
      [[Slot index name optional dependent annotation defaultValue]]
    OrderedArgumentSchema _ children -> combine children
    UnorderedArgumentSchema children ->
      concatMap combine (permutations children)
    ConcatenatedArgumentSchema left right ->
      [leftSlots <> rightSlots
      | leftSlots <- templateSlotOrders left
      , rightSlots <- templateSlotOrders right
      ]
    ProjectedArgumentSchema _ -> [[]]
    EmptyArgumentSchema -> [[]]
  where
    combine children =
      map concat (sequence (map templateSlotOrders children))

argumentSchemaFromValue :: InterpretedValue -> ArgumentSchema
argumentSchemaFromValue value = fst (fromValue 0 value)
  where
    fromValue next current =
      case optionalNamedParts current of
        Just (name, annotation, defaultValue) ->
          ( ArgumentSlotSchema next (Just name) True False annotation defaultValue
          , next + 1
          )
        Nothing ->
          case namedParts current of
            Just (name, annotation, defaultValue) ->
              ( ArgumentSlotSchema next (Just name) False False annotation defaultValue
              , next + 1
              )
            Nothing ->
              case interpretedForm current of
                ArgumentMapForm members _ ->
                  mapChildren UnorderedArgumentSchema next members
                ConcatenatedMapForm left right ->
                  let (leftTemplate, afterLeft) = fromValue next left
                      (rightTemplate, afterRight) =
                        fromValue afterLeft right
                  in ( ConcatenatedArgumentSchema leftTemplate rightTemplate
                     , afterRight
                     )
                SequentialMapForm ->
                  case finiteMembers current of
                    Just [] -> (EmptyArgumentSchema, next)
                    Just members ->
                      let (children, afterChildren) =
                            schemasFromValues next members
                      in ( OrderedArgumentSchema
                             (interpretedMapCardinality (interpretedMap current))
                             children
                         , afterChildren
                         )
                    Nothing -> slot current next
                MapForm ->
                  case finiteMembers current of
                    Just [] -> (EmptyArgumentSchema, next)
                    Just members ->
                      let (children, afterChildren) =
                            schemasFromValues next members
                      in ( OrderedArgumentSchema
                             (interpretedMapCardinality
                               (interpretedMap current))
                             children
                         , afterChildren
                         )
                    Nothing -> slot current next
                _ -> slot current next
    slot current next =
      (ArgumentSlotSchema next Nothing False False current Nothing, next + 1)
    mapChildren constructor start members =
      let (children, afterChildren) = schemasFromValues start members
      in (constructor children, afterChildren)
    schemasFromValues next [] = ([], next)
    schemasFromValues next (member : remaining) =
      let (schema, afterSchema) = fromValue next member
          (schemas, finalIndex) =
            schemasFromValues afterSchema remaining
      in (schema : schemas, finalIndex)

normalizeArgumentSchema :: ArgumentSchema -> ArgumentSchema
normalizeArgumentSchema schema = fst (go 0 schema)
  where
    go next current =
      case current of
        ArgumentSlotSchema _ name optional dependent annotation defaultValue ->
          ( ArgumentSlotSchema next name optional dependent annotation defaultValue
          , next + 1
          )
        OrderedArgumentSchema cardinality children ->
          let (normalized, afterChildren) = normalizeChildren next children
          in (OrderedArgumentSchema cardinality normalized, afterChildren)
        UnorderedArgumentSchema children ->
          let (normalized, afterChildren) = normalizeChildren next children
          in (UnorderedArgumentSchema normalized, afterChildren)
        ConcatenatedArgumentSchema left right ->
          let (normalizedLeft, afterLeft) = go next left
              (normalizedRight, afterRight) = go afterLeft right
          in (ConcatenatedArgumentSchema normalizedLeft normalizedRight, afterRight)
        ProjectedArgumentSchema target ->
          (ProjectedArgumentSchema target, next)
        EmptyArgumentSchema -> (EmptyArgumentSchema, next)
    normalizeChildren next [] = ([], next)
    normalizeChildren next (child : remaining) =
      let (normalized, afterChild) = go next child
          (normalizedRemaining, finalIndex) =
            normalizeChildren afterChild remaining
      in (normalized : normalizedRemaining, finalIndex)

argumentSlotSchema
  :: Maybe String
  -> Bool
  -> InterpretedValue
  -> Maybe InterpretedValue
  -> ArgumentSchema
argumentSlotSchema name optional annotation defaultValue =
  ArgumentSlotSchema 0 name optional False annotation defaultValue

dependentArgumentSlotSchema
  :: String
  -> Bool
  -> InterpretedValue
  -> ArgumentSchema
dependentArgumentSlotSchema name optional annotation =
  ArgumentSlotSchema 0 (Just name) optional True annotation Nothing

orderedArgumentSchema :: Natural -> [ArgumentSchema] -> ArgumentSchema
orderedArgumentSchema = OrderedArgumentSchema

unorderedArgumentSchema :: [ArgumentSchema] -> ArgumentSchema
unorderedArgumentSchema = UnorderedArgumentSchema

concatenatedArgumentSchema :: [ArgumentSchema] -> ArgumentSchema
concatenatedArgumentSchema schemas =
  case schemas of
    [] -> EmptyArgumentSchema
    first : remaining -> foldl ConcatenatedArgumentSchema first remaining

projectedArgumentSchema :: InterpretedValue -> ArgumentSchema
projectedArgumentSchema = ProjectedArgumentSchema

argumentSchemaBindings :: ArgumentSchema -> [(String, InterpretedValue)]
argumentSchemaBindings schema =
  case schema of
    ArgumentSlotSchema _ (Just name) _ _ annotation _ -> [(name, annotation)]
    ArgumentSlotSchema _ Nothing _ _ _ _ -> []
    OrderedArgumentSchema _ children -> concatMap argumentSchemaBindings children
    UnorderedArgumentSchema children -> concatMap argumentSchemaBindings children
    ConcatenatedArgumentSchema left right ->
      argumentSchemaBindings left <> argumentSchemaBindings right
    ProjectedArgumentSchema _ -> []
    EmptyArgumentSchema -> []

argumentSchemaDomain
  :: ArgumentSchema
  -> Either InterpretingError InterpretedValue
argumentSchemaDomain schema =
  case schema of
    ArgumentSlotSchema _ Nothing _ _ annotation _ -> pure annotation
    ArgumentSlotSchema _ (Just name) optional _ annotation _ -> do
      let named = simpleIdentifierTypeValue name annotation
      if optional then makeEitherValue named annotation else pure named
    OrderedArgumentSchema cardinality children ->
      makeAtlasMap cardinality <$> traverse argumentSchemaDomain children
    UnorderedArgumentSchema children ->
      traverse argumentSchemaDomain children >>= makeArgumentMap
    ConcatenatedArgumentSchema _ _ -> do
      alternatives <- schemaPages schema
      let presentations = map (makeAtlasMap 2) alternatives
      case nubBy sameValue presentations of
        [] -> pure (makeAtlasMap 0 [])
        first : remaining -> foldM makeEitherValue first remaining
    ProjectedArgumentSchema target -> pure target
    EmptyArgumentSchema -> pure (makeAtlasMap 0 [])
  where
    sameValue left right =
      interpretedCanonicalResult left == interpretedCanonicalResult right
    schemaPages current =
      case current of
        OrderedArgumentSchema _ entries ->
          (:[]) <$> traverse argumentSchemaDomain entries
        unordered@(UnorderedArgumentSchema _) ->
          argumentSchemaDomain unordered >>= argumentRows
        ConcatenatedArgumentSchema left right ->
          (\(leftPages, rightPages) ->
              [leftPage <> rightPage
              | leftPage <- leftPages
              , rightPage <- rightPages])
            <$> ((,) <$> schemaPages left <*> schemaPages right)
        ProjectedArgumentSchema target -> argumentRows target
        EmptyArgumentSchema -> pure [[]]
        entry -> (\value -> [[value]]) <$> argumentSchemaDomain entry

-- | The function body's implicit @it@ observes slots positionally.  Its
-- inference view therefore erases parameter names and defaults while keeping
-- the same written slot order used by overload resolution.
argumentSchemaPositionalDomain
  :: ArgumentSchema
  -> InterpretedValue
argumentSchemaPositionalDomain schema =
  case schema of
    ProjectedArgumentSchema target -> projectedPositionalDomain target
    _ -> makeAtlasMap 2
      [ slotAnnotation slot
      | slot <- templateSlots (normalizeArgumentSchema schema)
      ]

-- | A projected argument federation is consumed as a positional variadic
-- sequence inside a function body.  Its first positional member determines
-- the homogeneous element view used by source-defined prefix families such
-- as @Args T@; exact finite-prefix membership remains with the projection's
-- own dependent-sum validator.
argumentSchemaVariadicElementType
  :: ArgumentSchema
  -> Maybe InterpretedValue
argumentSchemaVariadicElementType schema =
  case schema of
    ProjectedArgumentSchema target ->
      either (const Nothing) Just
        (accessValues (projectedPositionalDomain target) (makeNatural 0))
    _ -> Nothing

-- A projected argument federation retains its public slot names for call
-- matching, but the function body's @it@ map is positional. Preserve the
-- family itself and erase names only after a page has been selected.
projectedPositionalDomain :: InterpretedValue -> InterpretedValue
projectedPositionalDomain target =
  case interpretedForm target of
    DependentSumForm dependent
      | Just project <- evaluatedDependentSumAccess dependent ->
          withDependentSumAccess
            (\insertion -> project insertion >>= eraseNames)
            target
    EitherForm alternatives ->
      case makeDistinctUnion
          [ projectedPositionalDomain (evaluatedEitherLeft alternatives)
          , projectedPositionalDomain (evaluatedEitherRight alternatives)
          ] of
        Right value -> value
        Left _ -> target
    _ -> target
  where
    eraseNames value =
      case interpretedForm value of
        DependentIdentifierTypeForm identifier ->
          eraseNames (evaluatedIdentifierUnderlying identifier)
        EitherForm alternatives ->
          traverse eraseNames
            [ evaluatedEitherLeft alternatives
            , evaluatedEitherRight alternatives
            ]
            >>= makeDistinctUnion
        _ -> Right value

-- | Complete the schema and expose the resulting values in written positional
-- order.  This is the map bound to a function body's implicit @it@ name.
argumentSchemaValuesComplete
  :: ArgumentSchema
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
argumentSchemaValuesComplete schema supplied =
  case schema of
    ProjectedArgumentSchema target -> specifyValues supplied target
    _ -> do
      let normalized = normalizeArgumentSchema schema
      replacements <- resolveReplacements normalized supplied
      completed <- traverse (completeSlot replacements) (templateSlots normalized)
      pure (makeAtlasMap 2 (map snd completed))

-- | Complete an evaluated argument-map type and expose its values in the
-- type's canonical positional order.  Dependent projections use this same
-- machinery, so named and positional calls cannot acquire separate rules.
argumentValuesComplete
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
argumentValuesComplete template =
  argumentSchemaValuesComplete (argumentSchemaFromValue template)

overloadArgumentSchemaComplete
  :: ArgumentSchema
  -> InterpretedValue
  -> Either InterpretingError (InterpretedValue, [(String, InterpretedValue)])
overloadArgumentSchemaComplete schema supplied =
  case schema of
    ProjectedArgumentSchema target -> do
      prepared <- specifyValues supplied target
      pure (prepared, [])
    _ -> do
      let normalized = normalizeArgumentSchema schema
      replacements <- resolveReplacements normalized supplied
      completed <- traverse (completeSlot replacements) (templateSlots normalized)
      result <- buildTemplate replacements normalized
      pure (result, [(name, value) | (Just name, value) <- completed])

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
  case lookup (slotIndex slot) replacements of
    Just (Just value) -> Right (slotName slot, value)
    Just Nothing -> fillSlot OverloadSkippedRequiredSlot
    Nothing -> fillSlot OverloadMissingRequiredSlot
  where
    fillSlot failure =
      case slotDefault slot of
        Just value -> Right (slotName slot, value)
        Nothing
          | interpretedTypeIsTotal (slotAnnotation slot) ->
              Right (slotName slot, slotAnnotation slot)
          | otherwise ->
              let empty = makeAtlasMap 0 []
              in case specifyValues empty (slotAnnotation slot) of
                Right _ -> Right (slotName slot, empty)
                Left _ -> Left (OverloadError failure)

buildTemplate
  :: Replacements
  -> ArgumentSchema
  -> Either InterpretingError InterpretedValue
buildTemplate replacements template =
  case template of
    ArgumentSlotSchema index name optional dependent annotation defaultValue ->
      buildSlot name optional dependent annotation
        (replacementAt index replacements <|> defaultValue)
    OrderedArgumentSchema cardinality children ->
      makeAtlasMap cardinality <$> traverse (buildTemplate replacements) children
    UnorderedArgumentSchema children ->
      traverse (buildTemplate replacements) children >>= makeArgumentMap
    ConcatenatedArgumentSchema left right ->
      do
        leftValue <- buildTemplate replacements left
        rightValue <- buildTemplate replacements right
        concatenateValues leftValue rightValue
    ProjectedArgumentSchema target -> Right target
    EmptyArgumentSchema -> Right (makeAtlasMap 0 [])

replacementAt :: Int -> Replacements -> Maybe InterpretedValue
replacementAt index replacements =
  case lookup index replacements of
    Just (Just value) -> Just value
    _ -> Nothing

buildSlot
  :: Maybe String
  -> Bool
  -> Bool
  -> InterpretedValue
  -> Maybe InterpretedValue
  -> Either InterpretingError InterpretedValue
buildSlot Nothing _ _ annotation supplied =
  Right (maybe annotation id supplied)
buildSlot (Just name) optional dependent annotation supplied = do
  present <-
    case supplied of
      Nothing -> Right (simpleIdentifierTypeValue name annotation)
      Just value
        | not (isPublicIdentifier name) && not dependent -> do
            _ <- specifyValues value annotation
            Right (simpleIdentifierTypeValue name value)
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
