-- | Default-bearing map overloading. The left operand supplies the shape and
-- defaults; the right operand is matched against the same shape with those
-- defaults erased, then replaces only the slots it supplies.
module Evaluation.Overload
  ( ArgumentSchema
  , argumentSchemaFromValue
  , argumentSlotSchema
  , dependentArgumentSlotSchema
  , inferredArgumentSlotSchema
  , orderedArgumentSchema
  , unorderedArgumentSchema
  , concatenatedArgumentSchema
  , projectedArgumentSchema
  , argumentSchemaBindings
  , argumentSchemaDomain
  , argumentSchemaBodyDomain
  , argumentSchemaBodyValues
  , argumentSchemaPositionalDomain
  , argumentSchemaVariadicElementType
  , argumentSchemaValuesComplete
  , optionalArgumentSlot
  , argumentValuesComplete
  , omegaArgumentValuesComplete
  , overloadArgumentSchemaComplete
  , overloadArgumentSchemaCompleteWithInferred
  , overloadValues
  , safeOverloadValues
  , overloadValuesComplete
  ) where

import Control.Applicative ((<|>))
import Control.Monad (foldM)
import Data.Foldable (traverse_)
import Data.List (nubBy, permutations, sortOn)
import DatraOrdinal
  ( finiteOrdinal
  , naturalAtOrdinal
  , omega
  , ordinalGT
  , ordinalGTE
  )
import DatraLanguage.Identifier (public)
import Evaluation.Arguments
  ( argumentRows
  , makeArgumentMap
  , makeDistinctUnion
  , overloadArgumentRows
  )
import Evaluation.Access (accessValues)
import Evaluation.Coalization (coalizeValue)
import Evaluation.Construction (makeNatural)
import Evaluation.Either (makeEitherValue)
import Evaluation.Error
  ( AtlasMapFederationOperation (AtlasMapFederationSpecification)
  , AtlasMapFederationRefutation
      (AtlasMapFederationSpecificationHasNoMatchingMember)
  , AtlasMapFederationUncertainty
      (NoAtlasMapFederationDecisionProcedure)
  , InterpretingError (..)
  , OverloadFailure (..)
  )
import Evaluation.Identifier (simpleIdentifierTypeValue)
import Evaluation.Map
  ( concatenateValues
  , isEmptyMap
  , makeAtlasMap
  , makeAtlasMapPreservingSingleton
  )
import Evaluation.Specification (assignIdentifierValues, specifyValues)
import Evaluation.Specification.ArgumentMap qualified as ArgumentMap
import Evaluation.Specification.Composition (selectFederationMember)
import Evaluation.Specification.Decision (Decision (..))
import Evaluation.Specification.Subfederation (decideValueSubfederation)
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
  | InferredArgumentSlotSchema Int String InterpretedValue
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
  , slotInferred :: Bool
  , slotAllowsPrivateName :: Bool
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
          | interpretedSemanticResult replacementValue
              == interpretedSemanticResult defaultValue -> Right ()
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
resolveReplacements template supplied
  | [slot] <- suppliedSlots
  , not (isSkip supplied)
  , Just value <- matchSlot (slotNames [slot]) slot supplied =
      Right [(slotIndex slot, Just value)]
  | otherwise = do
      let targetNames = slotNames suppliedSlots
          rowSource = case suppliedValue supplied of
            (Just name, underlying)
              | name `notElem` targetNames -> underlying
            _ -> supplied
      rows <- overloadArgumentRows rowSource
      writtenRows <-
        case interpretedForm rowSource of
          ArgumentMapForm members _ ->
            overloadArgumentRows (makeAtlasMap 2 members)
          _ -> pure rows
      let writtenOrder = suppliedSlots
          slotOrders = templateSlotOrders template
          writtenRoutes =
            nubBy sameReplacements
              [ replacements
              | row <- writtenRows
              , replacements <- matchInputs writtenOrder row
              ]
          routes =
            [ concat
                [ matchInputs slots row
                | slots <- slotOrders
                ]
            | row <- rows
            ]
      let routeResult =
            if any null routes
              then Left (OverloadError OverloadNoMatch)
              else case writtenRoutes of
                -- Written order is the canonical positional interpretation.
                -- Prefer it even when equal annotations admit permutations.
                [replacements] -> Right replacements
                [] ->
                  case nubBy sameReplacements (concat routes) of
                    [] -> Left (OverloadError OverloadNoMatch)
                    [replacements] -> Right replacements
                    _ -> Left (OverloadError
                      OverloadAmbiguousWithoutWrittenOrder)
                _ -> Left (OverloadError OverloadAmbiguousWrittenOrder)
      routeResult
  where
    suppliedSlots = filter (not . slotInferred) (templateSlots template)
    isSkip value = case interpretedForm value of
      SkipForm _ -> True
      _ -> False
    sameReplacements left right = canonical left == canonical right
    canonical = sortOn fst . map
      (\(index, value) ->
        (index, interpretedSemanticResult <$> value))

matchInputs :: [Slot] -> [Maybe InterpretedValue] -> [Replacements]
matchInputs slots inputs =
  case matchNamed slots inputs [] [] of
    Nothing -> []
    Just (remainingSlots, positionalInputs, named) ->
      map (reverse named <>)
        (matchPositional remainingSlots (reverse positionalInputs))
  where
    targetNames = slotNames slots

    matchNamed remaining [] positional named =
      Just (remaining, positional, named)
    matchNamed remaining (input : laterInputs) positional named =
      case admittedInputName input of
        Nothing ->
          matchNamed remaining laterInputs (input : positional) named
        Just name ->
          case removeNamedSlot name remaining of
            Nothing ->
              matchNamed remaining laterInputs (input : positional) named
            Just (slot, laterSlots) -> do
              value <- input >>= matchSlot targetNames slot
              matchNamed laterSlots laterInputs positional
                ((slotIndex slot, Just value) : named)

    admittedInputName Nothing = Nothing
    admittedInputName (Just value) =
      case suppliedValue value of
        (Just name, _) | name `elem` targetNames -> Just name
        _ -> Nothing

    removeNamedSlot _ [] = Nothing
    removeNamedSlot name (slot : remaining)
      | slotName slot == Just name = Just (slot, remaining)
      | otherwise = do
          (selected, later) <- removeNamedSlot name remaining
          pure (selected, slot : later)

    matchPositional _ [] = [[]]
    matchPositional [] _ = []
    matchPositional [slot] positional
      | length positional > 1
      , Just values <- traverse
          (>>= positionalInput targetNames)
          positional
      , Just grouped <- matchSlot
          targetNames slot (makeAtlasMap 2 values) =
          [[(slotIndex slot, Just grouped)]]
    matchPositional (slot : remainingSlots)
        (Nothing : remainingInputs) =
      [ (slotIndex slot, Nothing) : later
      | later <- matchPositional remainingSlots remainingInputs
      ]
    matchPositional (slot : remainingSlots)
        positional@(Just input : remainingInputs) =
      case matchSlot targetNames slot input of
        Just value ->
          [ (slotIndex slot, Just value) : later
          | later <- matchPositional remainingSlots remainingInputs
          ]
        Nothing -> matchPositional remainingSlots positional

-- An identifier not admitted by any target slot participates in the
-- positional pass.  Erase it before collecting several remaining inputs into
-- one variadic slot; otherwise the grouped value still carries labels and
-- cannot inhabit an ordinary sequence such as @List T@.
positionalInput :: [String] -> InterpretedValue -> Maybe InterpretedValue
positionalInput targetNames input =
  case suppliedValue input of
    (Nothing, value) -> positionalContents targetNames value
    (Just name, value)
      | name `notElem` targetNames -> positionalContents targetNames value
      | otherwise -> Nothing

positionalContents :: [String] -> InterpretedValue -> Maybe InterpretedValue
positionalContents targetNames value =
  case interpretedForm value of
    CoalizationForm operand -> positionalContents targetNames operand
    ArgumentMapForm members _ ->
      makeAtlasMap 2 <$> traverse (positionalInput targetNames) members
    SequentialMapForm -> do
      members <- finiteMembers value
      makeAtlasMap
        (interpretedMapCardinality (interpretedMap value))
        <$> traverse (positionalInput targetNames) members
    _ -> Just value

slotNames :: [Slot] -> [String]
slotNames = foldr (maybe id (:) . slotName) []

matchSlot :: [String] -> Slot -> InterpretedValue -> Maybe InterpretedValue
matchSlot targetNames slot input = do
  let (suppliedName, suppliedInput) =
        case slotName slot of
          Nothing -> (Nothing, input)
          Just _ -> suppliedValue input
      inputName = case suppliedName of
        Just name | name `notElem` targetNames -> Nothing
        _ -> suppliedName
  case (slotName slot, inputName) of
    (Just expected, Just actual)
      | not (isPublicIdentifier expected)
      , not (slotAllowsPrivateName slot)
      , not (slotDependentBinder slot) -> Nothing
      | expected == actual
      , not (slotDependentBinder slot) || suppliedAsAssignment input -> pure ()
      | otherwise -> Nothing
    (Just _, Nothing)
      | slotOptionalName slot -> pure ()
      | otherwise -> Nothing
    (Nothing, Nothing) -> pure ()
    (Nothing, Just _) -> Nothing
  case
      [ matched
      | inputValue <- suppliedInput : positionalFallback inputName
      , Just matched <- [matchInputValue inputValue]
      ] of
    matched : _ -> Just matched
    [] -> Nothing
  where
    positionalFallback Nothing =
      maybe [] (:[]) (positionalInput targetNames input)
    positionalFallback (Just _) = []
    matchInputValue inputValue =
      case specifyValues inputValue (slotAnnotation slot) of
        Right prepared
          | DependentSumForm _ <- interpretedForm (slotAnnotation slot) ->
              Just prepared
          | DecisionProved () <-
              decideValueSubfederation inputValue (slotAnnotation slot) ->
              Just inputValue
          | otherwise -> Just prepared
        Left _ -> Nothing

isPublicIdentifier :: String -> Bool
isPublicIdentifier identifier =
  not (null (public [(identifier, ())]))

suppliedValue :: InterpretedValue -> (Maybe String, InterpretedValue)
suppliedValue value =
  case interpretedForm value of
    CoalizationForm operand ->
      case suppliedValue operand of
        (Just name, supplied) -> (Just name, coalizeValue supplied)
        _ -> ordinary
    _ -> ordinary
  where
    ordinary =
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
    _ -> case interpretedSemanticResult value of
      CanonicalAssignment {} -> True
      _ -> False

templateSlots :: ArgumentSchema -> [Slot]
templateSlots = slots True
  where
    slots allowsPrivateName template = case template of
      ArgumentSlotSchema index name optional dependent annotation defaultValue ->
        [Slot index name optional dependent False allowsPrivateName annotation defaultValue]
      InferredArgumentSlotSchema index name annotation ->
        [Slot index (Just name) False True True allowsPrivateName annotation
          (Just annotation)]
      OrderedArgumentSchema _ children -> concatMap (slots True) children
      UnorderedArgumentSchema children -> concatMap (slots False) children
      ConcatenatedArgumentSchema left right ->
        slots allowsPrivateName left <> slots allowsPrivateName right
      ProjectedArgumentSchema _ -> []
      EmptyArgumentSchema -> []

-- Ordered maps retain one slot order. Argument maps contribute every member
-- order, so unnamed values remain ambiguous while named values normalize to
-- one replacement set. Concatenation preserves the order of its segments.
templateSlotOrders :: ArgumentSchema -> [[Slot]]
templateSlotOrders = orders True
  where
    orders allowsPrivateName template = case template of
      ArgumentSlotSchema index name optional dependent annotation defaultValue ->
        [[Slot index name optional dependent False allowsPrivateName annotation defaultValue]]
      InferredArgumentSlotSchema {} -> [[]]
      OrderedArgumentSchema _ children -> combine True children
      UnorderedArgumentSchema children ->
        concatMap (combine False) (permutations children)
      ConcatenatedArgumentSchema left right ->
        [leftSlots <> rightSlots
        | leftSlots <- orders allowsPrivateName left
        , rightSlots <- orders allowsPrivateName right
        ]
      ProjectedArgumentSchema _ -> [[]]
      EmptyArgumentSchema -> [[]]
    combine allowsPrivateName children =
      map concat (sequence (map (orders allowsPrivateName) children))

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
              fromComposite next current
    fromComposite next current =
      case interpretedForm current of
        ArgumentMapForm members _ ->
          mapChildren unorderedArgumentSchema next members
        ConcatenatedMapForm left right ->
          let (leftTemplate, afterLeft) = fromProjected next left
              (rightTemplate, afterRight) = fromProjected afterLeft right
          in ( concatenatedArgumentSchema [leftTemplate, rightTemplate]
             , afterRight
             )
        SequentialMapForm -> fromFiniteMap next current
        MapForm -> fromFiniteMap next current
        _ -> slot current next
    fromFiniteMap next current =
      case finiteMembers current of
        Just [] -> (EmptyArgumentSchema, next)
        Just members ->
          let (children, afterChildren) = schemasFromSlots next members
          in ( OrderedArgumentSchema
                 (interpretedMapCardinality (interpretedMap current))
                 children
             , afterChildren
             )
        Nothing -> slot current next
    slot current next =
      (ArgumentSlotSchema next Nothing False False current Nothing, next + 1)
    fromProjected next current
      | isEmptyMap current = (EmptyArgumentSchema, next)
      | CoalizationForm operand <- interpretedForm current =
          fromValue next operand
      | hasDependentArgumentFamily current =
          (ProjectedArgumentSchema current, next)
      | otherwise = fromValue next current
    mapChildren constructor start members =
      let (children, afterChildren) = schemasFromValues start members
      in (constructor children, afterChildren)
    schemasFromValues next [] = ([], next)
    schemasFromValues next (member : remaining) =
      let (schema, afterSchema) = fromValue next member
          (schemas, finalIndex) =
            schemasFromValues afterSchema remaining
      in (schema : schemas, finalIndex)
    schemasFromSlots next [] = ([], next)
    schemasFromSlots next (member : remaining) =
      let (schema, afterSchema) = directSlot next member
          (schemas, finalIndex) =
            schemasFromSlots afterSchema remaining
      in (schema : schemas, finalIndex)
    directSlot next current =
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
            Nothing -> slot current next

normalizeArgumentSchema :: ArgumentSchema -> ArgumentSchema
normalizeArgumentSchema schema = fst (go 0 schema)
  where
    go next current =
      case current of
        ArgumentSlotSchema _ name optional dependent annotation defaultValue ->
          ( ArgumentSlotSchema next name optional dependent annotation defaultValue
          , next + 1
          )
        InferredArgumentSlotSchema _ name annotation ->
          (InferredArgumentSlotSchema next name annotation, next + 1)
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

inferredArgumentSlotSchema
  :: String
  -> InterpretedValue
  -> ArgumentSchema
inferredArgumentSlotSchema name annotation =
  InferredArgumentSlotSchema 0 name annotation

orderedArgumentSchema :: Natural -> [ArgumentSchema] -> ArgumentSchema
orderedArgumentSchema = OrderedArgumentSchema

unorderedArgumentSchema :: [ArgumentSchema] -> ArgumentSchema
unorderedArgumentSchema schemas =
  case schemas of
    -- A singleton projected family has no alternate argument-map ordering.
    -- Keep the projection visible so its dependent fibres can prepare calls
    -- and construct the named value exposed to the function body.
    [projected@ProjectedArgumentSchema {}] -> projected
    _ -> UnorderedArgumentSchema schemas

concatenatedArgumentSchema :: [ArgumentSchema] -> ArgumentSchema
concatenatedArgumentSchema = foldl append EmptyArgumentSchema
  where
    append EmptyArgumentSchema right = right
    append left EmptyArgumentSchema = left
    append left right = ConcatenatedArgumentSchema left right

projectedArgumentSchema :: InterpretedValue -> ArgumentSchema
projectedArgumentSchema target
  | CoalizationForm operand <- interpretedForm target =
      argumentSchemaFromValue operand
  | hasDependentArgumentFamily target = ProjectedArgumentSchema target
  | otherwise = argumentSchemaFromValue target

hasDependentArgumentFamily :: InterpretedValue -> Bool
hasDependentArgumentFamily value = case interpretedForm value of
  DependentSumForm _ -> True
  EitherForm alternatives ->
    hasDependentArgumentFamily (evaluatedEitherLeft alternatives)
      || hasDependentArgumentFamily (evaluatedEitherRight alternatives)
  _ -> False

argumentSchemaBindings :: ArgumentSchema -> [(String, InterpretedValue)]
argumentSchemaBindings schema =
  case schema of
    ArgumentSlotSchema _ (Just name) _ _ annotation _ -> [(name, annotation)]
    ArgumentSlotSchema _ Nothing _ _ _ _ -> []
    InferredArgumentSlotSchema _ name annotation -> [(name, annotation)]
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
    InferredArgumentSlotSchema _ name annotation ->
      pure (simpleIdentifierTypeValue name annotation)
    OrderedArgumentSchema cardinality children ->
      makeAtlasMap cardinality <$> traverse argumentSchemaDomain children
    UnorderedArgumentSchema children -> do
      members <- traverse argumentSchemaDomain children
      case makeArgumentMap members of
        Right domain -> Right domain
        -- The runtime schema retains unordered routing and gives the written
        -- positional order priority. When optional labels make its permuted
        -- federation overlap, keep that written presentation as the semantic
        -- function domain instead of rejecting an otherwise callable schema.
        Left EitherAlternativesNotDistinct -> Right (makeAtlasMap 2 members)
        Left failure -> Left failure
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
      interpretedSemanticResult left == interpretedSemanticResult right
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

-- | The body sees completed slots in written order, with names retained even
-- when a caller supplies an optional name positionally.
argumentSchemaBodyDomain :: ArgumentSchema -> InterpretedValue
argumentSchemaBodyDomain schema = case schema of
  ProjectedArgumentSchema target -> projectedBodyDomain target
  _ -> bodyAggregate normalized
    [ namedSlot (slotName slot, slotAnnotation slot)
    | slot <- templateSlots normalized
    ]
  where
    normalized = normalizeArgumentSchema schema

-- Projection selects ordinary schemas, including optional names. The body
-- always sees their completed, named form, independently of library spelling.
projectedBodyDomain :: InterpretedValue -> InterpretedValue
projectedBodyDomain target = case interpretedForm target of
  DependentSumForm dependent
    | Just project <- evaluatedDependentSumAccess dependent ->
        withDependentSumAccess
          (fmap (argumentSchemaBodyDomain . argumentSchemaFromValue) . project)
          target
  EitherForm alternatives -> target
    { interpretedForm = EitherForm alternatives
        { evaluatedEitherLeft = projectedBodyDomain (evaluatedEitherLeft alternatives)
        , evaluatedEitherRight = projectedBodyDomain (evaluatedEitherRight alternatives) } }
  _ -> argumentSchemaBodyDomain (argumentSchemaFromValue target)

namedSlot :: (Maybe String, InterpretedValue) -> InterpretedValue
namedSlot (name, value) = maybe value (`simpleIdentifierTypeValue` value) name

argumentSchemaBodyValues
  :: ArgumentSchema -> InterpretedValue
  -> Either InterpretingError InterpretedValue
argumentSchemaBodyValues schema supplied = case schema of
  ProjectedArgumentSchema target -> do
    selected <- specifyValues supplied target
    argumentSchemaBodyValues (argumentSchemaFromValue selected) selected
  _ -> do
    let normalized = normalizeArgumentSchema schema
    replacements <- resolveReplacements normalized supplied
    completed <- traverse (completeSlot replacements) (templateSlots normalized)
    pure (bodyAggregate normalized (map namedSlot completed))

-- A direct unnamed domain such as @Nat -> Nat@ exposes its sole value as
-- @_it@. Named and structurally composite domains expose a positional Atlas
-- map, so their singleton boundary remains meaningful.
bodyAggregate :: ArgumentSchema -> [InterpretedValue] -> InterpretedValue
bodyAggregate schema values =
  case schema of
    ArgumentSlotSchema _ Nothing _ _ _ _ -> makeAtlasMap 2 values
    _ -> makeAtlasMapPreservingSingleton 2 values

-- | Values-only view of the written slots, used to infer identifier erasure.
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

-- | A projected finite-prefix family erases to the homogeneous sequence
-- whose element is exposed by its first nonempty page. Exact call membership
-- remains the responsibility of the projected family itself.
argumentSchemaVariadicElementType
  :: ArgumentSchema
  -> Maybe InterpretedValue
argumentSchemaVariadicElementType schema =
  case schema of
    ProjectedArgumentSchema target ->
      either (const Nothing) Just
        (accessValues (projectedPositionalDomain target) (makeNatural 0))
    _ -> Nothing

-- The erased view of a projected argument federation preserves the family
-- and removes identifier wrappers after a page has been selected.
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
-- order, without identifier wrappers.
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

-- | Complete an evaluated argument-map type and expose named slots in the
-- type's canonical positional order. Dependent projections use this same
-- machinery, so named and positional calls cannot acquire separate rules.
argumentValuesComplete
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
argumentValuesComplete template =
  argumentSchemaBodyValues (argumentSchemaFromValue template)

-- | Select one argument-map fibre from a dependent federation whose index
-- order is at most omega.  Candidate indices come exclusively from the
-- retained dependent domain; source arity is used only to prove that a failed
-- candidate and every later, strictly larger candidate cannot fit.
omegaArgumentValuesComplete
  :: InterpretedValue
  -> InterpretedValue
  -> (InterpretedValue -> Either InterpretingError InterpretedValue)
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
omegaArgumentValuesComplete domain staticTarget fibreAt supplied = do
  let candidateOrder =
        interpretedMapFinalOrderType (interpretedMap domain)
  if ordinalGT candidateOrder omega
    then undecidable
    else do
      reservations <- decisionEither
        (ArgumentMap.argumentReservations
          selectFederationMember
          supplied
          [staticTarget])
      let positional =
            ArgumentMap.positionalArgumentSource reservations supplied
      suppliedOrder <- argumentOrder supplied
      search candidateOrder reservations positional suppliedOrder Nothing 0
  where
    search familyOrder reservations positional suppliedOrder previousOrder position
      | Just count <- naturalAtOrdinal familyOrder
      , position >= count = refuted
      | otherwise = do
          witness <- maybe undecidable Right
            (interpretedMapValueAt
              (interpretedMap domain)
              (finiteOrdinal position))
          candidate <- fibreAt witness
          orderType <- argumentOrder candidate
          candidateReservations <- decisionEither
            (ArgumentMap.argumentReservations
              selectFederationMember
              supplied
              [candidate])
          let admitsReserved = and
                (zipWith
                  (\reserved admitted -> not reserved || admitted)
                  reservations
                  candidateReservations)
              later = search familyOrder reservations positional
                suppliedOrder (Just orderType) (position + 1)
          if not admitsReserved
            then later
            else case argumentValuesComplete candidate positional of
              Right selected -> Right selected
              Left failure
                | ordinalGTE orderType suppliedOrder -> Left failure
                | Just previous <- previousOrder
                , not (ordinalGT orderType previous) -> undecidable
                | otherwise -> later

    argumentOrder value = do
      rows <- argumentRows value
      case nubBy (==)
          [finiteOrdinal (fromIntegral (length row)) | row <- rows] of
        [orderType] -> Right orderType
        _ -> undecidable

    decisionEither decision =
      case decision of
        DecisionProved value -> Right value
        DecisionRefuted -> refuted
        DecisionUndecidable -> undecidable

    refuted = Left
      (AtlasMapFederationOperationRefuted
        AtlasMapFederationSpecificationHasNoMatchingMember)
    undecidable = Left
      (AtlasMapFederationOperationUndecidable
        (NoAtlasMapFederationDecisionProcedure
          AtlasMapFederationSpecification))

overloadArgumentSchemaComplete
  :: ArgumentSchema
  -> InterpretedValue
  -> Either InterpretingError (InterpretedValue, [(String, InterpretedValue)])
overloadArgumentSchemaComplete = overloadArgumentSchemaCompleteWithInferred []

overloadArgumentSchemaCompleteWithInferred
  :: [(String, InterpretedValue)]
  -> ArgumentSchema
  -> InterpretedValue
  -> Either InterpretingError (InterpretedValue, [(String, InterpretedValue)])
overloadArgumentSchemaCompleteWithInferred inferred schema supplied =
  case schema of
    ProjectedArgumentSchema _ -> do
      prepared <- argumentSchemaBodyValues schema supplied
      pure (prepared, [])
    _ -> do
      let normalized = normalizeArgumentSchema schema
      replacements <- resolveReplacements normalized supplied
      let slots = templateSlots normalized
      completed <- traverse (completeSlotWithInferred inferred replacements) slots
      let prepared = bodyAggregate normalized (map namedSlot completed)
      pure (prepared, [(name, value) | (Just name, value) <- completed])

completeSlotWithInferred
  :: [(String, InterpretedValue)]
  -> Replacements
  -> Slot
  -> Either InterpretingError (Maybe String, InterpretedValue)
completeSlotWithInferred inferred replacements slot
  | slotInferred slot
  , Just name <- slotName slot
  , Just value <- lookup name inferred = Right (Just name, value)
  | otherwise = completeSlot replacements slot

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
  if interpretedSemanticResult annotation
      == interpretedSemanticResult (evaluatedEitherRight alternatives)
    then Just parts
    else Nothing

-- | Observe an optional identifier slot without exposing its internal Either
-- representation across the DatraTypes boundary.
optionalArgumentSlot :: InterpretedValue -> Maybe (String, InterpretedValue)
optionalArgumentSlot value = do
  (name, annotation, _) <- optionalNamedParts value
  pure (name, annotation)

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
    InferredArgumentSlotSchema _ name annotation ->
      buildSlot (Just name) False True annotation (Just annotation)
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
