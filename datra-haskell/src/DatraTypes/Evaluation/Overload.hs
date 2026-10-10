-- | Default-bearing map overloading. The left operand supplies the shape and
-- defaults; the right operand is matched against the same shape with those
-- defaults erased, then replaces only the slots it supplies.
module Evaluation.Overload
  ( ArgumentSchema
  , GenericArgumentBinder (..)
  , argumentSchemaFromValue
  , argumentSlotSchema
  , dependentArgumentSlotSchema
  , genericArgumentSlotSchema
  , genericEvidenceArgumentSchema
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
  , suppliedArgumentValue
  , foliageArgumentValuesComplete
  , overloadArgumentSchemaComplete
  , overloadArgumentSchemaCompleteWithGenerics
  , overloadArgumentSchemaCompleteWithTrustedGenerics
  , argumentSchemaHasInferredGenerics
  , argumentSchemaInferredGenericNames
  , argumentSchemaValidationArgument
  , overloadValues
  , safeOverloadValues
  , overloadValuesComplete
  ) where

import Control.Applicative ((<|>))
import Control.Monad (foldM)
import Data.Foldable (traverse_)
import Data.List (nub, nubBy, permutations, sortOn)
import DatraLanguage.AST (GenericBinderId, GenericPolarity)
import DatraOrdinal
  ( finiteOrdinal
  , naturalAtOrdinal
  , omega
  , ordinalGT
  , ordinalGTE
  , ordinalLTE
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
import FoliageMap (foliageMap, foliageMapPositionAt)
import Numeric.Natural (Natural)

data GenericArgumentBinder = GenericArgumentBinder
  { genericArgumentBinderId :: GenericBinderId
  , genericArgumentPolarity :: GenericPolarity
  , genericArgumentName :: String
  , genericArgumentOptionalName :: Bool
  , genericArgumentInferred :: Bool
  }
  deriving (Eq, Show)

data ArgumentSchema
  = ArgumentSlotSchema
      Int
      (Maybe String)
      Bool
      Bool
      InterpretedValue
      (Maybe InterpretedValue)
  | GenericArgumentSlotSchema
      Int GenericArgumentBinder InterpretedValue
  | GenericEvidenceArgumentSchema [GenericBinderId] ArgumentSchema
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
  , slotGenericBinder :: Maybe GenericArgumentBinder
  , slotEvidenceBinders :: [GenericBinderId]
  , slotAllowsPrivateName :: Bool
  , slotAnnotation :: InterpretedValue
  , slotDefault :: Maybe InterpretedValue
  }

slotIsInferred :: Slot -> Bool
slotIsInferred slot =
  maybe False genericArgumentInferred (slotGenericBinder slot)

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
    suppliedSlots = filter (not . slotIsInferred) (templateSlots template)
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

-- | Observe the routing name and underlying value of one supplied argument.
-- Existential packaging uses the same name erasure as ordinary application
-- before splitting the generic prefix from its dependent fibre.
suppliedArgumentValue
  :: InterpretedValue
  -> (Maybe String, InterpretedValue)
suppliedArgumentValue = suppliedValue

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
        [Slot index name optional dependent Nothing [] allowsPrivateName
          annotation defaultValue]
      GenericArgumentSlotSchema index binder annotation ->
        [Slot index (Just (genericArgumentName binder))
          (genericArgumentOptionalName binder) True (Just binder) []
          allowsPrivateName annotation
          (if genericArgumentInferred binder then Just annotation else Nothing)]
      GenericEvidenceArgumentSchema binderIds child ->
        [slot
          { slotEvidenceBinders = nub (binderIds <> slotEvidenceBinders slot) }
        | slot <- slots allowsPrivateName child]
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
        [[Slot index name optional dependent Nothing [] allowsPrivateName
          annotation defaultValue]]
      GenericArgumentSlotSchema index binder annotation
        | genericArgumentInferred binder -> [[]]
        | otherwise ->
            [[Slot index (Just (genericArgumentName binder))
              (genericArgumentOptionalName binder) True (Just binder) []
              allowsPrivateName annotation Nothing]]
      GenericEvidenceArgumentSchema binderIds child ->
        [ [slot
            { slotEvidenceBinders =
                nub (binderIds <> slotEvidenceBinders slot) }
          | slot <- childSlots]
        | childSlots <- orders allowsPrivateName child]
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
        GenericArgumentSlotSchema _ binder annotation ->
          (GenericArgumentSlotSchema next binder annotation, next + 1)
        GenericEvidenceArgumentSchema binderIds child ->
          let (normalized, afterChild) = go next child
          in (GenericEvidenceArgumentSchema binderIds normalized, afterChild)
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

genericArgumentSlotSchema
  :: GenericArgumentBinder
  -> InterpretedValue
  -> ArgumentSchema
genericArgumentSlotSchema binder annotation =
  GenericArgumentSlotSchema 0 binder annotation

genericEvidenceArgumentSchema
  :: [GenericBinderId]
  -> ArgumentSchema
  -> ArgumentSchema
genericEvidenceArgumentSchema [] schema = schema
genericEvidenceArgumentSchema binderIds schema =
  GenericEvidenceArgumentSchema binderIds schema

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
hasDependentArgumentFamily value =
  case dependentSumView value of
    Just _ -> True
    Nothing -> case interpretedForm value of
      EitherForm alternatives ->
        hasDependentArgumentFamily (evaluatedEitherLeft alternatives)
          || hasDependentArgumentFamily (evaluatedEitherRight alternatives)
      _ -> False

argumentSchemaBindings :: ArgumentSchema -> [(String, InterpretedValue)]
argumentSchemaBindings schema =
  case schema of
    ArgumentSlotSchema _ (Just name) _ _ annotation _ -> [(name, annotation)]
    ArgumentSlotSchema _ Nothing _ _ _ _ -> []
    GenericArgumentSlotSchema _ binder annotation ->
      [(genericArgumentName binder, annotation)]
    GenericEvidenceArgumentSchema _ child -> argumentSchemaBindings child
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
  case projectedGenericInferenceParts (normalizeArgumentSchema schema) of
    Just (genericSlots, _, ProjectedArgumentSchema target) -> do
      prefix <- makeAtlasMapPreservingSingleton 2
        <$> traverse genericSlotDomain genericSlots
      concatenateValues prefix target
    _ -> ordinary schema
  where
    genericSlotDomain slot =
      case slotGenericBinder slot of
        Just binder -> do
          let named = simpleIdentifierTypeValue
                (genericArgumentName binder) (slotAnnotation slot)
          if genericArgumentOptionalName binder
            then makeEitherValue named (slotAnnotation slot)
            else pure named
        Nothing -> Left (OverloadError OverloadNoMatch)
    ordinary current =
      case current of
        ArgumentSlotSchema _ Nothing _ _ annotation _ -> pure annotation
        ArgumentSlotSchema _ (Just name) optional _ annotation _ -> do
          let named = simpleIdentifierTypeValue name annotation
          if optional then makeEitherValue named annotation else pure named
        GenericArgumentSlotSchema _ binder annotation -> do
          let named = simpleIdentifierTypeValue
                (genericArgumentName binder) annotation
          if genericArgumentOptionalName binder
            then makeEitherValue named annotation
            else pure named
        GenericEvidenceArgumentSchema _ child -> argumentSchemaDomain child
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
    sameValue left right =
      interpretedSemanticResult left == interpretedSemanticResult right
    schemaPages current =
      case current of
        GenericEvidenceArgumentSchema _ child -> schemaPages child
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
  GenericEvidenceArgumentSchema _ child -> argumentSchemaBodyDomain child
  _ -> bodyAggregate normalized
    [ namedSlot (slotName slot, slotAnnotation slot)
    | slot <- templateSlots normalized
    ]
  where
    normalized = normalizeArgumentSchema schema

-- Projection selects ordinary schemas, including optional names. The body
-- always sees their completed, named form, independently of library spelling.
projectedBodyDomain :: InterpretedValue -> InterpretedValue
projectedBodyDomain target =
  case dependentSumView target >>= evaluatedDependentSumAccess of
    Just project ->
      withDependentSumAccess
        (fmap (argumentSchemaBodyDomain . argumentSchemaFromValue) . project)
        target
    Nothing -> case interpretedForm target of
      EitherForm alternatives -> target
        { interpretedForm = EitherForm alternatives
            { evaluatedEitherLeft =
                projectedBodyDomain (evaluatedEitherLeft alternatives)
            , evaluatedEitherRight =
                projectedBodyDomain (evaluatedEitherRight alternatives) } }
      _ -> argumentSchemaBodyDomain (argumentSchemaFromValue target)

namedSlot :: (Maybe String, InterpretedValue) -> InterpretedValue
namedSlot (name, value) = maybe value (`simpleIdentifierTypeValue` value) name

argumentSchemaBodyValues
  :: ArgumentSchema -> InterpretedValue
  -> Either InterpretingError InterpretedValue
argumentSchemaBodyValues schema supplied = case schema of
  ProjectedArgumentSchema target ->
    case orderedAtlasMapView target of
      Just _ -> foliageArgumentValuesComplete target supplied
      Nothing -> do
        selected <- specifyValues supplied target
        argumentSchemaBodyValues (argumentSchemaFromValue selected) selected
  GenericEvidenceArgumentSchema _ child ->
    argumentSchemaBodyValues child supplied
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
    GenericEvidenceArgumentSchema _ child -> bodyAggregate child values
    _ -> makeAtlasMapPreservingSingleton 2 values

-- | Values-only view of the written slots, used to infer identifier erasure.
argumentSchemaPositionalDomain
  :: ArgumentSchema
  -> InterpretedValue
argumentSchemaPositionalDomain schema =
  case schema of
    ProjectedArgumentSchema target -> projectedPositionalDomain target
    GenericEvidenceArgumentSchema _ child ->
      argumentSchemaPositionalDomain child
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
  case dependentSumView target >>= evaluatedDependentSumAccess of
    Just project ->
      withDependentSumAccess
        (\insertion -> project insertion >>= eraseNames)
        target
    Nothing -> case interpretedForm target of
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
    ProjectedArgumentSchema target ->
      case orderedAtlasMapView target of
        Just _ -> foliageArgumentValuesCompleteWith
          argumentSchemaValuesComplete target supplied
        Nothing -> do
          selected <- specifyValues supplied target
          argumentSchemaValuesComplete
            (argumentSchemaFromValue selected) selected
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

-- | Select the first matching page in a generic family's canonical foliage
-- traversal. Finite families are exhausted and may therefore be refuted. An
-- infinite family is observed only through a finite, source-derived frontier:
-- finding a page proves the application, while exhausting that frontier is
-- undecidable rather than a false refutation.
foliageArgumentValuesComplete
  :: InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
foliageArgumentValuesComplete =
  foliageArgumentValuesCompleteWith argumentSchemaBodyValues

-- Page selection is independent of the representation exposed afterwards.
-- Calls retain the selected page's identifiers for body bindings, while
-- values-only conversions erase them into canonical positional order.
foliageArgumentValuesCompleteWith
  :: (ArgumentSchema
      -> InterpretedValue
      -> Either InterpretingError InterpretedValue)
  -> InterpretedValue
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
foliageArgumentValuesCompleteWith complete family supplied = do
  ordered <- maybe undecidable Right (orderedAtlasMapView family)
  reservations <- decisionEither
    (ArgumentMap.argumentReservations
      selectFederationMember supplied [family])
  let positional =
        ArgumentMap.positionalArgumentSource reservations supplied
  rows <- argumentRows supplied
  let orderType = ordinalOrderedValuesOrderType ordered
      traversal = foliageMap orderType
      sourceFrontier = 1 + maximum (0 : map (fromIntegral . length) rows)
      ranks = case naturalAtOrdinal orderType of
        Just count -> naturalPositions count
        Nothing -> naturalPositions sourceFrontier
      exhausted = case naturalAtOrdinal orderType of
        Just _ -> refuted
        Nothing -> undecidable
  suppliedOrder <- argumentOrder supplied
  search reservations positional suppliedOrder
    (ordinalLTE orderType omega) Nothing ordered traversal ranks exhausted
  where
    search _ _ _ _ _ _ _ [] exhausted = exhausted
    search reservations positional suppliedOrder monotonicFamily previousOrder
        ordered traversal
        (rank : remaining) exhausted =
      case foliageMapPositionAt traversal rank
          >>= ordinalOrderedValueAt ordered of
        Nothing -> undecidable
        Just candidate -> do
          candidateOrder <- argumentOrder candidate
          let monotonic = monotonicFamily && maybe True
                (candidateOrder `ordinalGT`) previousOrder
              conclusive = monotonic
                && candidateOrder `ordinalGTE` suppliedOrder
          case decisionEither
              (ArgumentMap.argumentReservations
                selectFederationMember supplied [candidate]) of
            Left _ -> undecidable
            Right candidateReservations ->
              let admitsReserved = and
                    (zipWith
                      (\reserved admitted -> not reserved || admitted)
                      reservations
                      candidateReservations)
              in if not admitsReserved
                then if conclusive then missing else later candidateOrder
                else case complete
                    (argumentSchemaFromValue candidate) positional of
                  Right selected -> Right selected
                  Left failure ->
                    if conclusive then Left failure else later candidateOrder
      where
        later candidateOrder = search reservations positional suppliedOrder
          monotonicFamily (Just candidateOrder) ordered traversal
          remaining exhausted

    naturalPositions 0 = []
    naturalPositions count = [0 .. count - 1]

    decisionEither decision =
      case decision of
        DecisionProved value -> Right value
        DecisionRefuted -> refuted
        DecisionUndecidable -> undecidable

    argumentOrder value = do
      valueRows <- argumentRows value
      case nubBy (==)
          [finiteOrdinal (fromIntegral (length row)) | row <- valueRows] of
        [orderType] -> Right orderType
        _ -> undecidable

    refuted = Left
      (AtlasMapFederationOperationRefuted
        AtlasMapFederationSpecificationHasNoMatchingMember)
    undecidable = Left
      (AtlasMapFederationOperationUndecidable
        (NoAtlasMapFederationDecisionProcedure
          AtlasMapFederationSpecification))
    missing = Left (OverloadError OverloadMissingRequiredSlot)

overloadArgumentSchemaComplete
  :: ArgumentSchema
  -> InterpretedValue
  -> Either InterpretingError (InterpretedValue, [(String, InterpretedValue)])
overloadArgumentSchemaComplete = overloadArgumentSchemaCompleteWithGenerics
  (\_ annotation _ _ -> Right annotation)

overloadArgumentSchemaCompleteWithGenerics
  :: ( GenericArgumentBinder
       -> InterpretedValue
       -> [InterpretedValue]
       -> [(GenericArgumentBinder, InterpretedValue)]
       -> Either InterpretingError InterpretedValue)
  -> ArgumentSchema
  -> InterpretedValue
  -> Either InterpretingError (InterpretedValue, [(String, InterpretedValue)])
overloadArgumentSchemaCompleteWithGenerics infer schema supplied =
  overloadArgumentSchemaCompleteWithTrustedGenerics
    infer [] schema supplied

-- | Complete a call while accepting selected generic witnesses directly from
-- their declared indexing family. Projection uses this path after obtaining
-- a witness from the bound itself; explicit caller arguments continue through
-- ordinary slot specification.
overloadArgumentSchemaCompleteWithTrustedGenerics
  :: ( GenericArgumentBinder
       -> InterpretedValue
       -> [InterpretedValue]
       -> [(GenericArgumentBinder, InterpretedValue)]
       -> Either InterpretingError InterpretedValue)
  -> [(GenericBinderId, InterpretedValue)]
  -> ArgumentSchema
  -> InterpretedValue
  -> Either InterpretingError (InterpretedValue, [(String, InterpretedValue)])
overloadArgumentSchemaCompleteWithTrustedGenerics
    infer trusted schema supplied =
  let normalized = normalizeArgumentSchema schema
  in case projectedGenericInferenceParts normalized of
    Just (genericSlots, evidenceBinders, projection) -> do
      projected <- argumentSchemaBodyValues projection supplied
      projectedMembers <- canonicalArgumentMembers projected
      let evidence =
            [ (binderId, uniqueValues (map eraseIdentifier projectedMembers))
            | binderId <- evidenceBinders
            ]
          provisional =
            [ (slotName slot, trustedValue slot)
            | slot <- genericSlots
            ]
      completed <- completeGenericSlots trustedInfer
        evidence genericSlots provisional
      let prepared = makeAtlasMapPreservingSingleton 2
            (map namedSlot completed <> projectedMembers)
      pure
        ( prepared
        , [(name, value) | (Just name, value) <- completed]
        )
    Nothing -> case schema of
      ProjectedArgumentSchema _ -> do
        prepared <- argumentSchemaBodyValues schema supplied
        pure (prepared, [])
      _ -> do
        replacements <- resolveReplacements normalized supplied
        let slots = templateSlots normalized
        provisional <- traverse (completeTrustedSlot replacements) slots
        completed <- completeGenericSlots trustedInfer
          (genericEvidence slots provisional) slots provisional
        let prepared = bodyAggregate normalized (map namedSlot completed)
        pure (prepared, [(name, value) | (Just name, value) <- completed])
  where
    trustedValue slot =
      case slotGenericBinder slot of
        Just binder -> maybe (slotAnnotation slot) id
          (lookup (genericArgumentBinderId binder) trusted)
        Nothing -> slotAnnotation slot
    completeTrustedSlot replacements slot =
      case slotGenericBinder slot >>= \binder ->
          lookup (genericArgumentBinderId binder) trusted of
        Just value -> Right (slotName slot, value)
        Nothing -> completeSlot replacements slot
    trustedInfer binder annotation evidence prior =
      case lookup (genericArgumentBinderId binder) trusted of
        Just value -> Right value
        Nothing -> infer binder annotation evidence prior

-- A private generic prefix consumes no caller slots. When its only ordinary
-- suffix is a projected family such as @Args _T@, delegate the entire supplied
-- value to that family, then prepend the inferred witnesses to its selected
-- body page. Public/explicit prefix slots still use ordinary routing.
projectedGenericInferenceParts
  :: ArgumentSchema
  -> Maybe ([Slot], [GenericBinderId], ArgumentSchema)
projectedGenericInferenceParts schema = do
  (genericSlots, projections) <- collect [] schema
  case projections of
    [(binderIds, projection)]
      | not (null genericSlots)
      , all slotIsInferred genericSlots ->
          Just (genericSlots, binderIds, projection)
    _ -> Nothing
  where
    collect inherited current =
      case current of
        GenericArgumentSlotSchema {} ->
          Just (templateSlots current, [])
        GenericEvidenceArgumentSchema binderIds child ->
          collect (nub (inherited <> binderIds)) child
        ProjectedArgumentSchema {} ->
          Just ([], [(inherited, current)])
        OrderedArgumentSchema _ children -> collectChildren inherited children
        UnorderedArgumentSchema children -> collectChildren inherited children
        ConcatenatedArgumentSchema left right ->
          collectChildren inherited [left, right]
        EmptyArgumentSchema -> Just ([], [])
        ArgumentSlotSchema {} -> Nothing
    collectChildren inherited children = do
      parts <- traverse (collect inherited) children
      pure
        ( concatMap fst parts
        , concatMap snd parts
        )

canonicalArgumentMembers
  :: InterpretedValue
  -> Either InterpretingError [InterpretedValue]
canonicalArgumentMembers value =
  case interpretedForm value of
    ArgumentMapForm members _ -> Right members
    _ -> do
      rows <- argumentRows value
      case rows of
        [members] -> Right members
        _ -> Left (OverloadError OverloadNoMatch)

eraseIdentifier :: InterpretedValue -> InterpretedValue
eraseIdentifier value =
  case suppliedValue value of
    (Just _, underlying) -> eraseIdentifier underlying
    (Nothing, underlying) -> underlying

uniqueValues :: [InterpretedValue] -> [InterpretedValue]
uniqueValues = nubBy sameValue
  where
    sameValue left right =
      interpretedSemanticResult left == interpretedSemanticResult right

completeGenericSlots
  :: ( GenericArgumentBinder
       -> InterpretedValue
       -> [InterpretedValue]
       -> [(GenericArgumentBinder, InterpretedValue)]
       -> Either InterpretingError InterpretedValue)
  -> [(GenericBinderId, [InterpretedValue])]
  -> [Slot]
  -> [(Maybe String, InterpretedValue)]
  -> Either InterpretingError [(Maybe String, InterpretedValue)]
completeGenericSlots infer evidence = go []
  where
    go _ [] [] = Right []
    go generics (slot : remainingSlots) (completed : remainingCompleted) =
      case slotGenericBinder slot of
        Just binder | genericArgumentInferred binder -> do
          witness <- infer binder (slotAnnotation slot)
            (maybe [] id (lookup (genericArgumentBinderId binder) evidence))
            (reverse generics)
          remaining <- go ((binder, witness) : generics)
            remainingSlots remainingCompleted
          pure ((Just (genericArgumentName binder), witness) : remaining)
        Just binder -> do
          remaining <- go ((binder, snd completed) : generics)
            remainingSlots remainingCompleted
          pure (completed : remaining)
        Nothing -> (completed :) <$> go generics remainingSlots remainingCompleted
    go _ _ _ = Left (OverloadError OverloadNoMatch)

genericEvidence
  :: [Slot]
  -> [(Maybe String, InterpretedValue)]
  -> [(GenericBinderId, [InterpretedValue])]
genericEvidence slots completed = foldr add [] (zip slots completed)
  where
    add (slot, (_, value)) evidence =
      foldr (insertEvidence (eraseIdentifier value)) evidence
        (slotEvidenceBinders slot)
    insertEvidence value binderId evidence =
      case lookup binderId evidence of
        Nothing -> (binderId, [value]) : evidence
        Just values
          | any (sameValue value) values -> evidence
          | otherwise ->
              (binderId, value : values)
                : filter ((/= binderId) . fst) evidence
    sameValue left right =
      interpretedSemanticResult left == interpretedSemanticResult right

argumentSchemaHasInferredGenerics :: ArgumentSchema -> Bool
argumentSchemaHasInferredGenerics = any slotIsInferred . templateSlots

argumentSchemaInferredGenericNames :: ArgumentSchema -> [String]
argumentSchemaInferredGenericNames schema =
  [ genericArgumentName binder
  | slot <- templateSlots schema
  , Just binder <- [slotGenericBinder slot]
  , genericArgumentInferred binder
  ]

-- Function specifications validate the hidden prefix against its declared
-- domain. Keep the joined witness for the body and lexical binding, while the
-- redundant structural validation uses one already-checked evidence value.
-- The concatenated projected suffix remains expanded and concrete.
argumentSchemaValidationArgument
  :: ArgumentSchema
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
argumentSchemaValidationArgument schema prepared =
  case projectedGenericInferenceParts (normalizeArgumentSchema schema) of
    Just (genericSlots, _, ProjectedArgumentSchema _) -> do
      members <- canonicalArgumentMembers prepared
      let suffix = drop (length genericSlots) members
          representative = case suffix of
            first : _ -> eraseIdentifier first
            [] -> makeAtlasMap 0 []
          prefix =
            [ namedSlot (slotName slot, representative)
            | slot <- genericSlots
            ]
      pure (makeAtlasMapPreservingSingleton 2 (prefix <> suffix))
    _ -> Right prepared

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
    GenericArgumentSlotSchema index binder annotation ->
      buildSlot (Just (genericArgumentName binder))
        (genericArgumentOptionalName binder) True annotation
        (replacementAt index replacements
          <|> if genericArgumentInferred binder then Just annotation else Nothing)
    GenericEvidenceArgumentSchema _ child -> buildTemplate replacements child
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
