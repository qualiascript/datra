-- | Conservative inference for the executable expression fragment. Unknown
-- constraints are reported, never accepted by trying example arguments.
module FunctionInference (freeIdentifiers, inferParameters, inferBody) where
import Data.List (nub)
import DatraLanguage.AST
import DatraTypes

freeIdentifiers :: Expression -> [String]
freeIdentifiers = nub . free []
  where
    free bound expression = case expression of
      IdentifierReference (IdentifierString name) -> [name | name `notElem` bound]
      FunctionBody bindings result -> block bound bindings result
      Begin bindings result -> block bound bindings result
      Program bindings result -> block bound bindings result
      _ -> concatMap (free bound) (children expression)
    block bound bindings result = entries initial bindings
      where
        declarations = map (blockDeclaration False) bindings
        initial = [name | Just (name, True, _) <- declarations] <> bound
        entries visible [] = free visible result
        entries visible (entry : remaining) =
          free visible entry <> entries (afterEntry visible entry) remaining
        afterEntry visible entry =
          case blockDeclaration False entry of
            Just (name, False, _) -> name : visible
            _ -> visible

blockDeclaration :: Bool -> Expression -> Maybe (String, Bool, Expression)
blockDeclaration strict expression =
  case expression of
    Let binding -> blockDeclaration True binding
    IdentifierOperation (IdentifierString name) annotation given ->
      Just
        ( name
        , strict
        , maybe annotation
            (\value ->
              if value == annotation
                then value
                else MapSpecification value annotation)
            given
        )
    EitherType named@(IdentifierOperation _ annotation _) missing
      | annotation == missing -> blockDeclaration strict named
    _ -> Nothing

data InferenceBinding = InferenceBinding
  { inferenceBindingName :: String
  , inferenceBindingExpression :: Expression
  , inferenceBindingMembers :: [String]
  , inferenceBindingScope :: [InferenceBinding]
  }

inferParameters :: [String] -> Expression -> Either InterpretingError [(String, Expression)]
inferParameters names body = traverse infer names
  where
    infer name = case nub (constraints name body) of
      [] -> Left (FunctionEvaluationFailed
        (UnconstrainedInferredParameter name))
      [target] -> Right (name, target)
      _ -> Left (FunctionEvaluationFailed
        (IncompatibleInferredParameterConstraints name))
    constraints name expression = case expression of
      Addition a b -> numerical a b
      Subtraction a b -> numerical a b
      Multiplication a b -> numerical a b
      Exponentiation a b -> numerical a b
      Minus a -> require IntegerType a
      BooleanAnd a b -> require BooleanType a <> require BooleanType b
      BooleanOr a b -> require BooleanType a <> require BooleanType b
      BooleanNot a -> require BooleanType a
      Assert _ condition -> require BooleanType condition
      Conditional condition yes no -> require BooleanType condition <> recur yes <> recur no
      _ -> concatMap recur (children expression)
      where
        recur = constraints name
        numerical a b = require IntegerType a <> require IntegerType b
        require target value = [target | name `elem` freeIdentifiers value] <> recur value

inferBody :: (Expression -> Either InterpretingError InterpretedValue)
  -> [(String, InterpretedValue)] -> [Expression] -> Expression
  -> Either InterpretingError InterpretedValue
inferBody evaluate parameters bindings result = inferBlock [] bindings result
  where
    inferBlock enclosing entries resultValue =
      infer imported memberNames resultValue
      where
        definitions =
          [ definition
          | entry <- entries
          , Just definition <- [blockDeclaration False entry]
          ]
        memberNames = [name | (name, _, _) <- definitions]
        initial = recursiveLets <> enclosing
        recursiveLets =
          [ InferenceBinding name expressionValue memberNames
              (scopeBefore position)
          | (position, (name, strict, expressionValue)) <- zip [0..] definitions
          , strict
          ]
        scopeBefore position =
          foldl addOrdinary initial (take position definitions)
        addOrdinary scope (name, strict, expressionValue)
          | strict = scope
          | otherwise =
              InferenceBinding name expressionValue memberNames scope : scope
        imported = foldl addOrdinary initial definitions

    infer scope members expression = case expression of
      IdentifierReference (IdentifierString name)
        | Just target <- lookup name parameters -> Right target
        | Just binding <- lookupInferenceBinding name scope ->
            infer
              (inferenceBindingScope binding)
              (inferenceBindingMembers binding)
              (inferenceBindingExpression binding)
        | otherwise -> evaluate expression
      Addition a b -> numeric addValues False a b
      Multiplication a b -> numeric multiplyValues False a b
      Subtraction a b -> numeric subtractValues True a b
      Exponentiation a b -> numeric exponentiateValues False a b
      Minus a -> do
        operand <- recur a
        check operand =<< integerTypeValue
        if interpretedValueHasTotalMap operand then minusValue operand else integerTypeValue
      BooleanAnd a b -> logical [a,b]
      BooleanOr a b -> logical [a,b]
      BooleanNot a -> logical [a]
      Conditional condition yes no -> do
        flag <- recur condition
        check flag =<< booleanTypeValue
        left <- recur yes
        right <- recur no
        joinTypes left right
      Equality a b -> recur a >> recur b >> booleanTypeValue
      Inequality a b -> recur a >> recur b >> booleanTypeValue
      Subfederation a b -> recur a >> recur b >> booleanTypeValue
      Assert _ condition -> do
        value <- recur condition
        check value =<< booleanTypeValue
        pure (makeAtlasMap 0 [])
      MapSpecification source target -> do
        actual <- recur source
        expected <- recur target
        check actual expected
        pure expected
      This -> do
        values <- traverse
          (\name -> simpleIdentifierTypeValue name
            <$> infer scope members (IdentifierReference (IdentifierString name)))
          members
        pure (makeAtlasMap 2 values)
      NamedAccess operand (IdentifierString name) -> recur operand >>= (`namedAccessValue` name)
      MapAccess operand index -> do
        value <- recur operand
        position <- recur index
        accessValues value position
      FunctionApplication function argument -> do
        callable <- recur function
        case functionSignature callable of
          Nothing -> Left (FunctionEvaluationFailed
            InferredApplicationRequiresFunction)
          Just (domain,codomain) -> do
            actual <- recur argument
            check actual domain
            pure codomain
      IdentifierOperation (IdentifierString name) annotation given -> do
        target <- recur annotation
        requireCanonicalTypeAnnotation target
        case given of
          Nothing -> pure (simpleIdentifierTypeValue name target)
          Just value -> do actual <- recur value; check actual target; pure (simpleIdentifierTypeValue name target)
      AtlasMap values -> makeAtlasMap 2 <$> traverse recur values
      MapSequence values -> makeAtlasMap 2 <$> traverse recur values
      ArgumentMap values -> traverse recur values >>= makeArgumentMap
      MapConcatenation a b -> do left <- recur a; right <- recur b; concatenateValues left right
      Overload a b -> do left <- recur a; right <- recur b; overloadValues left right
      SafeOverload a b -> do left <- recur a; right <- recur b; safeOverloadValues left right
      EitherType a b -> do left <- recur a; right <- recur b; joinTypes left right
      Begin entries value -> inferBlock scope entries value
      Program entries value -> inferBlock scope entries value
      -- Literals, primitive types and closed expressions have exact known types.
      _ | all (`notElem` map fst parameters) (freeIdentifiers expression) -> evaluate expression
        | otherwise -> Left (FunctionEvaluationFailed
            UnsupportedInferredExpression)
      where
        recur = infer scope members
        numeric operation signed a b = do
          left <- recur a
          right <- recur b
          ints <- integerTypeValue
          check left ints
          check right ints
          if interpretedValueHasTotalMap left && interpretedValueHasTotalMap right
            then operation left right
            else do
              nats <- naturalTypeValue
              leftNat <- isSubtype left nats
              rightNat <- isSubtype right nats
              pure (if not signed && leftNat && rightNat then nats else ints)
        logical operands = do
          bools <- booleanTypeValue
          traverse recur operands >>= mapM_ (`check` bools)
          pure bools

lookupInferenceBinding :: String -> [InferenceBinding] -> Maybe InferenceBinding
lookupInferenceBinding name = go
  where
    go [] = Nothing
    go (binding : remaining)
      | inferenceBindingName binding == name = Just binding
      | otherwise = go remaining

check :: InterpretedValue -> InterpretedValue -> Either InterpretingError ()
check actual expected = do
  accepted <- isSubtype actual expected
  if accepted then Right () else Left (FunctionEvaluationFailed
    (InferredTypeOutsideRequirement
      (show (interpretedCanonicalResult actual))
      (show (interpretedCanonicalResult expected))))

isSubtype :: InterpretedValue -> InterpretedValue -> Either InterpretingError Bool
isSubtype source target = subfederationValues source target >>= booleanCondition

joinTypes :: InterpretedValue -> InterpretedValue -> Either InterpretingError InterpretedValue
joinTypes a b = do
  included <- isSubtype a b
  if included then Right b else do
    reverseIncluded <- isSubtype b a
    if reverseIncluded then Right a else eitherValue a b

children :: Expression -> [Expression]
children = expressionChildren
