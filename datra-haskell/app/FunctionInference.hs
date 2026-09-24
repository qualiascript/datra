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
    block bound bindings result = concatMap (free (declaredNames bindings <> bound)) (result : bindings)

declaredNames :: [Expression] -> [String]
declaredNames = concatMap names
  where
    names (IdentifierOperation (IdentifierString name) _ _) = [name]
    names (Let binding) = names binding
    names (AtlasMap members) = declaredNames members
    names (MapConcatenation a b) = names a <> names b
    names _ = []

inferParameters :: [String] -> Expression -> Either InterpretingError [(String, Expression)]
inferParameters names body = traverse infer names
  where
    infer name = case nub (constraints name body) of
      [] -> Left (FunctionError ("cannot infer unconstrained parameter " <> name <> "; provide an input type"))
      [target] -> Right (name, target)
      _ -> Left (FunctionError ("incompatible constraints for parameter " <> name))
    constraints name expression = case expression of
      Addition a b -> numerical a b
      Subtraction a b -> numerical a b
      Multiplication a b -> numerical a b
      Exponentiation a b -> numerical a b
      Minus a -> require IntegerType a
      BooleanAnd a b -> require BooleanType a <> require BooleanType b
      BooleanOr a b -> require BooleanType a <> require BooleanType b
      BooleanNot a -> require BooleanType a
      Conditional condition yes no -> require BooleanType condition <> recur yes <> recur no
      _ -> concatMap recur (children expression)
      where
        recur = constraints name
        numerical a b = require IntegerType a <> require IntegerType b
        require target value = [target | name `elem` freeIdentifiers value] <> recur value

inferBody :: (Expression -> Either InterpretingError InterpretedValue)
  -> [(String, InterpretedValue)] -> [Expression] -> Expression
  -> Either InterpretingError InterpretedValue
inferBody evaluate parameters bindings result = infer [] result
  where
    definitions = concatMap definition bindings
    definition (Let binding) = definition binding
    definition (IdentifierOperation (IdentifierString name) annotation given) =
      [(name, maybe annotation (\value -> if value == annotation then value else MapSpecification value annotation) given)]
    definition _ = []
    infer resolving expression = case expression of
      IdentifierReference (IdentifierString name)
        | name `elem` resolving -> Left (CyclicIdentifierReference (reverse (name:resolving)))
        | Just target <- lookup name parameters -> Right target
        | Just value <- lookup name definitions -> infer (name:resolving) value
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
      Subfederation a b -> recur a >> recur b >> booleanTypeValue
      MapSpecification source target -> do
        actual <- recur source
        expected <- evaluate target
        check actual expected
        pure expected
      This -> do
        values <- traverse (\(name, _) -> simpleIdentifierTypeValue name <$> infer resolving (IdentifierReference (IdentifierString name)))
          (filter (\(name,_) -> case name of '_':_ -> False; _ -> True) definitions)
        pure (makeAtlasMap 2 values)
      NamedAccess operand (IdentifierString name) -> recur operand >>= (`namedAccessValue` name)
      FunctionApplication function argument -> do
        callable <- recur function
        case functionSignature callable of
          Nothing -> Left (FunctionError "application requires a function")
          Just (domain,codomain) -> do
            actual <- recur argument
            check actual domain
            pure codomain
      IdentifierOperation (IdentifierString name) annotation given -> do
        target <- recur annotation
        case given of
          Nothing -> pure (simpleIdentifierTypeValue name target)
          Just value -> do actual <- recur value; check actual target; pure (simpleIdentifierTypeValue name target)
      AtlasMap members -> makeAtlasMap 2 <$> traverse recur members
      MapSequence members -> makeAtlasMap 2 <$> traverse recur members
      ArgumentMap members -> traverse recur members >>= makeArgumentMap
      MapConcatenation a b -> do left <- recur a; right <- recur b; concatenateValues left right
      EitherType a b -> do left <- recur a; right <- recur b; joinTypes left right
      Begin entries value -> inferBody evaluate parameters (bindings <> entries) value
      Program entries value -> inferBody evaluate parameters (bindings <> entries) value
      -- Literals, primitive types and closed expressions have exact known types.
      _ | all (`notElem` map fst parameters) (freeIdentifiers expression) -> evaluate expression
        | otherwise -> Left (FunctionError "cannot infer this expression; add a supported explicit specification")
      where
        recur = infer resolving
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

check :: InterpretedValue -> InterpretedValue -> Either InterpretingError ()
check actual expected = do
  accepted <- isSubtype actual expected
  if accepted then Right () else Left (FunctionError
    ("inferred type is outside the required type: " <> show (interpretedCanonicalResult actual)
      <> " of " <> show (interpretedCanonicalResult expected)))

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
