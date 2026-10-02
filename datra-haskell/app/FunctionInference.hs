-- | Conservative inference for the executable expression fragment. Unknown
-- constraints are reported, never accepted by trying example arguments.
module FunctionInference (freeIdentifiers, inferParameters, inferBody) where

import BlockScope
import Control.Monad (foldM)
import Data.List (nub)
import DatraLanguage.AST
import DatraTypes

data DependentBindingTag = ForBindingTag | WithBindingTag
  deriving (Eq)

freeIdentifiers :: Expression -> [String]
freeIdentifiers = nub . free []
  where
    free bound expression = case expression of
      IdentifierReference (IdentifierString name) -> [name | name `notElem` bound]
      FunctionType domain codomain ->
        dependentEntries bound ForBindingTag (domainEntries domain)
          <> free (dependentNames ForBindingTag (domainEntries domain) <> bound) codomain
      ArgumentMap entries -> dependentEntries bound ForBindingTag entries
      AtlasMap entries -> dependentEntries bound WithBindingTag entries
      MapSequence entries -> dependentEntries bound WithBindingTag entries
      FunctionBody bindings result -> block bound bindings result
      Begin bindings result -> block bound bindings result
      Program bindings result -> block bound bindings result
      MaybeThen optional branch ->
        free bound optional <> free ("it" : bound) branch
      _ -> concatMap (free bound) (children expression)
    dependentEntries bound tag = entries bound
      where
        entries _ [] = []
        entries visible (entry : remaining) =
          free visible (binderBound entry)
            <> entries (binderScope visible entry) remaining
        binderBound (ForBinding _ _ value) | tag == ForBindingTag = value
        binderBound (WithBinding _ _ value) | tag == WithBindingTag = value
        binderBound value = value
        binderScope visible (ForBinding (IdentifierString name) _ _)
          | tag == ForBindingTag = name : visible
        binderScope visible (WithBinding (IdentifierString name) _ _)
          | tag == WithBindingTag = name : visible
        binderScope visible _ = visible
    dependentNames tag = foldl collect []
      where
        collect names (ForBinding (IdentifierString name) _ _)
          | tag == ForBindingTag = names <> [name]
        collect names (WithBinding (IdentifierString name) _ _)
          | tag == WithBindingTag = names <> [name]
        collect names _ = names
    domainEntries (ArgumentMap entries) = entries
    domainEntries (AtlasMap entries) = entries
    domainEntries (MapSequence entries) = entries
    domainEntries value = [value]
    block bound bindings result = entries initial bindings
      where
        declarations = map blockDeclaration bindings
        initial = [declarationName value | Just value <- declarations, declarationIsLet value] <> bound
        entries visible [] = free visible result
        entries visible (entry : remaining) =
          free visible entry <> entries (afterEntry visible entry) remaining
        afterEntry visible entry =
          case blockDeclaration entry of
            Just value | not (declarationIsLet value) -> declarationName value : visible
            _ -> visible

data InferenceBinding =
  InferenceBinding String Expression [String] [InferenceBinding]
  | InferenceValueBinding String InterpretedValue

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
      Plus a -> require IntegerType a
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
  -> [(String, InterpretedValue)] -> Maybe InterpretedValue
  -> [String] -> Maybe InterpretedValue
  -> [Expression] -> Expression
  -> Either InterpretingError InterpretedValue
inferBody evaluate parameters self namedSelf declaredOutput bindings result =
  inferBlock declaredOutput [] bindings result
  where
    inferBlock resultType enclosing entries resultValue =
      inferExpected imported memberNames resultType resultValue
      where
        definitions =
          [ definition
          | entry <- entries
          , Just definition <- [blockDeclaration entry]
          ]
        memberNames = map declarationName definitions
        imported = buildScopeBindings
          (\captured value -> InferenceBinding (declarationName value)
            (declarationValue value) memberNames captured) enclosing definitions

    inferMaybePresent scope members optional = do
      optionalType <- infer scope members optional
      maybe
        (Left (FunctionEvaluationFailed NoApplicableFunctionAlternative))
        Right
        (optionalPresentType optionalType)

    inferExpected scope members expected expression =
      case (expected, expression) of
        (Just target, Conditional condition yes no) -> do
          flag <- infer scope members condition
          check flag =<< booleanTypeValue
          _ <- inferExpected scope members (Just target) yes
          _ <- inferExpected scope members (Just target) no
          pure target
        (Just target, MaybeThen optional branch) -> do
          present <- inferMaybePresent scope members optional
          _ <- inferExpected
            (InferenceValueBinding "it" present : scope)
            members
            (Just target)
            branch
          pure target
        (Just target, Begin entries value) ->
          inferBlock (Just target) scope entries value
        (Just target, Program entries value) ->
          inferBlock (Just target) scope entries value
        (Just target, value) -> do
          actual <- infer scope members value
          case check actual target of
            Right () -> pure target
            Left _ -> case contextuallySpecifyValues actual target of
              Right _ -> pure target
              Left _ -> Left (FunctionEvaluationFailed
                FunctionBodyOutsideDeclaredResult)
        (Nothing, value) -> infer scope members value

    infer scope members expression = case expression of
      IdentifierReference (IdentifierString name)
        | name == "this" -> maybe
            (declarationMap members
              (recur . IdentifierReference . IdentifierString))
            Right
            self
        | Just binding <- lookupInferenceBinding name scope ->
            case binding of
              InferenceBinding _ value bindingMembers bindingScope ->
                infer bindingScope bindingMembers value
              InferenceValueBinding _ target -> Right target
        | Just target <- lookup name parameters -> Right target
        | otherwise -> evaluate expression
      Addition a b -> numeric "+" addValues False a b
      Multiplication a b -> numeric "*" multiplyValues False a b
      Subtraction a b -> numeric "-" subtractValues True a b
      Exponentiation a b -> power a b
      Plus a -> do
        operand <- recur a
        limits <- integerLimitType
        check operand limits
        if interpretedValueHasTotalMap operand
          then plusValue operand
          else pure operand
      Minus a -> do
        operand <- recur a
        limits <- integerLimitType
        check operand limits
        if interpretedValueHasTotalMap operand
          then minusValue operand
          else do
            ints <- integerType
            finite <- isSubtype operand ints
            pure (if finite then ints else operand)
      BooleanAnd a b -> logical [a,b]
      BooleanOr a b -> logical [a,b]
      BooleanNot a -> logical [a]
      Coalization operand -> coalizeValue <$> recur operand
      StripIdentifiers operand -> recur operand >>= stripIdentifiersType
      Conditional condition yes no -> do
        flag <- recur condition
        check flag =<< booleanTypeValue
        left <- recur yes
        right <- recur no
        joinTypes left right
      MaybeThen optional branch -> do
        present <- inferMaybePresent scope members optional
        branchType <- infer
          (InferenceValueBinding "it" present : scope)
          members
          branch
        optionalValue branchType
      ListUncons operand -> do
        listType <- recur operand
        indexedType <- accessValues listType (naturalValue 0)
        let elementType = maybe indexedType id (optionalUnderlying indexedType)
        optionalValue (makeAtlasMap 2 [elementType, listType])
      Equality a b -> recur a >> recur b >> booleanTypeValue
      Inequality a b -> recur a >> recur b >> booleanTypeValue
      LessThan a b -> comparison a b
      LessThanOrEqual a b -> comparison a b
      GreaterThan a b -> comparison a b
      GreaterThanOrEqual a b -> comparison a b
      Subfederation a b -> recur a >> recur b >> booleanTypeValue
      Assert _ condition -> do
        value <- recur condition
        check value =<< booleanTypeValue
        pure (makeAtlasMap 0 [])
      -- A function implementation introduces its own parameter scope.  When
      -- it has an explicit signature, that signature is the complete type of
      -- the local value; attempting to infer the nested body here would make
      -- its @it@ look like the enclosing function's argument.
      MapSpecification FunctionBody {} target@FunctionType {} -> recur target
      MapSpecification source target -> do
        actual <- recur source
        expected <- case evaluate target of
          Right value -> Right value
          Left _ -> recur target
        check actual expected
        pure expected
      NamedAccess operand (IdentifierString name) -> recur operand >>= (`namedAccessValue` name)
      MapAccess (IdentifierReference (IdentifierString "this")) index -> do
        position <- recur index
        projectDeclaration members (recur . IdentifierReference . IdentifierString) position
      MapAccess operand index -> do
        value <- recur operand
        position <- recur index
        accessValues value position
      FunctionApplication function argument -> do
        callable <- recur function
        actual <- recur argument
        let alternatives = functionAlternatives callable
            recursiveCall = case (function, self) of
              (IdentifierReference (IdentifierString "this"), Just _) -> True
              (IdentifierReference (IdentifierString name), _) ->
                name `elem` namedSelf
              _ -> False
            accepted
              | recursiveCall = alternatives
              | otherwise =
                  [ alternative
                  | alternative <- alternatives
                  , Right () <-
                      [checkFunctionArgument argument actual
                        (functionDomain alternative)]
                  ]
        case accepted of
          [] -> case alternatives of
            [] -> Left (FunctionEvaluationFailed
              InferredApplicationRequiresFunction)
            [alternative] -> do
              checkFunctionArgument argument actual
                (functionDomain alternative)
              pure (functionCodomain alternative)
            _ -> Left (FunctionEvaluationFailed
              NoApplicableFunctionAlternative)
          alternative : remaining ->
            foldM joinTypes (functionCodomain alternative)
              (map functionCodomain remaining)
      IdentifierOperation (IdentifierString name) annotation given -> do
        target <- recur annotation
        requireCanonicalTypeAnnotation target
        case given of
          Nothing -> pure (simpleIdentifierTypeValue name target)
          Just value -> do actual <- recur value; check actual target; pure (simpleIdentifierTypeValue name target)
      AtlasMap values -> makeAtlasMap 2 <$> traverse recur values
      MapSequence values -> makeAtlasMap 2 <$> traverse recur values
      ArgumentMap values -> traverse recur values >>= makeArgumentMap
      MapConcatenation left right -> do
        leftValue <- recur left
        rightValue <- recur right
        concatenateValues leftValue rightValue
      Overload a b -> do left <- recur a; right <- recur b; overloadValues left right
      SafeOverload a b -> do left <- recur a; right <- recur b; safeOverloadValues left right
      EitherType a b -> do left <- recur a; right <- recur b; joinTypes left right
      OptionalType operand ->
        case optionalIdentifierExpression expression of
          Just (present, missing) -> do
            left <- recur present
            right <- recur missing
            joinTypes left right
          Nothing -> recur
            (FunctionApplication
              (IdentifierReference (IdentifierString "Maybe"))
              operand)
      StringTemplate parts -> do
        -- Interpolation affects whether evaluating the template can succeed,
        -- but not its result type. Still infer every embedded expression so
        -- unknown names and invalid enclosing parameter uses are diagnosed.
        mapM_ inferTemplatePart parts
        evaluate (IdentifierReference (IdentifierString "Str"))
      Begin entries value -> inferBlock Nothing scope entries value
      Program entries value -> inferBlock Nothing scope entries value
      -- Literals, primitive types and closed expressions have exact known types.
      _ | all (`notElem` map fst parameters) (freeIdentifiers expression) -> evaluate expression
        | otherwise -> Left (FunctionEvaluationFailed
            UnsupportedInferredExpression)
      where
        recur = infer scope members
        inferTemplatePart (StringTemplateLiteral _) = Right ()
        inferTemplatePart (StringTemplateInterpolation value) = () <$ recur value
        inferTemplatePart (StringTemplateWeakInterpolation value) = () <$ recur value
        numeric operator operation signed a b = do
          left <- recur a
          right <- recur b
          limits <- integerLimitType
          check left limits
          check right limits
          let leftConcrete = concreteIntegerLimit left
              rightConcrete = concreteIntegerLimit right
          if leftConcrete && rightConcrete
            then operation left right
            else do
              rejectIndeterminate operator left right
              ints <- integerType
              leftFinite <- isSubtype left ints
              rightFinite <- isSubtype right ints
              nats <- naturalType
              leftNat <- isSubtype left nats
              rightNat <- isSubtype right nats
              if leftFinite && rightFinite
                then pure (if not signed && leftNat && rightNat then nats else ints)
              else if not leftConcrete && rightConcrete
                  then pure left
                  else if leftConcrete && not rightConcrete
                    then pure right
                    else pure limits
        power base exponentValue = do
          baseType <- recur base
          exponentType <- recur exponentValue
          limits <- integerLimitType
          nats <- naturalType
          check baseType limits
          check exponentType nats
          if concreteIntegerLimit baseType
              && concreteIntegerLimit exponentType
            then exponentiateValues baseType exponentType
            else do
              ints <- integerType
              natural <- isSubtype baseType nats
              finite <- isSubtype baseType ints
              pure
                (if natural then nats
                  else if finite then ints
                  else baseType)
        comparison a b = do
          left <- recur a
          right <- recur b
          limits <- integerLimitType
          check left limits
          check right limits
          booleanTypeValue
        integerLimitType = standardType "IntLimit"
        integerType = standardType "Int"
        naturalType = standardType "Nat"
        standardType name = evaluate
          (IdentifierReference (IdentifierString name))
        concreteIntegerLimit value = case integerLimitProjection value of
          Just _ -> True
          Nothing -> False
        rejectIndeterminate operator left right = do
          positive <- asciiStringValue "PosInf"
          negative <- asciiStringValue "NegInf"
          let contains member target = isSubtype member target
          leftPositive <- contains positive left
          leftNegative <- contains negative left
          rightPositive <- contains positive right
          rightNegative <- contains negative right
          zero <- contains (naturalValue 0) left
          rightZero <- contains (naturalValue 0) right
          let unsafe = case operator of
                "+" ->
                  (leftPositive && rightNegative)
                    || (leftNegative && rightPositive)
                "-" ->
                  (leftPositive && rightPositive)
                    || (leftNegative && rightNegative)
                "*" ->
                  (zero && (rightPositive || rightNegative))
                    || (rightZero && (leftPositive || leftNegative))
                _ -> False
          if unsafe
            then Left (IndeterminateInfinityOperation operator)
            else Right ()
        logical operands = do
          bools <- booleanTypeValue
          traverse recur operands >>= mapM_ (`check` bools)
          pure bools

        -- Argument maps try their written order before any permutation. This
        -- lets an inferred assignment use the corresponding slot annotation
        -- as context, while reordered calls still fall back to the complete
        -- argument-map check.
        checkFunctionArgument written actual expected =
          case check actual expected of
            Right () -> Right ()
            Left original -> do
              supplied <- case stripOuterIdentifierType actual of
                Right erased -> Right erased
                Left _ -> Right actual
              case validateFunctionInput supplied expected of
                Right () -> Right ()
                Left _ -> case checkValueOrder supplied expected original of
                  Right () -> Right ()
                  Left _ -> case checkWrittenOrder written expected original of
                    Right () -> Right ()
                    Left _ -> Left original

        checkValueOrder supplied expected original = do
          suppliedMembers <- case argumentRows supplied of
            Right (first : _) -> Right first
            _ -> Left original
          expectedMembers <- case argumentRows expected of
            Right (first : _) -> Right first
            _ -> Left original
          if length suppliedMembers /= length expectedMembers
            then Left original
            else mapM_ (uncurry (checkValueMember original))
              (zip suppliedMembers expectedMembers)

        checkValueMember original supplied expected = do
          (_, acceptsUnnamed, expectedType) <- expectedSlot expected
          if acceptsUnnamed
            then check supplied expectedType
            else Left original

        checkWrittenOrder written expected original = do
          expectedMembers <- case argumentRows expected of
            Right (first : _) -> Right first
            _ -> Left original
          let suppliedMembers = writtenMembers written
          if length suppliedMembers /= length expectedMembers
            then Left original
            else mapM_ (uncurry (checkMember original))
              (zip suppliedMembers expectedMembers)

        checkMember original supplied expected = do
          (expectedName, acceptsUnnamed, expectedType) <- expectedSlot expected
          case supplied of
            IdentifierOperation actualName annotation (Just value)
              | annotation == value -> do
                  case expectedName of
                    Just name | name /= actualName -> Left original
                    _ -> pure ()
                  recur value >>= (`check` expectedType)
            _
              | acceptsUnnamed ->
                  recur supplied >>= (`check` expectedType)
              | otherwise -> Left original

        expectedSlot expected =
          case optionalArgumentSlot expected of
            Just (name, annotation) ->
              Right (Just (IdentifierString name), True, annotation)
            Nothing -> case interpretedCanonicalResult expected of
              CanonicalSimpleIdentifierType name _ -> do
                underlying <- accessValues expected (naturalValue 1)
                Right (Just (IdentifierString name), False, underlying)
              _ -> Right (Nothing, True, expected)

        writtenMembers written = case written of
          AtlasMap values -> values
          MapSequence values -> values
          ArgumentMap values -> values
          MapConcatenation left right ->
            writtenMembers left <> writtenMembers right
          MapAccess source selectors ->
            mappedAccessMembers source selectors
          value -> [value]

        mappedAccessMembers source selectors =
          case selectors of
            AtlasMap values -> map (MapAccess source) values
            MapSequence values -> map (MapAccess source) values
            ArgumentMap values -> map (MapAccess source) values
            MapExpansion left right ->
              [MapAccess source left, MapAccess source right]
            MapConcatenation left right ->
              mappedAccessMembers source left
                <> mappedAccessMembers source right
            value -> [MapAccess source value]

lookupInferenceBinding :: String -> [InferenceBinding] -> Maybe InferenceBinding
lookupInferenceBinding name = go
  where
    go [] = Nothing
    go (binding : remaining)
      | bindingName binding == name = Just binding
      | otherwise = go remaining
    bindingName (InferenceBinding binding _ _ _) = binding
    bindingName (InferenceValueBinding binding _) = binding

check :: InterpretedValue -> InterpretedValue -> Either InterpretingError ()
check actual expected
  | interpretedCanonicalResult actual
      == interpretedCanonicalResult expected = Right ()
  | otherwise = do
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
