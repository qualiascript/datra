{-# LANGUAGE PatternSynonyms #-}

module DatraLanguage.AST
  ( SimpleIdentifierString (..)
  , GenericPolarity (..)
  , GenericBinderId (..)
  , GenericArgument (..)
  , mapGenericArgument
  , genericArgumentExpression
  , GenericBinder (..)
  , StringTemplateInterpolation (..)
  , IdentifierExpression (..)
  , DeclarationModifier (..)
  , declarationModifierOperator
  , DependentDeclaration (..)
  , dependentDeclarationIsValid
  , traverseDependentDeclaration
  , mapDependentDeclaration
  , Expression (..)
  , pattern FunctionType
  , attachedFunctionImplementation
  , OperatorExpression (..)
  , toOperatorExpression
  , traverseExpressionChildren
  , mapExpressionChildren
  , expressionChildren
  , yieldedIdentifier
  , namedBeginBlock
  , dependentArgumentExpression
  , dependentArgumentWithAnnotation
  , optionalIdentifierExpression
  , normalizeExpression
  ) where

import Data.Functor.Identity (Identity (..))
import Data.Functor.Const (Const (..))
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NonEmpty
import DatraLanguage.AST.Operator (Operator (..))
import DatraLanguage.StringTemplate (StringTemplateInterpolation (..))
import Numeric.Natural (Natural)

newtype SimpleIdentifierString = SimpleIdentifierString
  { simpleIdentifierStringText :: String
  }
  deriving (Eq, Ord, Show)

-- | The quantifier-like polarity of a function-owned generic binder.
data GenericPolarity
  = GenericProduct
  | GenericSum
  deriving (Eq, Ord, Show)

-- | Identity allocated by function-type scope resolution. Identifier text is
-- presentation; this identity distinguishes shadowed binders.
newtype GenericBinderId = GenericBinderId Natural
  deriving (Eq, Ord, Show)

-- | The complete syntax of one generic argument. Its name is structurally a
-- simple identifier, so generic resolution and evaluation never have to
-- recover a name from an arbitrary expression. The parser supplies @Any@ as
-- the bound when the @::@ clause is omitted.
data GenericArgument expression = GenericArgument
  { genericArgumentPolarity :: GenericPolarity
  , genericArgumentName :: SimpleIdentifierString
  , genericArgumentOptional :: Bool
  , genericArgumentBound :: expression
  }
  deriving (Eq, Ord, Show)

mapGenericArgument
  :: (left -> right)
  -> GenericArgument left
  -> GenericArgument right
mapGenericArgument visit argument = GenericArgument
  { genericArgumentPolarity = genericArgumentPolarity argument
  , genericArgumentName = genericArgumentName argument
  , genericArgumentOptional = genericArgumentOptional argument
  , genericArgumentBound = visit (genericArgumentBound argument)
  }

genericArgumentExpression :: GenericArgument Expression -> Expression
genericArgumentExpression argument =
  if genericArgumentOptional argument
    then OptionalType dependent
    else dependent
  where
    dependent = DependentArgument
      (IdentifierReference (genericArgumentName argument))
      (Just (genericArgumentBound argument))

-- | One entry in a resolved function type's ordered generic telescope.
data GenericBinder expression = GenericBinder
  { genericBinderId :: GenericBinderId
  , genericBinderArgument :: GenericArgument expression
  }
  deriving (Eq, Ord, Show)

-- | The two expression families that can name a dependent declaration.
-- Keeping scalar string conversion and Atlas template conversion distinct
-- prevents either operator from silently accepting the other's operand kind.
data IdentifierExpression expression
  = IdentifierExpressionBody expression
  | AtlasIdentifierExpressionBody expression
  deriving (Eq, Ord, Show)

-- | A declaration is semantic block structure, not an expression which must
-- later be recognized by inspecting modifier and assignment nodes.
-- | Modifier applications in a declaration are recorded from the innermost
-- application to the outermost application: the right-to-left order in which
-- declared syntax is expanded.
data DeclarationModifier
  = DeclarationLet
  | DeclarationDef
  | DeclarationVal
  deriving (Eq, Ord, Show)

declarationModifierOperator :: DeclarationModifier -> Operator
declarationModifierOperator modifier = case modifier of
  DeclarationLet -> LetOperator
  DeclarationDef -> DefOperator
  DeclarationVal -> ValOperator

data DependentDeclaration expression = DependentDeclaration
  { dependentDeclarationHead :: IdentifierExpression expression
  , dependentDeclarationIsLet :: Bool
  , dependentDeclarationIsDefinition :: Bool
  , dependentDeclarationIsCanonicalValue :: Bool
  , dependentDeclarationModifierApplications :: [DeclarationModifier]
  , dependentDeclarationImplementation :: expression
  }
  deriving (Eq, Ord, Show)

traverseDependentDeclaration
  :: Applicative f
  => (left -> f right)
  -> DependentDeclaration left
  -> f (DependentDeclaration right)
traverseDependentDeclaration visit declaration = DependentDeclaration
  <$> traverseHead (dependentDeclarationHead declaration)
  <*> pure (dependentDeclarationIsLet declaration)
  <*> pure (dependentDeclarationIsDefinition declaration)
  <*> pure (dependentDeclarationIsCanonicalValue declaration)
  <*> pure (dependentDeclarationModifierApplications declaration)
  <*> visit (dependentDeclarationImplementation declaration)
  where
    traverseHead headValue = case headValue of
      IdentifierExpressionBody body -> IdentifierExpressionBody <$> visit body
      AtlasIdentifierExpressionBody body ->
        AtlasIdentifierExpressionBody <$> visit body

mapDependentDeclaration
  :: (left -> right)
  -> DependentDeclaration left
  -> DependentDeclaration right
mapDependentDeclaration transform =
  runIdentity . traverseDependentDeclaration (pure . transform)

dependentDeclarationIsValid :: DependentDeclaration expression -> Bool
dependentDeclarationIsValid declaration = applications == canonical
  where
    applications = dependentDeclarationModifierApplications declaration
    canonical = filter (`elem` applications)
      [DeclarationVal, DeclarationDef, DeclarationLet]

-- | Unevaluated Datra syntax. Capabilities and silent coercions are resolved
-- later by the type checker and interpreter, not while constructing the AST.
data Expression
  = EllipsisNatural Natural
  | EllipsisLiteral
  | Skip
  | AsciiStringLiteral String
  | NothingLiteral
  | StringTemplate [StringTemplateInterpolation Expression]
  | IdentifierExpression Expression
  | AtlasIdentifierExpression Expression
  | AtlasMap [Expression]
  | ArgumentativeMap [Expression]
  | MapSequence [Expression]
  -- | A transient raw-parser boundary. Declarative syntax rewriting removes
  -- it before the public/post-matching AST is exposed.
  | SyntaxBoundary Expression
  | MapExpansion Expression Expression
  | SuperEllipsisRange Expression Expression
  | SuperEllipsisRangePlus Expression
  | SuperEllipsisRangeMinus Expression
  | NaturalRange Natural Natural
  | NaturalRangeUpwards Natural
  | ValuedNaturalRange Natural Natural
  | ValuedNaturalRangeUpwards Natural
  | NaturalType
  | IntegerRange Integer Integer
  | IntegerRangeUpwards Integer
  | IntegerRangeDownwards Integer
  | ValuedIntegerRange Integer Integer
  | ValuedIntegerRangeUpwards Integer
  | ValuedIntegerRangeDownwards Integer
  | IntegerType
  | BooleanLiteral Bool
  | BooleanType
  | EitherType Expression Expression
  | OptionalType Expression
  | MaybeThen Expression Expression
  | Conditional Expression Expression Expression
  | Addition Expression Expression
  | Subtraction Expression Expression
  | Plus Expression
  | Minus Expression
  | Equality Expression Expression
  | Inequality Expression Expression
  | LessThan Expression Expression
  | LessThanOrEqual Expression Expression
  | GreaterThan Expression Expression
  | GreaterThanOrEqual Expression Expression
  | Coalization Expression
  | Fun Expression
  | GenericIntroductionExpression (GenericArgument Expression)
  | InModule String Expression
  | Import [String] Expression
  | FunctionTypeExpression [GenericBinder Expression] Expression Expression
  | FunctionBody [DependentDeclaration Expression] Expression
  | FunctionApplication Expression Expression
  | DeclarationExpression (DependentDeclaration Expression)
  | Begin [DependentDeclaration Expression] Expression
  | IdentifierReference SimpleIdentifierString
  | Lookup Expression
  | Multiplication Expression Expression
  | Exponentiation Expression Expression
  | MapConcatenation Expression Expression
  | ScopeAccess Expression Expression
  | MapAccess Expression Expression
  | MapSpecification Expression Expression
  | Overload Expression Expression
  | SafeOverload Expression Expression
  -- | Transient raw-parser forms retain written operand order until syntax
  -- rewriting has found source-order block delimiters such as @yield@.
  | ReverseMapSpecification Expression Expression
  | ReverseOverload Expression Expression
  | ReverseSafeOverload Expression Expression
  | DependentArgument
      { dependentArgumentName :: Expression
      , dependentArgumentTypeAnnotation :: Maybe Expression
      }
  deriving (Eq, Ord, Show)

-- | Convenience pattern for a function type without a generic prefix.
-- Generic-aware code matches 'FunctionTypeExpression' directly so a
-- transformation cannot silently discard a non-empty telescope.
pattern FunctionType :: Expression -> Expression -> Expression
pattern FunctionType domain codomain = FunctionTypeExpression [] domain codomain

-- | The implementation attached by a function specification expression.
-- This is structural syntax information; inspecting it does not evaluate the
-- function's domain or codomain.
attachedFunctionImplementation :: Expression -> Maybe Expression
attachedFunctionImplementation expression = case expression of
  FunctionApplication FunctionTypeExpression {} implementation ->
    Just implementation
  MapSpecification implementation FunctionTypeExpression {} ->
    Just implementation
  _ -> Nothing

-- | A module resource yields exactly one simple identifier type. Its
-- annotation or assigned implementation is the value imported under that
-- identifier.
yieldedIdentifier
  :: Expression
  -> Maybe (SimpleIdentifierString, Expression, Maybe Expression)
yieldedIdentifier (Begin _ result) = yieldedIdentifier result
yieldedIdentifier (ScopeAccess _ body) = yieldedIdentifier body
yieldedIdentifier (Import _ (FunctionBody _ result)) = yieldedIdentifier result
yieldedIdentifier
    (DependentArgument (IdentifierReference name) (Just annotation)) =
  Just (name, annotation, Nothing)
yieldedIdentifier
    (MapSpecification given
      (DependentArgument (IdentifierReference name) annotation)) =
  Just (name, maybe given id annotation, Just given)
yieldedIdentifier _ = Nothing

-- | Some named module values are begin blocks. Their declarations remain
-- available for syntax discovery and lexical evaluation, but begin is not a
-- requirement of the general import contract.
namedBeginBlock
  :: Expression
  -> Maybe
      (SimpleIdentifierString, [DependentDeclaration Expression], Expression)
namedBeginBlock expressionValue = do
  (name, annotation, given) <- yieldedIdentifier expressionValue
  let value = maybe annotation id given
  case value of
    Begin bindings result -> Just (name, bindings, result)
    _ -> Nothing

-- | View both a bare dependent argument and its specification-sugar form.
-- Assignment does not add another dependent-argument AST case: @name := value@
-- is @MapSpecification value (DependentArgument name Nothing)@.
dependentArgumentExpression
  :: Expression
  -> Maybe (Expression, Maybe Expression, Maybe Expression)
dependentArgumentExpression (DependentArgument name annotation) =
  Just (name, annotation, Nothing)
dependentArgumentExpression
    (MapSpecification given (DependentArgument name annotation)) =
  Just (name, annotation, Just given)
dependentArgumentExpression _ = Nothing

-- | Attach an annotation to a parsed argument name without decoding and
-- reconstructing optional-name syntax in each caller.
dependentArgumentWithAnnotation :: Expression -> Expression -> Expression
dependentArgumentWithAnnotation name annotation = case name of
  OptionalType present ->
    OptionalType (DependentArgument present (Just annotation))
  _ -> DependentArgument name (Just annotation)

-- | Recover the present and unnamed alternatives represented by identifier
-- postfix @?@. Other optional nodes use ordinary @Maybe T@ semantics.
optionalIdentifierExpression
  :: Expression
  -> Maybe (Expression, Expression)
optionalIdentifierExpression (OptionalType operation) =
  case operation of
    DependentArgument _ (Just annotation) -> Just (operation, annotation)
    MapSpecification given (DependentArgument _ annotation) ->
      Just (operation, maybe given id annotation)
    _ -> Nothing
optionalIdentifierExpression _ = Nothing

data OperatorExpression
  = NaturalValue Natural
  | EllipsisValue
  | SkipValue
  | AsciiStringValue String
  | NothingValue
  | StringTemplateValue [StringTemplateInterpolation OperatorExpression]
  | IdentifierExpressionValue OperatorExpression
  | AtlasIdentifierExpressionValue OperatorExpression
  | EmptyMap
  | Sequential (NonEmpty OperatorExpression)
  | ArgumentativeMapValue [OperatorExpression]
  | Expansion OperatorExpression OperatorExpression
  | Range OperatorExpression OperatorExpression
  | RangePlus OperatorExpression
  | RangeMinus OperatorExpression
  | InclusiveNaturalRange Natural Natural
  | InclusiveNaturalRangeUpwards Natural
  | InclusiveValuedNaturalRange Natural Natural
  | InclusiveValuedNaturalRangeUpwards Natural
  | NaturalTypeValue
  | InclusiveIntegerRange Integer Integer
  | InclusiveIntegerRangeUpwards Integer
  | InclusiveIntegerRangeDownwards Integer
  | InclusiveValuedIntegerRange Integer Integer
  | InclusiveValuedIntegerRangeUpwards Integer
  | InclusiveValuedIntegerRangeDownwards Integer
  | IntegerTypeValue
  | BooleanValue Bool
  | BooleanTypeValue
  | EitherValue OperatorExpression OperatorExpression
  | OptionalValue OperatorExpression
  | MaybeThenValue OperatorExpression OperatorExpression
  | ConditionalValue
      OperatorExpression
      OperatorExpression
      OperatorExpression
  | Add OperatorExpression OperatorExpression
  | Subtract OperatorExpression OperatorExpression
  | Positive OperatorExpression
  | Negate OperatorExpression
  | Equal OperatorExpression OperatorExpression
  | NotEqual OperatorExpression OperatorExpression
  | Less OperatorExpression OperatorExpression
  | LessOrEqual OperatorExpression OperatorExpression
  | Greater OperatorExpression OperatorExpression
  | GreaterOrEqual OperatorExpression OperatorExpression
  | CoalizationValue OperatorExpression
  | FunValue OperatorExpression
  | GenericIntroductionValue
      (GenericArgument OperatorExpression)
  | InModuleValue String OperatorExpression
  | ImportValue [String] OperatorExpression
  | FunctionTypeValue
      [GenericBinder OperatorExpression]
      OperatorExpression
      OperatorExpression
  | FunctionBodyValue
      [DependentDeclaration OperatorExpression]
      OperatorExpression
  | FunctionApplicationValue OperatorExpression OperatorExpression
  | DeclarationValue (DependentDeclaration OperatorExpression)
  | BeginValue
      [DependentDeclaration OperatorExpression]
      OperatorExpression
  | IdentifierReferenceValue SimpleIdentifierString
  | LookupValue OperatorExpression
  | Multiply OperatorExpression OperatorExpression
  | Power OperatorExpression OperatorExpression
  | Concatenate OperatorExpression OperatorExpression
  | ScopeAccessValue OperatorExpression OperatorExpression
  | Access OperatorExpression OperatorExpression
  | Specify OperatorExpression OperatorExpression
  | OverloadValue OperatorExpression OperatorExpression
  | SafeOverloadValue OperatorExpression OperatorExpression
  | DependentArgumentValue
      OperatorExpression
      (Maybe OperatorExpression)
  deriving (Eq, Show)

toOperatorExpression :: Expression -> OperatorExpression
toOperatorExpression = lower

normalizeExpression :: Expression -> Expression
normalizeExpression (EllipsisNatural value) = EllipsisNatural value
normalizeExpression EllipsisLiteral = EllipsisLiteral
normalizeExpression Skip = Skip
normalizeExpression (AsciiStringLiteral value) = AsciiStringLiteral value
normalizeExpression NothingLiteral = NothingLiteral
normalizeExpression (StringTemplate parts) =
  StringTemplate (map normalizeStringTemplateInterpolation parts)
normalizeExpression (IdentifierExpression operand) =
  IdentifierExpression (normalizeExpression operand)
normalizeExpression (AtlasIdentifierExpression operand) =
  AtlasIdentifierExpression (normalizeExpression operand)
normalizeExpression (AtlasMap expressions) =
  normalizeSequence AtlasMap expressions
normalizeExpression (ArgumentativeMap expressions) =
  ArgumentativeMap (map normalizeExpression expressions)
normalizeExpression (MapSequence expressions) =
  normalizeSequence MapSequence expressions
normalizeExpression (SyntaxBoundary expressionValue) =
  normalizeExpression expressionValue
normalizeExpression (MapExpansion left right) =
  normalizeExpansion
    (normalizeExpression left)
    (normalizeExpression right)
normalizeExpression (SuperEllipsisRange lowerBound upperBound) =
  SuperEllipsisRange
    (normalizeExpression lowerBound)
    (normalizeExpression upperBound)
normalizeExpression (SuperEllipsisRangePlus lowerBound) =
  SuperEllipsisRangePlus (normalizeExpression lowerBound)
normalizeExpression (SuperEllipsisRangeMinus upperBound) =
  SuperEllipsisRangeMinus (normalizeExpression upperBound)
normalizeExpression (NaturalRange origin target) = NaturalRange origin target
normalizeExpression (NaturalRangeUpwards origin) = NaturalRangeUpwards origin
normalizeExpression (ValuedNaturalRange origin target) =
  ValuedNaturalRange origin target
normalizeExpression (ValuedNaturalRangeUpwards origin) =
  ValuedNaturalRangeUpwards origin
normalizeExpression NaturalType = NaturalType
normalizeExpression (IntegerRange origin target) = IntegerRange origin target
normalizeExpression (IntegerRangeUpwards origin) = IntegerRangeUpwards origin
normalizeExpression (IntegerRangeDownwards origin) = IntegerRangeDownwards origin
normalizeExpression (ValuedIntegerRange origin target) =
  ValuedIntegerRange origin target
normalizeExpression (ValuedIntegerRangeUpwards origin) =
  ValuedIntegerRangeUpwards origin
normalizeExpression (ValuedIntegerRangeDownwards origin) =
  ValuedIntegerRangeDownwards origin
normalizeExpression IntegerType = IntegerType
normalizeExpression (BooleanLiteral value) = BooleanLiteral value
normalizeExpression BooleanType = BooleanType
normalizeExpression (EitherType left right) =
  normalizeEither
    (normalizeExpression left)
    (normalizeExpression right)
normalizeExpression (OptionalType operand) =
  OptionalType (normalizeExpression operand)
normalizeExpression (MaybeThen optional branch) =
  MaybeThen (normalizeExpression optional) (normalizeExpression branch)
normalizeExpression (Conditional condition consequent alternative) =
  Conditional
    (normalizeExpression condition)
    (normalizeExpression consequent)
    (normalizeExpression alternative)
normalizeExpression (Addition left right) =
  Addition (normalizeExpression left) (normalizeExpression right)
normalizeExpression (Subtraction left right) =
  Subtraction (normalizeExpression left) (normalizeExpression right)
normalizeExpression (Plus operand) = Plus (normalizeExpression operand)
normalizeExpression (Minus operand) = Minus (normalizeExpression operand)
normalizeExpression (Equality left right) =
  Equality (normalizeExpression left) (normalizeExpression right)
normalizeExpression (Inequality left right) =
  Inequality (normalizeExpression left) (normalizeExpression right)
normalizeExpression (LessThan left right) =
  LessThan (normalizeExpression left) (normalizeExpression right)
normalizeExpression (LessThanOrEqual left right) =
  LessThanOrEqual (normalizeExpression left) (normalizeExpression right)
normalizeExpression (GreaterThan left right) =
  GreaterThan (normalizeExpression left) (normalizeExpression right)
normalizeExpression (GreaterThanOrEqual left right) =
  GreaterThanOrEqual (normalizeExpression left) (normalizeExpression right)
normalizeExpression (Coalization operand) =
  Coalization (normalizeExpression operand)
normalizeExpression (Fun operand) = Fun (normalizeExpression operand)
normalizeExpression (GenericIntroductionExpression introduction) =
  GenericIntroductionExpression
    (mapGenericArgument normalizeExpression introduction)
normalizeExpression (InModule path value) = InModule path (normalizeExpression value)
normalizeExpression (Import paths body) =
  Import paths (normalizeExpression body)
normalizeExpression (FunctionTypeExpression generics input output) =
  FunctionTypeExpression
      [ binder
        { genericBinderArgument =
            mapGenericArgument normalizeExpression (genericBinderArgument binder)
        }
    | binder <- generics
    ]
    (normalizeExpression input)
    (normalizeExpression output)
normalizeExpression (FunctionBody bindings result) =
  FunctionBody
    (map (mapDependentDeclaration normalizeExpression) bindings)
    (normalizeExpression result)
normalizeExpression (FunctionApplication function input) = FunctionApplication (normalizeExpression function) (normalizeExpression input)
normalizeExpression (DeclarationExpression declaration) =
  DeclarationExpression (mapDependentDeclaration normalizeExpression declaration)
normalizeExpression (Begin bindings result) =
  Begin
    (map (mapDependentDeclaration normalizeExpression) bindings)
    (normalizeExpression result)
normalizeExpression (IdentifierReference name) = IdentifierReference name
normalizeExpression (Lookup operand) = Lookup (normalizeExpression operand)
normalizeExpression (Multiplication left right) =
  Multiplication (normalizeExpression left) (normalizeExpression right)
normalizeExpression (Exponentiation left right) =
  Exponentiation (normalizeExpression left) (normalizeExpression right)
normalizeExpression (MapConcatenation left right) =
  MapConcatenation (normalizeExpression left) (normalizeExpression right)
normalizeExpression (ScopeAccess source body) =
  ScopeAccess (normalizeExpression source) (normalizeExpression body)
normalizeExpression (MapAccess left right) =
  MapAccess (normalizeExpression left) (normalizeExpression right)
normalizeExpression (MapSpecification left right) =
  MapSpecification (normalizeExpression left) (normalizeExpression right)
normalizeExpression (Overload left right) =
  Overload (normalizeExpression left) (normalizeExpression right)
normalizeExpression (SafeOverload left right) =
  SafeOverload (normalizeExpression left) (normalizeExpression right)
normalizeExpression (ReverseMapSpecification target source) =
  MapSpecification (normalizeExpression source) (normalizeExpression target)
normalizeExpression (ReverseOverload supplied defaults) =
  Overload (normalizeExpression defaults) (normalizeExpression supplied)
normalizeExpression (ReverseSafeOverload supplied defaults) =
  SafeOverload (normalizeExpression defaults) (normalizeExpression supplied)
normalizeExpression (DependentArgument name typeAnnotation) =
  DependentArgument
    (normalizeDependentArgumentName name)
    (normalizeExpression <$> typeAnnotation)

normalizeDependentArgumentName :: Expression -> Expression
normalizeDependentArgumentName name@IdentifierReference {} = name
normalizeDependentArgumentName name = normalizeExpression name

normalizeStringTemplateInterpolation
  :: StringTemplateInterpolation Expression
  -> StringTemplateInterpolation Expression
normalizeStringTemplateInterpolation
    (StringTemplateInterpolation expressionValue) =
  StringTemplateInterpolation (normalizeExpression expressionValue)

-- | Empty maps are neutral sequence members and a one-member sequence adds no
-- genuine Atlas page: beyond an Atlas's finite presentation its final page is
-- already repeated. Only a sequence with at least two members introduces a
-- structural boundary.
normalizeSequence
  :: ([Expression] -> Expression)
  -> [Expression]
  -> Expression
normalizeSequence constructor expressions =
  case filter (not . isEmptyMap) (map normalizeExpression expressions) of
    [] -> AtlasMap []
    [expressionValue] -> expressionValue
    normalized -> constructor normalized

normalizeExpansion :: Expression -> Expression -> Expression
normalizeExpansion left right
  | isEmptyMap left = right
  | isEmptyMap right = left
  | otherwise = MapExpansion left right

-- Either is associative. Flattening and rebuilding to the right gives every
-- source spelling one injection tree, so its Boolean tag paths are stable.
normalizeEither :: Expression -> Expression -> Expression
normalizeEither left right = buildEither (eitherMembers left <> eitherMembers right)
  where
    buildEither [member] = member
    buildEither (member : members) = EitherType member (buildEither members)
    buildEither [] = EitherType left right

eitherMembers :: Expression -> [Expression]
eitherMembers (EitherType left right) =
  eitherMembers left <> eitherMembers right
eitherMembers expressionValue = [expressionValue]

isEmptyMap :: Expression -> Bool
isEmptyMap (AtlasMap []) = True
isEmptyMap (MapSequence []) = True
isEmptyMap _ = False

lower :: Expression -> OperatorExpression
lower (EllipsisNatural value) = NaturalValue value
lower EllipsisLiteral = EllipsisValue
lower Skip = SkipValue
lower (AsciiStringLiteral value) = AsciiStringValue value
lower NothingLiteral = NothingValue
lower (StringTemplate parts) =
  StringTemplateValue (map lowerStringTemplateInterpolation parts)
lower (IdentifierExpression operand) = IdentifierExpressionValue (lower operand)
lower (AtlasIdentifierExpression operand) =
  AtlasIdentifierExpressionValue (lower operand)
lower (AtlasMap []) = EmptyMap
lower (AtlasMap expressions) =
  combineExpansions (map lowerSegment (segments expressions))
lower (ArgumentativeMap expressions) =
  ArgumentativeMapValue (map lower expressions)
lower (MapSequence []) = EmptyMap
lower (MapSequence (expressionValue : expressions)) =
  Sequential (lower expressionValue :| map lower expressions)
lower (SyntaxBoundary expressionValue) = lower expressionValue
lower (MapExpansion left right) = Expansion (lower left) (lower right)
lower (SuperEllipsisRange lowerBound upperBound) =
  Range (lower lowerBound) (lower upperBound)
lower (SuperEllipsisRangePlus lowerBound) = RangePlus (lower lowerBound)
lower (SuperEllipsisRangeMinus upperBound) = RangeMinus (lower upperBound)
lower (NaturalRange origin target) = InclusiveNaturalRange origin target
lower (NaturalRangeUpwards origin) = InclusiveNaturalRangeUpwards origin
lower (ValuedNaturalRange origin target) =
  InclusiveValuedNaturalRange origin target
lower (ValuedNaturalRangeUpwards origin) =
  InclusiveValuedNaturalRangeUpwards origin
lower NaturalType = NaturalTypeValue
lower (IntegerRange origin target) = InclusiveIntegerRange origin target
lower (IntegerRangeUpwards origin) = InclusiveIntegerRangeUpwards origin
lower (IntegerRangeDownwards origin) = InclusiveIntegerRangeDownwards origin
lower (ValuedIntegerRange origin target) =
  InclusiveValuedIntegerRange origin target
lower (ValuedIntegerRangeUpwards origin) =
  InclusiveValuedIntegerRangeUpwards origin
lower (ValuedIntegerRangeDownwards origin) =
  InclusiveValuedIntegerRangeDownwards origin
lower IntegerType = IntegerTypeValue
lower (BooleanLiteral value) = BooleanValue value
lower BooleanType = BooleanTypeValue
lower (EitherType left right) = EitherValue (lower left) (lower right)
lower (OptionalType operand) = OptionalValue (lower operand)
lower (MaybeThen optional branch) =
  MaybeThenValue (lower optional) (lower branch)
lower (Conditional condition consequent alternative) =
  ConditionalValue (lower condition) (lower consequent) (lower alternative)
lower (Addition left right) = Add (lower left) (lower right)
lower (Subtraction left right) = Subtract (lower left) (lower right)
lower (Plus operand) = Positive (lower operand)
lower (Minus operand) = Negate (lower operand)
lower (Equality left right) = Equal (lower left) (lower right)
lower (Inequality left right) = NotEqual (lower left) (lower right)
lower (LessThan left right) = Less (lower left) (lower right)
lower (LessThanOrEqual left right) = LessOrEqual (lower left) (lower right)
lower (GreaterThan left right) = Greater (lower left) (lower right)
lower (GreaterThanOrEqual left right) = GreaterOrEqual (lower left) (lower right)
lower (Coalization operand) = CoalizationValue (lower operand)
lower (Fun operand) = FunValue (lower operand)
lower (GenericIntroductionExpression introduction) =
  GenericIntroductionValue (mapGenericArgument lower introduction)
lower (InModule path value) = InModuleValue path (lower value)
lower (Import paths body) = ImportValue paths (lower body)
lower (FunctionTypeExpression generics input output) =
  FunctionTypeValue
    [ binder
        { genericBinderArgument =
            mapGenericArgument lower (genericBinderArgument binder)
        }
    | binder <- generics
    ]
    (lower input)
    (lower output)
lower (FunctionBody bindings result) = FunctionBodyValue
  (map (mapDependentDeclaration lower) bindings) (lower result)
lower (FunctionApplication function input) = FunctionApplicationValue (lower function) (lower input)
lower (DeclarationExpression declaration) =
  DeclarationValue (mapDependentDeclaration lower declaration)
lower (Begin bindings result) = BeginValue
  (map (mapDependentDeclaration lower) bindings) (lower result)
lower (IdentifierReference name) = IdentifierReferenceValue name
lower (Lookup operand) = LookupValue (lower operand)
lower (Multiplication left right) = Multiply (lower left) (lower right)
lower (Exponentiation left right) = Power (lower left) (lower right)
lower (MapConcatenation left right) =
  Concatenate (lower left) (lower right)
lower (ScopeAccess source body) = ScopeAccessValue (lower source) (lower body)
lower (MapAccess left right) = Access (lower left) (lower right)
lower (MapSpecification left right) = Specify (lower left) (lower right)
lower (Overload left right) = OverloadValue (lower left) (lower right)
lower (SafeOverload left right) = SafeOverloadValue (lower left) (lower right)
lower (ReverseMapSpecification target source) =
  Specify (lower source) (lower target)
lower (ReverseOverload supplied defaults) =
  OverloadValue (lower defaults) (lower supplied)
lower (ReverseSafeOverload supplied defaults) =
  SafeOverloadValue (lower defaults) (lower supplied)
lower (DependentArgument name typeAnnotation) =
  DependentArgumentValue (lower name) (lower <$> typeAnnotation)

lowerStringTemplateInterpolation
  :: StringTemplateInterpolation Expression
  -> StringTemplateInterpolation OperatorExpression
lowerStringTemplateInterpolation
    (StringTemplateInterpolation expressionValue) =
  StringTemplateInterpolation (lower expressionValue)

data Segment
  = ExpressionSegment (NonEmpty Expression)
  | MapSegment Expression

-- Consecutive expressions occupy one level. Each directly nested map
-- delimits another level, even when that map contains only one expression.
segments :: [Expression] -> [Segment]
segments = go []
  where
    go expressions [] = finishExpressions expressions
    go expressions (nested@(AtlasMap _) : rest) =
      finishExpressions expressions <> (MapSegment nested : go [] rest)
    go expressions (next : rest) = go (next : expressions) rest

    finishExpressions =
      maybe [] (pure . ExpressionSegment) . NonEmpty.nonEmpty . reverse

lowerSegment :: Segment -> OperatorExpression
lowerSegment (ExpressionSegment (value :| [])) = lower value
lowerSegment (ExpressionSegment values) = Sequential (lower <$> values)
lowerSegment (MapSegment expressionValue) = lower expressionValue

combineExpansions :: [OperatorExpression] -> OperatorExpression
combineExpansions [] = EmptyMap
combineExpansions [expressionValue] = expressionValue
combineExpansions (firstExpression : rest) =
  Expansion firstExpression (combineExpansions rest)


-- | One shared traversal of immediate AST children, preserving identifiers and
-- literal metadata. Analyses and source migrations compose it recursively.
traverseExpressionChildren :: Applicative f => (Expression -> f Expression) -> Expression -> f Expression
traverseExpressionChildren visit expression = case expression of
  AtlasMap xs -> AtlasMap <$> traverse visit xs
  ArgumentativeMap xs -> ArgumentativeMap <$> traverse visit xs
  MapSequence xs -> MapSequence <$> traverse visit xs
  SyntaxBoundary x -> SyntaxBoundary <$> visit x
  Plus x -> Plus <$> visit x
  Minus x -> Minus <$> visit x
  Coalization x -> Coalization <$> visit x
  OptionalType x -> OptionalType <$> visit x
  SuperEllipsisRangePlus x -> SuperEllipsisRangePlus <$> visit x
  SuperEllipsisRangeMinus x -> SuperEllipsisRangeMinus <$> visit x
  MapExpansion a b -> MapExpansion <$> visit a <*> visit b
  SuperEllipsisRange a b -> SuperEllipsisRange <$> visit a <*> visit b
  EitherType a b -> EitherType <$> visit a <*> visit b
  MaybeThen a b -> MaybeThen <$> visit a <*> visit b
  Addition a b -> Addition <$> visit a <*> visit b
  Subtraction a b -> Subtraction <$> visit a <*> visit b
  Equality a b -> Equality <$> visit a <*> visit b
  Inequality a b -> Inequality <$> visit a <*> visit b
  LessThan a b -> LessThan <$> visit a <*> visit b
  LessThanOrEqual a b -> LessThanOrEqual <$> visit a <*> visit b
  GreaterThan a b -> GreaterThan <$> visit a <*> visit b
  GreaterThanOrEqual a b -> GreaterThanOrEqual <$> visit a <*> visit b
  Fun x -> Fun <$> visit x
  GenericIntroductionExpression introduction ->
    (\bound -> GenericIntroductionExpression
      introduction { genericArgumentBound = bound })
      <$> visit (genericArgumentBound introduction)
  FunctionTypeExpression generics domain codomain ->
    FunctionTypeExpression
      <$> traverse visitBinder generics
      <*> visit domain
      <*> visit codomain
  FunctionApplication a b -> FunctionApplication <$> visit a <*> visit b
  DeclarationExpression declaration ->
    DeclarationExpression <$> traverseDependentDeclaration visit declaration
  Lookup operand -> Lookup <$> visit operand
  Multiplication a b -> Multiplication <$> visit a <*> visit b
  Exponentiation a b -> Exponentiation <$> visit a <*> visit b
  MapConcatenation left right ->
    MapConcatenation <$> visit left <*> visit right
  MapAccess a b -> MapAccess <$> visit a <*> visit b
  MapSpecification a b -> MapSpecification <$> visit a <*> visit b
  Overload a b -> Overload <$> visit a <*> visit b
  SafeOverload a b -> SafeOverload <$> visit a <*> visit b
  ReverseMapSpecification a b ->
    ReverseMapSpecification <$> visit a <*> visit b
  ReverseOverload a b -> ReverseOverload <$> visit a <*> visit b
  ReverseSafeOverload a b -> ReverseSafeOverload <$> visit a <*> visit b
  Begin xs y ->
    Begin <$> traverse (traverseDependentDeclaration visit) xs <*> visit y
  FunctionBody xs y -> FunctionBody
    <$> traverse (traverseDependentDeclaration visit) xs
    <*> visit y
  Conditional a b c -> Conditional <$> visit a <*> visit b <*> visit c
  InModule path value -> InModule path <$> visit value
  Import paths body -> Import paths <$> visit body
  ScopeAccess source body -> ScopeAccess <$> visit source <*> visit body
  DependentArgument name annotation ->
    DependentArgument
      <$> visitDependentArgumentName name
      <*> traverse visit annotation
  StringTemplate parts -> StringTemplate <$> traverse part parts
  IdentifierExpression operand -> IdentifierExpression <$> visit operand
  AtlasIdentifierExpression operand ->
    AtlasIdentifierExpression <$> visit operand
  _ -> pure expression
  where
    visitBinder binder =
      (\bound -> binder
        { genericBinderArgument =
            (genericBinderArgument binder) { genericArgumentBound = bound }
        })
        <$> visit (genericArgumentBound (genericBinderArgument binder))
    part (StringTemplateInterpolation value) =
      StringTemplateInterpolation <$> visit value
    visitDependentArgumentName name@IdentifierReference {} = pure name
    visitDependentArgumentName name = visit name

mapExpressionChildren :: (Expression -> Expression) -> Expression -> Expression
mapExpressionChildren visit = runIdentity . traverseExpressionChildren (Identity . visit)

expressionChildren :: Expression -> [Expression]
expressionChildren = getConst . traverseExpressionChildren (Const . (:[]))
