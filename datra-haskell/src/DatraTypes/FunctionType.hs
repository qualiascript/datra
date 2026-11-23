{-# LANGUAGE PatternSynonyms #-}

-- | Function-type and generic normalization independent of concrete parsing.
module DatraTypes.FunctionType
  ( FunctionTypeIdentifier (..)
  , PreparedFunctionDomainKind (..)
  , PreparedFunctionDomainMember (..)
  , PreparedFunctionDomain (..)
  , functionTypeIdentifiers
  , prepareFunctionDomain
  , prepareFunctionDomainExpression
  , prepareGenericExpression
  , forwardGenericBoundReference
  , inferredFunction
  , resolveGenericFunctionTypes
  ) where

import Control.Monad.Trans.State.Strict (State, evalState, get, put)
import DatraLanguage.AST
import Numeric.Natural (Natural)

data FunctionTypeIdentifier
  = SimpleFunctionTypeIdentifier SimpleIdentifierString
  | DependentFunctionTypeIdentifier Expression
  deriving (Eq, Show)

-- | Container behavior retained while generic binders become real leading
-- domain members. Both parenthesized Atlas maps and semicolon map sequences
-- use the ordered path; argumentative maps retain their name-matching boundary.
data PreparedFunctionDomainKind
  = PreparedOrderedFunctionDomain
  | PreparedArgumentFunctionDomain
  | PreparedScalarFunctionDomain
  deriving (Eq, Show)

data PreparedFunctionDomainMember
  = PreparedGenericFunctionDomainMember (GenericBinder Expression)
  | PreparedOrdinaryFunctionDomainMember Expression
  deriving (Eq, Show)

data PreparedFunctionDomain = PreparedFunctionDomain
  { preparedFunctionDomainKind :: PreparedFunctionDomainKind
  , preparedFunctionDomainMembers :: [PreparedFunctionDomainMember]
  }
  deriving (Eq, Show)

type GenericResolution = State Natural

-- Generic declarations are collected after the source parser has
-- established arrow ownership. This gives every binder a globally unique AST
-- identity while keeping nested function domains independent.
resolveGenericFunctionTypes :: Expression -> Expression
resolveGenericFunctionTypes expressionValue =
  evalState
    (resolveGenericExpression expressionValue)
    (nextGenericBinderId expressionValue)

-- Resolution also runs after declarative rewriting, when arrow-less function
-- bodies have acquired function types. Continue above any identities already
-- allocated by the source parse so the second pass cannot alias binders.
nextGenericBinderId :: Expression -> Natural
nextGenericBinderId expressionValue = case genericBinderIds expressionValue of
  [] -> 0
  identities -> maximum identities + 1
  where
    genericBinderIds value = current <> concatMap genericBinderIds
      (expressionChildren value)
      where
        current = case value of
          FunctionTypeExpression binders _ _ ->
            [ identity
            | GenericBinderId identity <- map genericBinderId binders
            ]
          _ -> []

resolveGenericExpression
  :: Expression
  -> GenericResolution Expression
resolveGenericExpression expressionValue =
  case expressionValue of
    FunctionTypeExpression [] domain codomain ->
      resolveNewGenericFunctionType domain codomain
    FunctionTypeExpression generics domain codomain -> do
      resolvedGenerics <- traverse
        (\binder -> do
          bound <- resolveGenericExpression
            (genericArgumentBound (genericBinderArgument binder))
          pure binder
            { genericBinderArgument =
                (genericBinderArgument binder) { genericArgumentBound = bound }
            })
        generics
      resolvedDomain <- resolveGenericExpression domain
      resolvedCodomain <- resolveGenericExpression codomain
      pure (FunctionTypeExpression
        resolvedGenerics resolvedDomain resolvedCodomain)
    GenericIntroductionExpression introduction -> do
      bound <- resolveGenericExpression (genericArgumentBound introduction)
      pure (GenericIntroductionExpression
        introduction { genericArgumentBound = bound })
    _ -> traverseExpressionChildren
      resolveGenericExpression
      expressionValue

resolveNewGenericFunctionType
  :: Expression
  -> Expression
  -> GenericResolution Expression
resolveNewGenericFunctionType domain codomain = do
  let introductions = collectOwnedGenericIntroductions domain
  identities <- traverse (const freshGenericBinderId) introductions
  let declarations = zip introductions identities
  binders <- resolveGenericBinders declarations
  resolvedDomain <- resolveOwnedGenericDomain declarations domain
  resolvedCodomain <- resolveGenericExpression codomain
  pure (FunctionTypeExpression binders resolvedDomain resolvedCodomain)

resolveGenericBinders
  :: [(GenericArgument Expression, GenericBinderId)]
  -> GenericResolution [GenericBinder Expression]
resolveGenericBinders [] = pure []
resolveGenericBinders ((introduction, identity) : remaining) = do
  bound <- resolveGenericExpression (genericArgumentBound introduction)
  let binder = GenericBinder
        { genericBinderId = identity
        , genericBinderArgument = introduction { genericArgumentBound = bound }
        }
  later <- resolveGenericBinders remaining
  pure (binder : later)

resolveOwnedGenericDomain
  :: [(GenericArgument Expression, GenericBinderId)]
  -> Expression
  -> GenericResolution Expression
resolveOwnedGenericDomain declarations expressionValue =
  case expressionValue of
    FunctionTypeExpression {} ->
      resolveGenericExpression expressionValue
    GenericIntroductionExpression introduction ->
      case lookup introduction declarations of
        Nothing -> resolveGenericExpression expressionValue
        Just _ -> do
          bound <- resolveGenericExpression (genericArgumentBound introduction)
          pure (GenericIntroductionExpression
            introduction { genericArgumentBound = bound })
    _ -> traverseExpressionChildren
      (resolveOwnedGenericDomain declarations)
      expressionValue

collectOwnedGenericIntroductions
  :: Expression
  -> [GenericArgument Expression]
collectOwnedGenericIntroductions expressionValue =
  case expressionValue of
    FunctionTypeExpression {} -> []
    GenericIntroductionExpression introduction -> [introduction]
    _ -> concatMap collectOwnedGenericIntroductions
      (expressionChildren expressionValue)

freshGenericBinderId :: GenericResolution GenericBinderId
freshGenericBinderId = do
  next <- get
  put (next + 1)
  pure (GenericBinderId next)

-- Identifier declarations buried in a domain combinator still contribute to
-- that function type's completed scope. An identifier declaration owns its
-- annotation, so names nested inside that annotation are not members of the
-- surrounding scope. Nested function types likewise establish a fresh
-- ownership boundary.
functionTypeIdentifiers :: Expression -> [FunctionTypeIdentifier]
functionTypeIdentifiers expressionValue =
  case expressionValue of
    FunctionTypeExpression {} -> []
    DependentArgument nameExpression _
      | Just name <- literalIdentifierName
          (maybe nameExpression id
            (requiredIdentifierExpression nameExpression)) ->
          [SimpleFunctionTypeIdentifier name]
    dependent@DependentArgument {} ->
      [DependentFunctionTypeIdentifier dependent]
    SyntaxBoundary value -> functionTypeIdentifiers value
    OptionalType value -> functionTypeIdentifiers value
    EitherType left right -> both left right
    AtlasMap entries -> entriesOf entries
    ArgumentativeMap entries -> entriesOf entries
    MapSequence entries -> entriesOf entries
    MapConcatenation left right -> both left right
    MapSpecification _ target -> functionTypeIdentifiers target
    ReverseMapSpecification target _ -> functionTypeIdentifiers target
    Overload defaults supplied -> both defaults supplied
    ReverseOverload supplied defaults -> both defaults supplied
    SafeOverload defaults supplied -> both defaults supplied
    ReverseSafeOverload supplied defaults -> both defaults supplied
    _ -> []
  where
    entriesOf = concatMap functionTypeIdentifiers
    both left right =
      functionTypeIdentifiers left <> functionTypeIdentifiers right

-- | Materialize the domain order consumed by generic-aware matching. The
-- generic introduction remains at its written location while the telescope
-- entries themselves occupy the leading positions.
prepareFunctionDomain
  :: [GenericBinder Expression]
  -> Expression
  -> PreparedFunctionDomain
prepareFunctionDomain generics domain =
  PreparedFunctionDomain kind
    (map PreparedGenericFunctionDomainMember generics
      <> map PreparedOrdinaryFunctionDomainMember suffix)
  where
    (kind, suffix) = layout domain
    layout expressionValue =
      case expressionValue of
        SyntaxBoundary value -> layout value
        AtlasMap entries -> (PreparedOrderedFunctionDomain, entries)
        MapSequence entries -> (PreparedOrderedFunctionDomain, entries)
        ArgumentativeMap entries -> (PreparedArgumentFunctionDomain, entries)
        GenericIntroductionExpression introduction
          | any (sameGenericName introduction) generics ->
              (PreparedScalarFunctionDomain, [])
        _ -> (PreparedScalarFunctionDomain, [expressionValue])
    sameGenericName introduction binder =
      genericArgumentName introduction
        == genericArgumentName (genericBinderArgument binder)

-- | Materialize the identity-based generic telescope as ordinary named prefix
-- slots. The owning telescope retains polarity and identity; the prepared
-- domain needs only the existing identifier-slot representation.
prepareFunctionDomainExpression
  :: [GenericBinder Expression]
  -> Expression
  -> Expression
prepareFunctionDomainExpression generics domain =
  case prepareFunctionDomain generics domain of
    PreparedFunctionDomain kind members ->
      container kind (map lowerMember members)
  where
    container PreparedArgumentFunctionDomain = ArgumentativeMap
    container PreparedOrderedFunctionDomain = AtlasMap
    container PreparedScalarFunctionDomain = AtlasMap
    lowerMember member =
      case member of
        PreparedGenericFunctionDomainMember binder ->
          prepareGenericExpression generics
            (genericArgumentExpression (genericBinderArgument binder))
        PreparedOrdinaryFunctionDomainMember expressionValue ->
          prepareGenericExpression generics expressionValue

-- | Lower declaration markers owned by the supplied telescope to the same
-- ordinary identifier references used everywhere else. Nested function types
-- own their own introductions and are left for their evaluator.
prepareGenericExpression
  :: [GenericBinder Expression]
  -> Expression
  -> Expression
prepareGenericExpression generics = lower
  where
    lower expressionValue =
      case expressionValue of
        FunctionTypeExpression {} -> expressionValue
        GenericIntroductionExpression introduction ->
          case binderName (genericArgumentName introduction) generics of
            Just name -> IdentifierReference name
            Nothing -> expressionValue
        _ -> mapExpressionChildren lower expressionValue
    binderName _ [] = Nothing
    binderName identifier (binder : remaining)
      | genericArgumentName (genericBinderArgument binder) == identifier =
          Just identifier
      | otherwise = binderName identifier remaining

-- | Find the first self or forward reference in an ordered generic telescope.
-- Earlier binders are available lexically; an occurrence of the current or a
-- later local name is an invalid forward dependency rather than an ambient
-- lookup.
forwardGenericBoundReference
  :: [GenericBinder Expression]
  -> Maybe (SimpleIdentifierString, SimpleIdentifierString)
forwardGenericBoundReference = go
  where
    go [] = Nothing
    go remaining@(binder : later) =
      case firstMatchingReference unavailable bound of
        Just referenced -> Just (owner, referenced)
        Nothing -> go later
      where
        argument = genericBinderArgument binder
        owner = genericArgumentName argument
        bound = genericArgumentBound argument
        unavailable = map
          (genericArgumentName . genericBinderArgument)
          remaining
    firstMatchingReference unavailable expressionValue =
      case expressionValue of
        IdentifierReference name
          | name `elem` unavailable -> Just name
        _ -> firstFrom
          (map (firstMatchingReference unavailable)
            (expressionChildren expressionValue))
    firstFrom [] = Nothing
    firstFrom (result : remaining) =
      case result of
        Just value -> Just value
        Nothing -> firstFrom remaining


inferredFunction :: Expression -> Expression -> Expression
inferredFunction body (Fun signature) =
  Fun (FunctionApplication (inferredFunctionSignature signature) body)
inferredFunction body (SyntaxBoundary signature) =
  SyntaxBoundary (inferredFunction body signature)
inferredFunction body signature =
  FunctionApplication (inferredFunctionSignature signature) body

inferredFunctionSignature :: Expression -> Expression
inferredFunctionSignature signature =
  case appliedFunctionType signature of
    Just functionType -> functionType
    Nothing -> FunctionType signature AnyType
  where
    appliedFunctionType functionType@FunctionTypeExpression {} =
      Just functionType
    appliedFunctionType (SyntaxBoundary inner) =
      SyntaxBoundary <$> appliedFunctionType inner
    appliedFunctionType (FunctionApplication function argument) = do
      functionType <- appliedFunctionType function
      pure (applyCodomainArgument functionType argument)
    appliedFunctionType _ = Nothing

    applyCodomainArgument
        (FunctionTypeExpression generics domain codomain) argument =
      FunctionTypeExpression generics domain
        (FunctionApplication codomain argument)
    applyCodomainArgument (SyntaxBoundary inner) argument =
      SyntaxBoundary (applyCodomainArgument inner argument)
    applyCodomainArgument functionType argument =
      FunctionApplication functionType argument



