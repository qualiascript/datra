{-# LANGUAGE GADTs #-}

-- | Internal runtime representation shared by DatraTypes evaluation modules.
-- Constructors stay internal; the public 'DatraTypes' module exposes only the
-- observations and checked operations needed by the AST interpreter.
module Evaluation.Value
  ( ASTMetaCategory (..)
  , BuiltinMetaType (..)
  , CanonicalStringImplementation (..)
  , DatraType
  , DatraTypeFamily (..)
  , structuralDatraType
  , composedStructuralDatraType
  , functionDatraType
  , builtinMetaDatraType
  , totalBlockDatraType
  , datraTypeFamily
  , canonicalStringImplementation
  , PreparedFunctionArgument (..)
  , EvaluatedFunctionInvocation (..)
  , SyntaxFunctionInsertion (..)
  , RuntimeFunctionInsertion (..)
  , EvaluatedFunctionBody (..)
  , functionBodySource
  , EvaluatedFunction (..)
  , ReductionContext (..)
  , functionSyntaxEquivalent
  , makeFunctionValue
  , makeFunctionBodyValue
  , interpretedFunctionBody
  , interpretedRuntimeFunctionInsertion
  , syntaxCategoryTypeValue
  , functionAlternatives
  , isFunctionFamily
  , templateTypeValue
  , syntaxTemplateTypeValue
  , anyTypeValue
  , ordinalTypeValue
  , builtinMetaTypeName
  , builtinMetaTypeCanonicalString
  , naturalRangeTypeValue
  , integerRangeTypeValue
  , naturalValuedRangeTypeValue
  , integerValuedRangeTypeValue
  , functionSignature
  , callableFunction
  , interpretedFunction
  , ExplicitOrigin (..)
  , EvaluatedExplicit (..)
  , RangeAccessPolicy (..)
  , EvaluatedRange (..)
  , EvaluatedNaturalRange (..)
  , EvaluatedValuedNaturalRange (..)
  , EvaluatedIntegerRange (..)
  , EvaluatedValuedIntegerRange (..)
  , EvaluatedEither (..)
  , IdentifierDependency (..)
  , identifierDependencyStringFor
  , identifierDependencyRepresentativeString
  , identifierDependenciesCompatible
  , EvaluatedDependentIdentifierType (..)
  , DependentSumStructure (..)
  , EvaluatedDependentSum (..)
  , InterpretedTotalAtlasMap (..)
  , EvaluatedStringTemplate (..)
  , EvaluatedStringTemplateSegment (..)
  , EvaluatedGreedyStringTemplate (..)
  , EvaluatedAtlasMapFederationMember (..)
  , EvaluatedSpecification (..)
  , ValueForm (..)
  , SomeSuperEllipsisInsertion
  , InsertionCapability (..)
  , OrdinalOrderedValues (..)
  , InterpretedMap (..)
  , interpretedMapCardinality
  , NamedMember (..)
  , NamedMapOrdinalProjection (..)
  , NamedMapProjection (..)
  , NamedMapView (..)
  , namedMapView
  , namedMapOrderType
  , namedMapMemberAt
  , namedMapMemberByName
  , namedMapContainsName
  , namedMapDeclaredMembers
  , namedMapViewForValue
  , appendNamedMapViews
  , namedMapValue
  , interpretedSimpleIdentifierName
  , ToStringInverseDecision (..)
  , ProvenInjectiveToString (..)
  , InterpretedAtlasMapFederationPrimitive (..)
  , InterpretedAtlasMapFederation
  , PresentationDependency (..)
  , IntegerLimit (..)
  , ValueSemantics (..)
  , DynamicScopeLabel (..)
  , ScopeActivation (..)
  , ScopeProtectionPolicy (..)
  , ScopeProtection (..)
  , semanticValueSemantics
  , CanonicalResult (..)
  , InterpretedValue
  , InterpretedValueTotality (..)
  , makeInterpretedValue
  , neverValue
  , interpretedScopeProtection
  , protectInterpretedValue
  , withoutScopeProtection
  , makeSingletonInterpretedValue
  , makeDependentSumValue
  , dependentSumView
  , dependentSumElementType
  , finiteDependentSumElementType
  , finiteDependentSumView
  , withDependentSumView
  , withSpecificationTargetEvidence
  , orderedAtlasMapView
  , withOrderedAtlasMapView
  , withOrderedAtlasMapValues
  , withMapView
  , withDependentSumStructure
  , withDependentSumAccess
  , withDependentSumFamily
  , withDependentSumReservationTarget
  , makeLazyMapValue
  , makeCheckedLazyMapValue
  , interpretedForm
  , interpretedInsertionCapability
  , interpretedMap
  , interpretedAtlasMapFederation
  , interpretedTotalAtlasMap
  , interpretedSemantics
  , interpretedDatraType
  , interpretedValueHasTotalMap
  , interpretedTypeIsTotal
  , interpretedCanonicalResult
  , interpretedSemanticResult
  , interpretedSemanticSemantics
  , withInterpretedSemantics
  , interpretedCanonicalPresentation
  , withCanonicalReference
  , withCanonicalNamedAccess
  , withCanonicalApplication
  , withoutCanonicalPresentation
  , withoutCanonicalDependencies
  , interpretedEvaluationSource
  , withEvaluationSource
  , interpretedValueKind
  , interpretedStringTemplate
  , interpretedGreedyStringTemplate
  , interpretedNamedMapView
  , withNamedMapView
  , withStringTemplatePlan
  , withGreedyStringTemplatePlan
  , interpretedExplicitOrdinal
  , interpretedSpecificationSourceValue
  , interpretedSpecificationTargetEvidence
  , interpretedFederationSpecificationBranches
  , interpretedFederationSpecificationSourceValue
  , interpretedInteger
  , interpretedFormulationLevel
  , interpretedRangeDescription
  , interpretedMapFinalOrderType
  , interpretedMapValueAt
  , interpretedMapValueAtChecked
  , asciiStringFromInterpretedMap
  , explicitOrdinal
  , explicitInsertion
  , rangeDescription
  , evaluatedRangeLevel
  , evaluatedRangeAccessPolicy
  , rangeInsertion
  , naturalRangeAsEvaluatedRange
  , valuedNaturalRangeAsEvaluatedRange
  , valueRanges
  , emptyInterpretedMap
  , singletonMap
  , emptyOrdinalOrderedValues
  , singletonOrdinalOrderedValues
  , appendOrdinalOrderedValues
  , appendSomeSuperEllipsisInsertion
  ) where

import Control.Monad (guard)
import BooleanType (DatraBoolean)
import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (SingletonAtlasMapFederation) )
import Data.Char (chr)
import Data.IORef (IORef)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NonEmpty
import DatraLanguage.SyntaxTemplate
  ( FunctionSyntax (..)
  , SyntaxHoleKind (..)
  , SyntaxPiece (..)
  , SyntaxTemplate (..)
  )
import DatraLanguage.AST (Expression)
import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  , naturalAtOrdinal
  , naturalsBelow
  , ordinalLT
  , subtractOrdinal
  , omega
  )
import FoliageMap (foliageMap, foliageMapPositionAt)
import Evaluation.Error
  ( InterpretedValueKind (..)
  , InterpretingError (..)
  , NamedAccessFailure (..)
  )
import Evaluation.DatraType
import Evaluation.Value.Semantics
import MapOperators.OrderedAtlasMap
  ( OrdinalOrderedValues (..)
  , appendOrdinalOrderedValues
  , emptyOrdinalOrderedValues
  , singletonOrdinalOrderedValues
  )
import Numeric.Natural (Natural)
import NaturalRange qualified
import ValuedNaturalRange qualified
import IntegerRange qualified
import ValuedIntegerRange qualified
import NumericalOperators.NumericalOperand
  ( SomeSuperEllipsis
  , someSuperEllipsisLevel
  )
import SuperEllipsisInsertion
  ( SomeSuperEllipsisInsertion
  , appendSomeSuperEllipsisInsertion
  , eraseSuperEllipsisInsertion
  )
import SuperEllipsisRange qualified as Range
import SuperEllipsisValue
  ( SuperEllipsisValue
  , superEllipsisValueInsertion
  , superEllipsisValueOrdinal
  )

data ExplicitOrigin = NaturalOrigin | ComputedOrigin

data EvaluatedExplicit where
  EvaluatedExplicit
    :: Natural
    -> ExplicitOrigin
    -> SuperEllipsisValue target scope
    -> EvaluatedExplicit

-- | The behavior retained by a range when it is later used as an access
-- selector.  Range values share a normalized insertion representation, but
-- their surface families deliberately do not share access semantics.
data RangeAccessPolicy
  = ClippableConcreteRange
  | ClippableRangeFederation
  | ExactRangeInsertion
  deriving (Eq)

data EvaluatedRange where
  EvaluatedRange
    :: Natural
    -> RangeAccessPolicy
    -> Range.SuperEllipsisRange target scope
    -> EvaluatedRange

data EvaluatedNaturalRange where
  EvaluatedNaturalRange
    :: NaturalRange.NaturalRange rangeScope federationScope
    -> EvaluatedNaturalRange

data EvaluatedValuedNaturalRange where
  EvaluatedValuedNaturalRange
    :: ValuedNaturalRange.ValuedNaturalRange rangeScope federationScope
    -> EvaluatedValuedNaturalRange

data EvaluatedIntegerRange where
  EvaluatedIntegerRange
    :: IntegerRange.IntegerRange rangeScope federationScope
    -> EvaluatedIntegerRange

data EvaluatedValuedIntegerRange where
  EvaluatedValuedIntegerRange
    :: ValuedIntegerRange.ValuedIntegerRange rangeScope federationScope
    -> EvaluatedValuedIntegerRange

-- | A proven-disjoint federation union. The alternatives remain separate so
-- selection can record its route, but that internal route does not make equal
-- or overlapping Atlas maps distinct.
data EvaluatedEither = EvaluatedEither
  { evaluatedEitherLeft :: InterpretedValue
  , evaluatedEitherRight :: InterpretedValue
  }

data EvaluatedDependentIdentifierType = EvaluatedDependentIdentifierType
  { evaluatedIdentifierDependency :: IdentifierDependency
  , evaluatedIdentifierUnderlying :: InterpretedValue
  , evaluatedIdentifierNameFederation :: Maybe InterpretedValue
  , evaluatedIdentifierNameFamily :: Maybe
      (InterpretedValue -> Either InterpretingError InterpretedValue)
  }

-- | Structural provenance that remains meaningful after a source-level
-- declaration has been evaluated.  This records constructors recognized by
-- their ordinary expression shape; it does not retain or inspect a binding
-- name from the standard library.
data DependentSumStructure
  = OrdinaryDependentSum
  | CharacterDependentSum
  | ListDependentSum InterpretedValue
  | StreamDependentSum InterpretedValue

-- | A dependent sum keeps its ordinary structural approximation for map
-- operations and its exact left-to-right membership procedure for typing.
data EvaluatedDependentSum = EvaluatedDependentSum
  { evaluatedDependentSumStaticTarget :: InterpretedValue
  , evaluatedDependentSumSpecify
      :: InterpretedValue -> Either InterpretingError InterpretedValue
  , evaluatedDependentSumAccess
      :: Maybe
          (InterpretedValue -> Either InterpretingError InterpretedValue)
  , evaluatedDependentSumDomain :: Maybe InterpretedValue
  , evaluatedDependentSumFibreAt
      :: Maybe
          (InterpretedValue -> Either InterpretingError InterpretedValue)
  , evaluatedDependentSumReservationTarget :: Maybe InterpretedValue
  , evaluatedDependentSumStructure :: DependentSumStructure
  }

-- | Runtime erasure of the proof-bearing 'TotalAtlasMap'.  This certificate
-- is attached only by constructors known to give every final-page region a
-- singleton value; being a singleton federation is not sufficient by itself.
newtype InterpretedTotalAtlasMap = InterpretedTotalAtlasMap
  { interpretedTotalAtlasMapUnderlying :: InterpretedMap
  }

-- | The selected member stays tagged by federation family. Primitive range
-- members remain distinct even when they carry the same natural; a singleton
-- federation records the canonical identity of its sole total-map member.
data EvaluatedAtlasMapFederationMember
  = EvaluatedNaturalRangeMember NaturalRange.NaturalSubrangeDescription
  | EvaluatedValuedNaturalRangeMember Natural
  | EvaluatedIntegerRangeMember IntegerRange.IntegerSubrangeDescription
  | EvaluatedValuedIntegerRangeMember Integer
  | EvaluatedAsciiStringMember String
  | EvaluatedEitherMember
      DatraBoolean
      EvaluatedAtlasMapFederationMember
  | EvaluatedArgumentMapMember
      InterpretedValue
      EvaluatedAtlasMapFederationMember
  | EvaluatedDependentIdentifierTypeMember
      (Maybe EvaluatedAtlasMapFederationMember)
      EvaluatedAtlasMapFederationMember
  | EvaluatedDependentSumMember InterpretedValue
  | EvaluatedToStringMember
      InterpretedValue
      EvaluatedAtlasMapFederationMember
  | EvaluatedCanonicalTypeMember CanonicalResult
  | EvaluatedSingletonAtlasMapMember CanonicalResult
  | EvaluatedSequentialAtlasMapMember [EvaluatedAtlasMapFederationMember]
  | EvaluatedExpansionAtlasMapMember
      EvaluatedAtlasMapFederationMember
      EvaluatedAtlasMapFederationMember
  | EvaluatedConcatenatedAtlasMapMember [EvaluatedAtlasMapFederationMember]

-- | Erased semantic witness for a successful specification.  The core
-- 'SpecificationOperator' module carries the non-erased categorical form used
-- when concrete Atlas witnesses remain available.
data EvaluatedSpecification = EvaluatedSpecification
  { evaluatedSpecificationSourceValue :: InterpretedValue
  , evaluatedSpecificationSource :: InterpretedTotalAtlasMap
  , evaluatedSpecificationTarget :: InterpretedValue
  , evaluatedSpecificationMember :: EvaluatedAtlasMapFederationMember
  }

data PreparedFunctionArgument = PreparedFunctionArgument
  { functionSuppliedArgument :: InterpretedValue
  , functionPreparedArgument :: InterpretedValue
  , functionPreparedBindings :: [(String, InterpretedValue)]
  }

-- | The value produced by one invocation and the checked semantic contract
-- which governed that result.  Generic functions may evaluate their codomain
-- per call, so this cannot in general be recovered from the function's static
-- summary after invocation has completed.
data EvaluatedFunctionInvocation = EvaluatedFunctionInvocation
  { functionInvocationValue :: InterpretedValue
  , functionInvocationContract :: Maybe InterpretedValue
  }

data SyntaxFunctionInsertion = SyntaxFunctionInsertion
  { applySyntaxFunction :: [Expression] -> Maybe Expression
  , preimageSyntaxFunction :: Expression -> Maybe [Expression]
  }

-- | An executable runtime function together with a partial left inverse.
-- The shared forward map keeps the injectivity witness attached to the exact
-- operation used for invocation.
data RuntimeFunctionInsertion = RuntimeFunctionInsertion
  { applyRuntimeFunction
      :: InterpretedValue
      -> Either InterpretingError InterpretedValue
  , preimageRuntimeFunction
      :: InterpretedValue
      -> Maybe InterpretedValue
  }

data EvaluatedFunctionBody
  = EvaluatedSyntaxFunctionBody
      String
      SyntaxFunctionInsertion
  | EvaluatedRuntimeFunctionBody String EvaluatedFunction

data EvaluatedFunction = EvaluatedFunction
  { functionDomain :: InterpretedValue
  , functionCodomain :: InterpretedValue
  , functionSyntax :: Maybe (FunctionSyntax InterpretedValue)
  , functionSyntaxSource :: Maybe (FunctionSyntax String)
  , functionSource :: Maybe String
  , functionBody :: Maybe EvaluatedFunctionBody
  , functionSignatureSource :: String
  , functionPrepare :: Maybe
      (InterpretedValue -> Either InterpretingError PreparedFunctionArgument)
  , functionInvoke :: Maybe
      (ScopeActivation
        -> ReductionContext
        -> PreparedFunctionArgument
        -> Either InterpretingError EvaluatedFunctionInvocation)
  , functionValidatesResult :: Bool
  , functionInsertion :: Maybe RuntimeFunctionInsertion
  }

-- | Ordinary evaluation is unrestricted. Shadowing consistency is established
-- with finite reduction fuel so a divergent proposed binding is rejected
-- instead of preventing the surrounding scope from being evaluated.
data ReductionContext
  = UnrestrictedReduction
  | ShadowingConsistencyReduction String Int
  deriving (Eq, Show)

functionSyntaxEquivalent
  :: FunctionSyntax InterpretedValue
  -> FunctionSyntax InterpretedValue
  -> Bool
functionSyntaxEquivalent left right =
  let leftTemplates = functionSyntaxTemplates left
      rightTemplates = functionSyntaxTemplates right
  in length leftTemplates == length rightTemplates
    && and (zipWith templateEquivalent leftTemplates rightTemplates)
  where
    templateEquivalent
        (SyntaxTemplate leftPieces) (SyntaxTemplate rightPieces) =
      length leftPieces == length rightPieces
        && and (zipWith pieceEquivalent leftPieces rightPieces)
    pieceEquivalent
        (SyntaxLiteral leftLiteral) (SyntaxLiteral rightLiteral) =
      leftLiteral == rightLiteral
    pieceEquivalent
        (SyntaxHole leftHole) (SyntaxHole rightHole) =
      holeEquivalent leftHole rightHole
    pieceEquivalent _ _ = False
    holeEquivalent
        (ExpressionSyntaxHole leftValue)
        (ExpressionSyntaxHole rightValue) = equivalent leftValue rightValue
    holeEquivalent
        (BlockSyntaxHole leftValue)
        (BlockSyntaxHole rightValue) = equivalent leftValue rightValue
    holeEquivalent
        (FunctionBodySyntaxHole leftValue)
        (FunctionBodySyntaxHole rightValue) = equivalent leftValue rightValue
    holeEquivalent
        (DeclarationSyntaxHole leftValue)
        (DeclarationSyntaxHole rightValue) = equivalent leftValue rightValue
    holeEquivalent
        (DependentIdentifierSyntaxHole leftValue)
        (DependentIdentifierSyntaxHole rightValue) =
          equivalent leftValue rightValue
    holeEquivalent
        (ValueSyntaxHole leftValue) (ValueSyntaxHole rightValue) =
      equivalent leftValue rightValue
    holeEquivalent _ _ = False
    equivalent leftValue rightValue =
      interpretedSemanticResult leftValue
        == interpretedSemanticResult rightValue

makeFunctionValue :: EvaluatedFunction -> InterpretedValue
makeFunctionValue function = makeInterpretedValue functionDatraType
  (FunctionForm function) NoInsertion emptyInterpretedMap
  (SingletonAtlasMapFederation emptyInterpretedMap) NonTotalInterpretedMap
  (FunctionSemantics (interpretedSemantics (functionDomain function))
    (interpretedSemantics (functionCodomain function))
    (Just canonicalSource))
  where
    signature = functionSignatureSource function
    canonicalSource = maybe signature id (functionSource function)

makeFunctionBodyValue :: EvaluatedFunctionBody -> InterpretedValue
makeFunctionBodyValue body = case body of
  EvaluatedSyntaxFunctionBody {} -> bodyValue (FunctionBodyForm body)
  EvaluatedRuntimeFunctionBody _ implementation ->
    bodyValue (FunctionForm implementation)
  where
    bodyValue form = makeInterpretedValue
      (builtinMetaDatraType (ASTMetaType FunctionBodyAST))
      form
      NoInsertion
      emptyInterpretedMap
      (SingletonAtlasMapFederation emptyInterpretedMap)
      TotalInterpretedMap
      (FunctionBodySemantics (functionBodySource body))

functionBodySource :: EvaluatedFunctionBody -> String
functionBodySource body = case body of
  EvaluatedSyntaxFunctionBody source _ -> source
  EvaluatedRuntimeFunctionBody source _ -> source

interpretedFunctionBody :: InterpretedValue -> Maybe EvaluatedFunctionBody
interpretedFunctionBody value = case interpretedForm value of
  FunctionBodyForm body -> Just body
  FunctionForm function -> case datraTypeFamily
      (interpretedDatraType value) of
    BuiltinMetaTypeFamily (ASTMetaType FunctionBodyAST) ->
      Just (EvaluatedRuntimeFunctionBody source function)
    _ -> Nothing
    where
      source = case functionSource function of
        Just implementationSource -> implementationSource
        Nothing -> functionSignatureSource function
  DependentIdentifierTypeForm identifier ->
    interpretedFunctionBody (evaluatedIdentifierUnderlying identifier)
  AssignmentForm specification ->
    interpretedFunctionBody (evaluatedSpecificationSourceValue specification)
  SpecificationForm specification ->
    interpretedFunctionBody (evaluatedSpecificationSourceValue specification)
  _ -> Nothing

-- | Recover the executable insertion evidence attached either directly to a
-- function or through its runtime body. Typed wrappers deliberately keep the
-- body separate from the signature, so consumers must inspect both layers.
interpretedRuntimeFunctionInsertion
  :: InterpretedValue
  -> Maybe RuntimeFunctionInsertion
interpretedRuntimeFunctionInsertion value =
  case interpretedFunction value >>= functionInsertionFrom of
    Just insertion -> Just insertion
    Nothing -> interpretedFunctionBody value >>= bodyInsertion
  where
    bodyInsertion body = case body of
      EvaluatedRuntimeFunctionBody _ function -> functionInsertionFrom function
      EvaluatedSyntaxFunctionBody {} -> Nothing
    functionInsertionFrom function =
      case functionInsertion function of
        Just insertion -> Just insertion
        Nothing -> functionBody function >>= bodyInsertion

interpretedFunction :: InterpretedValue -> Maybe EvaluatedFunction
interpretedFunction value = case interpretedForm value of
  FunctionForm function -> Just function
  _ -> Nothing

callableFunction :: InterpretedValue -> Maybe EvaluatedFunction
callableFunction value = case interpretedForm value of
  DependentIdentifierTypeForm identifier -> callableFunction (evaluatedIdentifierUnderlying identifier)
  AssignmentForm specification -> callableFunction (evaluatedSpecificationSourceValue specification)
  SpecificationForm specification -> callableFunction (evaluatedSpecificationSourceValue specification)
  _ -> interpretedFunction value

functionSignature :: InterpretedValue -> Maybe (InterpretedValue, InterpretedValue)
functionSignature value = (\function -> (functionDomain function, functionCodomain function)) <$> callableFunction value

functionAlternatives :: InterpretedValue -> [EvaluatedFunction]
functionAlternatives value = case interpretedForm value of
  EitherForm alternatives -> functionAlternatives (evaluatedEitherLeft alternatives) <> functionAlternatives (evaluatedEitherRight alternatives)
  DependentIdentifierTypeForm identifier -> functionAlternatives (evaluatedIdentifierUnderlying identifier)
  AssignmentForm specification -> functionAlternatives (evaluatedSpecificationSourceValue specification)
  SpecificationForm specification -> functionAlternatives (evaluatedSpecificationSourceValue specification)
  FunctionForm function -> [function]
  _ -> []

-- | True only when every branch of the value is callable.  Merely finding a
-- function somewhere inside an Either is not enough: mixed federations still
-- use ordinary structural specification and subfederation rules.
isFunctionFamily :: InterpretedValue -> Bool
isFunctionFamily value =
  case interpretedForm value of
    EitherForm alternatives ->
      isFunctionFamily (evaluatedEitherLeft alternatives)
        && isFunctionFamily (evaluatedEitherRight alternatives)
    DependentIdentifierTypeForm identifier ->
      isFunctionFamily (evaluatedIdentifierUnderlying identifier)
    AssignmentForm specification ->
      isFunctionFamily (evaluatedSpecificationSourceValue specification)
    SpecificationForm specification ->
      isFunctionFamily (evaluatedSpecificationSourceValue specification)
    FunctionForm _ -> True
    _ -> False

builtinMetaTypeName :: BuiltinMetaType -> String
builtinMetaTypeName AnyMetaType = "Any"
builtinMetaTypeName OrdinalMetaType = "Ordinal"
builtinMetaTypeName (ASTMetaType category) = case category of
  ExpressionAST -> "Expr"
  BlockAST -> "Block"
  FunctionBodyAST -> "FunctionBody"
  DeclarationAST -> "DependentDeclaration"
  DependentIdentifierAST -> "DependentIdentifier"
builtinMetaTypeName NatRangeMetaType = "NatRange"
builtinMetaTypeName IntRangeMetaType = "IntRange"
builtinMetaTypeName NatValRangeMetaType = "NatValRange"
builtinMetaTypeName IntValRangeMetaType = "IntValRange"
builtinMetaTypeName TemplateMetaType = "Template"
builtinMetaTypeName SyntaxTemplateMetaType = "_SyntaxTemplate"

builtinMetaTypeCanonicalString :: BuiltinMetaType -> String
builtinMetaTypeCanonicalString (ASTMetaType category) = case category of
  ExpressionAST -> "'datra.Expr"
  BlockAST -> "'datra.Block"
  FunctionBodyAST -> "'datra.FunctionBody"
  DeclarationAST -> "'datra.DependentDeclaration"
  DependentIdentifierAST -> "'datra.DependentIdentifier"
builtinMetaTypeCanonicalString SyntaxTemplateMetaType =
  "'datra.SyntaxTemplate"
builtinMetaTypeCanonicalString kind = builtinMetaTypeName kind

builtinMetaTypeValue :: BuiltinMetaType -> InterpretedValue
builtinMetaTypeValue kind = makeInterpretedValue
  (builtinMetaDatraType kind)
  (BuiltinMetaTypeForm kind) NoInsertion emptyInterpretedMap
  (SingletonAtlasMapFederation emptyInterpretedMap) NonTotalInterpretedMap (BuiltinMetaTypeSemantics kind)

anyTypeValue, ordinalTypeValue, naturalRangeTypeValue, integerRangeTypeValue,
  naturalValuedRangeTypeValue, integerValuedRangeTypeValue,
  templateTypeValue, syntaxTemplateTypeValue :: InterpretedValue
anyTypeValue = builtinMetaTypeValue AnyMetaType
ordinalTypeValue = builtinMetaTypeValue OrdinalMetaType
naturalRangeTypeValue = builtinMetaTypeValue NatRangeMetaType
integerRangeTypeValue = builtinMetaTypeValue IntRangeMetaType
naturalValuedRangeTypeValue = builtinMetaTypeValue NatValRangeMetaType
integerValuedRangeTypeValue = builtinMetaTypeValue IntValRangeMetaType
templateTypeValue = builtinMetaTypeValue TemplateMetaType
syntaxTemplateTypeValue = builtinMetaTypeValue SyntaxTemplateMetaType

syntaxCategoryTypeValue :: ASTMetaCategory -> InterpretedValue
syntaxCategoryTypeValue = builtinMetaTypeValue . ASTMetaType

data ValueForm
  = NeverForm
  | BuiltinMetaTypeForm BuiltinMetaType
  | FunctionBodyForm EvaluatedFunctionBody
  | FunctionForm EvaluatedFunction
  | ExplicitForm EvaluatedExplicit
  | IntegerForm Integer
  | BooleanForm DatraBoolean
  | NothingForm
  | FormulationForm SomeSuperEllipsis
  | RangeForm EvaluatedRange
  | NaturalRangeForm EvaluatedNaturalRange
  | ValuedNaturalRangeForm EvaluatedValuedNaturalRange
  | IntegerRangeForm EvaluatedIntegerRange
  | ValuedIntegerRangeForm EvaluatedValuedIntegerRange
  | EitherForm EvaluatedEither
  | ArgumentMapForm [InterpretedValue] InterpretedValue
  | SkipForm InterpretedValue
  | FederationSpecificationForm
      InterpretedValue InterpretedValue [InterpretedValue]
  | RangeConcatenationForm
      [EvaluatedRange]
      (Maybe (InterpretedValue, InterpretedValue))
  | AsciiStringForm String
  | IdentifierValueTypeForm
  | ToStringForm
  | TemplateForm InterpretedValue
  | SpecificationForm EvaluatedSpecification
  | AssignmentForm EvaluatedSpecification
  | DependentIdentifierTypeForm EvaluatedDependentIdentifierType
  | IdentifierStringProjectionForm EvaluatedDependentIdentifierType
  | DependentSumForm EvaluatedDependentSum
  | CoalizationForm InterpretedValue
  | SequentialMapForm
  | ExpansionMapForm InterpretedValue InterpretedValue
  | ConcatenatedMapForm InterpretedValue InterpretedValue
  | MapForm

data InsertionCapability
  = NoInsertion
  | ValidInsertion SomeSuperEllipsisInsertion
  | RejectedInsertion Range.SuperEllipsisRangeConcatError

data InterpretedMap = InterpretedMap
  { interpretedMapPageCardinality :: Natural
  , interpretedMapFinalValues :: OrdinalOrderedValues InterpretedValue
  , interpretedMapCheckedValueAt
      :: Ordinal -> Either InterpretingError (Maybe InterpretedValue)
  , interpretedMapComponents :: [ValueSemantics]
  }

-- | One materialized member of a named namespace. Visibility and canonical
-- declaration status belong to the member rather than being rediscovered by
-- inspecting its rendered value.
data NamedMember = NamedMember
  { namedMemberName :: String
  , namedMemberValue :: InterpretedValue
  }

-- | A namespace-preserving view of an Atlas map. Ordinal access retains the
-- map's own order; direct name lookup must decide absence without enumerating
-- that order. The finite declaration manifest is metadata for syntax and
-- module interfaces, not a substitute for enumerating the value namespace.
data NamedMapOrdinalProjection = NamedMapOrdinalProjection
  { namedOrdinalProjectionOrderType :: Ordinal
  , namedOrdinalProjectionMemberAt
      :: Ordinal -> Either InterpretingError (Maybe NamedMember)
  }

-- | Direct name projection is available independently of ordinal traversal.
-- Some namespaces, notably syntax-category declaration families, can decode a
-- concrete name without possessing a canonical enumeration of every name.
data NamedMapProjection = NamedMapProjection
  { namedProjectionCollection
      :: Either InterpretingError NamedMapOrdinalProjection
  , namedProjectionOrdinal
      :: Either InterpretingError NamedMapOrdinalProjection
  , namedProjectionMemberByName
      :: String -> Either InterpretingError (Maybe NamedMember)
  , namedProjectionContainsName
      :: String -> Either InterpretingError Bool
  -- The manifest may materialize representative declarations. Keep it
  -- explicitly delayed so composing namespace views cannot evaluate those
  -- declarations while the surrounding recursive scope is still forming.
  , namedProjectionDeclaredMembers
      :: () -> Either InterpretingError [NamedMember]
  }

newtype NamedMapView = NamedMapView
  { namedMapProjection :: NamedMapProjection
  }

-- | Recover a simple declaration name from its identifier value. The name is
-- already represented by the first slot, so lookup does not need a parallel
-- metadata record.
interpretedSimpleIdentifierName :: InterpretedValue -> Maybe String
interpretedSimpleIdentifierName value =
  case interpretedForm value of
    DependentIdentifierTypeForm identifier -> dependencyName identifier
    IdentifierStringProjectionForm identifier -> dependencyName identifier
    AssignmentForm specification ->
      interpretedSimpleIdentifierName (evaluatedSpecificationTarget specification)
    SpecificationForm specification ->
      interpretedSimpleIdentifierName (evaluatedSpecificationTarget specification)
    _ -> semanticName (interpretedSemantics value)
  where
    dependencyName identifier =
      case evaluatedIdentifierDependency identifier of
        SimpleIdentifierDependency name -> Just name
        DependentIdentifierDependency {} -> Nothing
    semanticName semantics = case semantics of
      PresentedSemantics _ _ underlying -> semanticName underlying
      AssignmentSemantics name _ _ -> Just name
      DependentIdentifierTypeSemantics
          (SimpleIdentifierDependency name) _ _ _ -> Just name
      _ -> Nothing

namedMapView
  :: Ordinal
  -> (Ordinal -> Either InterpretingError (Maybe NamedMember))
  -> (String -> Either InterpretingError (Maybe NamedMember))
  -> (String -> Either InterpretingError Bool)
  -> NamedMapView
namedMapView orderType memberAt memberByName containsName =
  NamedMapView (NamedMapProjection
    (Right ordinalProjection)
    (Right (NamedMapOrdinalProjection orderType memberAt))
    memberByName
    containsName
    (const (Right [])))
  where
    ordinalProjection = NamedMapOrdinalProjection orderType memberAt

namedMapOrderType :: NamedMapView -> Either InterpretingError Ordinal
namedMapOrderType view = namedOrdinalProjectionOrderType
  <$> namedProjectionCollection (namedMapProjection view)

namedMapMemberAt
  :: NamedMapView
  -> Ordinal
  -> Either InterpretingError (Maybe NamedMember)
namedMapMemberAt view position = do
  ordinalProjection <- namedProjectionCollection (namedMapProjection view)
  namedOrdinalProjectionMemberAt ordinalProjection position

namedMapMemberByName
  :: NamedMapView
  -> String
  -> Either InterpretingError (Maybe NamedMember)
namedMapMemberByName = namedProjectionMemberByName . namedMapProjection

namedMapContainsName
  :: NamedMapView
  -> String
  -> Either InterpretingError Bool
namedMapContainsName = namedProjectionContainsName . namedMapProjection

namedMapDeclaredMembers
  :: NamedMapView
  -> Either InterpretingError [NamedMember]
namedMapDeclaredMembers view =
  namedProjectionDeclaredMembers (namedMapProjection view) ()

namedMapViewForValue :: InterpretedValue -> Maybe NamedMapView
namedMapViewForValue value =
  case interpretedSimpleIdentifierName value of
    Just name -> Just (NamedMapView (NamedMapProjection
      (Right singletonProjection)
      (Right (NamedMapOrdinalProjection
        (finiteOrdinal 1)
        (\position -> Right
          (if position == finiteOrdinal 0 then Just member else Nothing))))
      (\candidate -> Right
        (if candidate == name then Just member else Nothing))
      (\candidate -> Right (candidate == name))
      (const (Right [member]))))
      where
        member = NamedMember name value
        singletonProjection = NamedMapOrdinalProjection
          (finiteOrdinal 1)
          (\position -> Right
            (if position == finiteOrdinal 0 then Just member else Nothing))
    Nothing -> interpretedNamedMapView value

appendNamedMapViews :: NamedMapView -> NamedMapView -> NamedMapView
appendNamedMapViews left right = NamedMapView (appendNamedMapProjections
  (namedMapProjection left)
  (namedMapProjection right))

appendNamedMapProjections
  :: NamedMapProjection
  -> NamedMapProjection
  -> NamedMapProjection
appendNamedMapProjections left right = NamedMapProjection
  (appendOrdinalProjections
    <$> namedProjectionCollection left
    <*> namedProjectionCollection right)
  (appendOrdinalProjections
    <$> namedProjectionOrdinal left
    <*> namedProjectionOrdinal right)
  memberByName
  (\name -> (||)
    <$> namedProjectionContainsName left name
    <*> namedProjectionContainsName right name)
  (\() -> (<>)
    <$> namedProjectionDeclaredMembers left ()
    <*> namedProjectionDeclaredMembers right ())
  where
    appendOrdinalProjections leftOrdinal rightOrdinal =
      NamedMapOrdinalProjection
        (addOrdinals leftOrder
          (namedOrdinalProjectionOrderType rightOrdinal))
        memberAt
      where
        leftOrder = namedOrdinalProjectionOrderType leftOrdinal
        memberAt position
          | position `ordinalLT` leftOrder =
              namedOrdinalProjectionMemberAt leftOrdinal position
          | otherwise = case subtractOrdinal leftOrder position of
              Just relative ->
                namedOrdinalProjectionMemberAt rightOrdinal relative
              Nothing -> Right Nothing
    memberByName name = do
      leftMember <- namedProjectionMemberByName left name
      rightMember <- namedProjectionMemberByName right name
      case (leftMember, rightMember) of
        (Nothing, member) -> Right member
        (member, Nothing) -> Right member
        (Just _, Just _) ->
          Left (NamedAccessFailed (NamedFieldAmbiguous name))

-- | Materialize only the ordinary Atlas-map shell of a named namespace. Each
-- ordinal demand delegates to the producer and retains its checked failure.
namedMapValue :: NamedMapView -> Either InterpretingError InterpretedValue
namedMapValue view = do
  collection <- namedProjectionCollection (namedMapProjection view)
  let normalizedCollection = foliageOrdinalProjection collection
      normalizedView = NamedMapView ((namedMapProjection view)
        { namedProjectionCollection = Right normalizedCollection })
      shellOrderType = namedOrdinalProjectionOrderType normalizedCollection
  pure (withNamedMapView normalizedView
    (makeCheckedLazyMapValue
      shellOrderType
      (fmap (fmap namedMemberValue)
        . namedOrdinalProjectionMemberAt normalizedCollection)))

-- | Collections use natural positions even when their source namespace is a
-- transfinite ordinal sum. The ordinal projection remains available for
-- callers that need the source order; the ordinary Atlas shell follows the
-- same fair foliage traversal used by generic map views.
foliageOrdinalProjection
  :: NamedMapOrdinalProjection
  -> NamedMapOrdinalProjection
foliageOrdinalProjection source =
  case naturalAtOrdinal sourceOrder of
    Just _ -> source
    Nothing -> NamedMapOrdinalProjection omega memberAt
  where
    sourceOrder = namedOrdinalProjectionOrderType source
    traversal = foliageMap sourceOrder
    memberAt position = case naturalAtOrdinal position of
      Nothing -> Right Nothing
      Just rank -> case foliageMapPositionAt traversal rank of
        Just sourcePosition ->
          namedOrdinalProjectionMemberAt source sourcePosition
        Nothing -> Right Nothing

-- | Compatibility name for the number of Atlas pages represented by a map.
-- This is distinct from the final page's possibly-transfinite order type.
interpretedMapCardinality :: InterpretedMap -> Natural
interpretedMapCardinality = interpretedMapPageCardinality

-- | The evaluated, non-total holes retained by a string template. Total
-- interpolations are folded into adjacent literal chunks before this plan is
-- attached, so every capture here participates in lookup enumeration.
data EvaluatedStringTemplate = EvaluatedStringTemplate
  { evaluatedStringTemplateSegments :: [EvaluatedStringTemplateSegment]
  }

data EvaluatedStringTemplateSegment
  = EvaluatedStringTemplateLiteral String
  | EvaluatedStringTemplateCapture
      Natural
      InterpretedValue
      InterpretedValue

newtype EvaluatedGreedyStringTemplate = EvaluatedGreedyStringTemplate
  { evaluatedGreedyStringTemplateOperand :: Expression
  }

-- | The partial inverse carried by a proven pointwise string conversion.
data ToStringInverseDecision
  = ToStringInverseMatched [InterpretedValue]
  | ToStringInverseRejected

data ProvenInjectiveToString = ProvenInjectiveToString
  { injectiveToStringCharacterAlphabet :: Maybe String
  , injectiveToStringExactStrings :: Maybe [String]
  , injectiveToStringExcludesSubstring :: String -> Bool
  , invertInjectiveToString :: String -> ToStringInverseDecision
  }

-- | Primitive Atlas-map federation kinds understood by the interpreter.
-- The injective string primitive carries the language facts and inverse that
-- justified its construction.
data InterpretedAtlasMapFederationPrimitive
  = NaturalRangeAtlasMapFederation EvaluatedNaturalRange
  | ValuedNaturalRangeAtlasMapFederation EvaluatedValuedNaturalRange
  | IntegerRangeAtlasMapFederation EvaluatedIntegerRange
  | ValuedIntegerRangeAtlasMapFederation EvaluatedValuedIntegerRange
  | EitherAtlasMapFederation EvaluatedEither
  | DependentIdentifierTypeAtlasMapFederation EvaluatedDependentIdentifierType
  | IdentifierStringProjectionAtlasMapFederation EvaluatedDependentIdentifierType
  | IdentifierValueTypeAtlasMapFederation
  | ToStringAtlasMapFederation
      InterpretedValue
      ProvenInjectiveToString

type InterpretedAtlasMapFederation =
  AtlasMapFederationExpression
    InterpretedAtlasMapFederationPrimitive
    InterpretedMap

data InterpretedValue = InterpretedValue
  { interpretedDatraType :: DatraType
  , interpretedForm :: ValueForm
  , interpretedInsertionCapability :: InsertionCapability
  , interpretedMap :: InterpretedMap
  , interpretedAtlasMapFederation :: InterpretedAtlasMapFederation
  , interpretedTotalAtlasMap :: Maybe InterpretedTotalAtlasMap
  , interpretedSemantics :: ValueSemantics
  , interpretedEvaluationSource :: Maybe String
  , interpretedScopeProtection :: Maybe ScopeProtection
  , interpretedDependentSumView :: Maybe EvaluatedDependentSum
  , interpretedSpecificationTargetEvidence :: Maybe InterpretedValue
  , interpretedOrderedAtlasMapView
      :: Maybe (OrdinalOrderedValues InterpretedValue)
  , interpretedStringTemplate :: Maybe EvaluatedStringTemplate
  , interpretedGreedyStringTemplate :: Maybe EvaluatedGreedyStringTemplate
  , interpretedNamedMapView :: Maybe NamedMapView
  }

newtype DynamicScopeLabel = DynamicScopeLabel Natural
  deriving (Eq, Ord, Show)

-- | Runtime identity for one active lexical-scope chain.  The supply belongs
-- to the complete evaluation; the labels are obtained from the active scope
-- ancestry rather than from a separate protection-only stack.
data ScopeActivation = ScopeActivation
  { scopeActivationLabelSupply :: IORef Natural
  , scopeActivationLabel :: DynamicScopeLabel
  , scopeActivationParent :: Maybe ScopeActivation
  }

data ScopeProtectionPolicy
  = GenericExistentialProtection
  deriving (Eq, Ord, Show)

data ScopeProtection = ScopeProtection
  { scopeProtectionLabel :: DynamicScopeLabel
  , scopeProtectionPolicies :: NonEmpty ScopeProtectionPolicy
  }
  deriving (Eq, Show)

data InterpretedValueTotality = TotalInterpretedMap | NonTotalInterpretedMap

makeInterpretedValue
  :: DatraType
  -> ValueForm
  -> InsertionCapability
  -> InterpretedMap
  -> InterpretedAtlasMapFederation
  -> InterpretedValueTotality
  -> ValueSemantics
  -> InterpretedValue
makeInterpretedValue datraType form capability valueMap federation totality semantics =
  InterpretedValue
    { interpretedDatraType = datraType
    , interpretedForm = form
    , interpretedInsertionCapability = capability
    , interpretedMap = valueMap
    , interpretedAtlasMapFederation = federation
    , interpretedTotalAtlasMap =
        case totality of
          TotalInterpretedMap -> Just (InterpretedTotalAtlasMap valueMap)
          NonTotalInterpretedMap -> Nothing
    , interpretedSemantics = semantics
    , interpretedEvaluationSource = Nothing
    , interpretedScopeProtection = Nothing
    , interpretedDependentSumView = Nothing
    , interpretedSpecificationTargetEvidence = Nothing
    , interpretedOrderedAtlasMapView = Nothing
    , interpretedStringTemplate = Nothing
    , interpretedGreedyStringTemplate = Nothing
    , interpretedNamedMapView = Nothing
    }

withNamedMapView :: NamedMapView -> InterpretedValue -> InterpretedValue
withNamedMapView view value = value { interpretedNamedMapView = Just view }

withStringTemplatePlan
  :: EvaluatedStringTemplate
  -> InterpretedValue
  -> InterpretedValue
withStringTemplatePlan plan value =
  value { interpretedStringTemplate = Just plan }

withGreedyStringTemplatePlan
  :: EvaluatedGreedyStringTemplate
  -> InterpretedValue
  -> InterpretedValue
withGreedyStringTemplatePlan plan value =
  value { interpretedGreedyStringTemplate = Just plan }

neverValue :: InterpretedValue
neverValue =
  makeInterpretedValue
    structuralDatraType
    NeverForm
    NoInsertion
    emptyInterpretedMap
    (SingletonAtlasMapFederation emptyInterpretedMap)
    NonTotalInterpretedMap
    NeverSemantics

protectInterpretedValue
  :: DynamicScopeLabel
  -> NonEmpty ScopeProtectionPolicy
  -> InterpretedValue
  -> InterpretedValue
protectInterpretedValue label policies value = value
  { interpretedScopeProtection = Just
      (ScopeProtection label (normalizePolicies policies))
  }
  where
    normalizePolicies (first NonEmpty.:| remaining) =
      first NonEmpty.:| foldr add [] remaining
      where
        add policy accumulated
          | policy == first || policy `elem` accumulated = accumulated
          | otherwise = policy : accumulated

withoutScopeProtection :: InterpretedValue -> InterpretedValue
withoutScopeProtection value = value { interpretedScopeProtection = Nothing }

makeSingletonInterpretedValue
  :: DatraType
  -> ValueForm
  -> InsertionCapability
  -> InterpretedMap
  -> InterpretedValueTotality
  -> ValueSemantics
  -> InterpretedValue
makeSingletonInterpretedValue datraType form capability valueMap totality =
  withOrderedAtlasMapValues (interpretedMapFinalValues valueMap)
    . makeInterpretedValue
      datraType
      form
      capability
      valueMap
      (SingletonAtlasMapFederation valueMap)
      totality

makeDependentSumValue
  :: String
  -> InterpretedValue
  -> (InterpretedValue -> Either InterpretingError InterpretedValue)
  -> InterpretedValue
makeDependentSumValue source staticTarget specify =
  makeInterpretedValue
    structuralDatraType
    (DependentSumForm
      (EvaluatedDependentSum
        staticTarget specify Nothing Nothing Nothing Nothing OrdinaryDependentSum))
    (interpretedInsertionCapability staticTarget)
    (interpretedMap staticTarget)
    (interpretedAtlasMapFederation staticTarget)
    NonTotalInterpretedMap
    (DependentSumSemantics source)

-- | Observe the existential capability of a value independently of its
-- primary runtime form. Ordinary dependent sums carry the capability in their
-- form; generic functions attach the same capability while remaining
-- callable and canonically rendered as functions.
dependentSumView :: InterpretedValue -> Maybe EvaluatedDependentSum
dependentSumView value =
  case interpretedForm value of
    DependentSumForm dependent -> Just dependent
    _ -> interpretedDependentSumView value

-- | Recover the common member type of a homogeneous dependent-sum family.
-- This is deliberately phrased in terms of the semantic dependent-sum
-- capability: callers do not need to know whether the family came from a
-- finite list, an omega stream, or a disjoint union of the two.
dependentSumElementType :: InterpretedValue -> Maybe InterpretedValue
dependentSumElementType value =
  case interpretedSpecificationTargetEvidence value
      >>= dependentSumElementType of
    Just elementType -> Just elementType
    Nothing ->
      case evaluatedDependentSumStructure <$> dependentSumView value of
        Just (ListDependentSum elementType) -> Just elementType
        Just (StreamDependentSum elementType) -> Just elementType
        _ -> case interpretedForm value of
          EitherForm alternatives -> commonElementType
            (dependentSumElementType (evaluatedEitherLeft alternatives))
            (dependentSumElementType (evaluatedEitherRight alternatives))
          SpecificationForm specification ->
            dependentSumElementType (evaluatedSpecificationTarget specification)
          AssignmentForm specification ->
            dependentSumElementType (evaluatedSpecificationTarget specification)
          FederationSpecificationForm _ _ branches ->
            commonElementTypes (map dependentSumElementType branches)
          _ -> Nothing
  where
    commonElementType (Just left) (Just right)
      | interpretedSemanticResult left == interpretedSemanticResult right =
          Just left
    commonElementType _ _ = Nothing
    commonElementTypes [] = Nothing
    commonElementTypes (first : remaining) =
      foldl commonElementType first remaining

-- | Recover the member type of a finite recursive collection. Besides the
-- empty-or-step fixed point itself, a finite homogeneous prefix followed by
-- the same collection is another presentation of that family (for example
-- @T; List T@). This observes evaluated map structure, not parser encodings.
finiteDependentSumElementType :: InterpretedValue -> Maybe InterpretedValue
finiteDependentSumElementType = fmap snd . finiteDependentSumView

-- | The guaranteed finite prefix length and homogeneous member type of a
-- recursive finite collection.
finiteDependentSumView
  :: InterpretedValue
  -> Maybe (Natural, InterpretedValue)
finiteDependentSumView value =
  case interpretedSpecificationTargetEvidence value
      >>= finiteDependentSumView of
    Just description -> Just description
    Nothing ->
      case evaluatedDependentSumStructure <$> dependentSumView value of
        Just (ListDependentSum elementType) -> Just (0, elementType)
        _ -> case interpretedForm value of
          EitherForm alternatives -> commonElementType
            (finiteDependentSumView
              (evaluatedEitherLeft alternatives))
            (finiteDependentSumView
              (evaluatedEitherRight alternatives))
          SpecificationForm specification ->
            finiteDependentSumView
              (evaluatedSpecificationTarget specification)
          AssignmentForm specification ->
            finiteDependentSumView
              (evaluatedSpecificationTarget specification)
          FederationSpecificationForm _ _ branches ->
            commonElementTypes
              (map finiteDependentSumView branches)
          ConcatenatedMapForm left right -> do
            (minimumLength, elementType) <- finiteDependentSumView right
            guard (sameElementType elementType left)
            Just (minimumLength + 1, elementType)
          SequentialMapForm -> finitePrefixElementType value
          MapForm -> finitePrefixElementType value
          _ -> Nothing
  where
    commonElementType
        (Just (leftMinimum, left))
        (Just (rightMinimum, right))
      | sameElementType left right =
          Just (min leftMinimum rightMinimum, left)
    commonElementType _ _ = Nothing
    commonElementTypes [] = Nothing
    commonElementTypes (first : remaining) =
      foldl commonElementType first remaining
    finitePrefixElementType sequenceValue = do
      count <- naturalAtOrdinal
        (interpretedMapFinalOrderType (interpretedMap sequenceValue))
      guard (count >= 2)
      members <- traverse
        (interpretedMapValueAt (interpretedMap sequenceValue) . finiteOrdinal)
        (naturalsBelow count)
      (prefix, tailValue) <- splitLast members
      (minimumLength, elementType) <- finiteDependentSumView tailValue
      guard (all (sameElementType elementType) prefix)
      Just (minimumLength + fromIntegral (length prefix), elementType)
    splitLast [] = Nothing
    splitLast members = Just (init members, last members)
    sameElementType left right =
      interpretedSemanticResult left == interpretedSemanticResult right

-- | Retain the target established by successful specification without
-- replacing the source's runtime representation. Evaluation paths that need
-- type-directed structure can recover the proof instead of re-validating or
-- guessing it from the erased source value.
withSpecificationTargetEvidence
  :: InterpretedValue
  -> InterpretedValue
  -> InterpretedValue
withSpecificationTargetEvidence target value = value
  { interpretedSpecificationTargetEvidence = Just target }

-- | Attach the dependent-sum capability of the first value to the second
-- without replacing the second value's primary form.
withDependentSumView :: InterpretedValue -> InterpretedValue -> InterpretedValue
withDependentSumView view value =
  value { interpretedDependentSumView = dependentSumView view }

-- | The semantic, ordinal-indexed view of a genuinely ordered Atlas map.
-- This is separate from 'interpretedMap': every runtime value has an erased
-- map presentation, but not every value denotes an ordered family whose
-- positions may be used as generic witnesses.
orderedAtlasMapView
  :: InterpretedValue
  -> Maybe (OrdinalOrderedValues InterpretedValue)
orderedAtlasMapView = interpretedOrderedAtlasMapView

-- | Expose the value's own final-page ordering as a semantic ordered-map
-- capability.
withOrderedAtlasMapView :: InterpretedValue -> InterpretedValue
withOrderedAtlasMapView value =
  withOrderedAtlasMapValues
    (interpretedMapFinalValues (interpretedMap value))
    value

-- | Attach an explicitly constructed semantic ordering. Range adapters use
-- this when their erased insertion coordinates differ from their Datra
-- witness values, as for descending integer ranges.
withOrderedAtlasMapValues
  :: OrdinalOrderedValues InterpretedValue
  -> InterpretedValue
  -> InterpretedValue
withOrderedAtlasMapValues values value =
  value { interpretedOrderedAtlasMapView = Just values }

-- | Retain a value's primary behavior while exposing another value through
-- ordinary Atlas access. Generic functions use this for the lazy map induced
-- by a valued-range prefix; calls and canonical rendering remain functional.
withMapView :: InterpretedValue -> InterpretedValue -> InterpretedValue
withMapView view value = value
  { interpretedInsertionCapability = interpretedInsertionCapability view
  , interpretedMap = interpretedMap view
  , interpretedAtlasMapFederation = interpretedAtlasMapFederation view
  , interpretedTotalAtlasMap = interpretedTotalAtlasMap view
  , interpretedOrderedAtlasMapView = orderedAtlasMapView view
  , interpretedNamedMapView = interpretedNamedMapView view
  }

-- | Attach source-independent structure to a dependent sum.  Constructors
-- such as recursive lists use this instead of making later consumers infer a
-- standard-library identifier from rendered text.
withDependentSumStructure
  :: DependentSumStructure
  -> InterpretedValue
  -> InterpretedValue
withDependentSumStructure structure value =
  mapDependentSumView
    (\dependent -> dependent { evaluatedDependentSumStructure = structure })
    value

-- | Attach the exact access map of a dependent family.  The structural
-- target remains available for ordinary static reasoning, while projection
-- is delayed until a concrete insertion is supplied.
withDependentSumAccess
  :: (InterpretedValue -> Either InterpretingError InterpretedValue)
  -> InterpretedValue
  -> InterpretedValue
withDependentSumAccess access value =
  mapDependentSumView
    (\dependent -> dependent { evaluatedDependentSumAccess = Just access })
    value

-- | Retain the indexing family and exact fibre constructor of a dependent
-- sum.  Selection can then instantiate a candidate from its dependency
-- witness instead of reconstructing an index from the candidate's shape.
withDependentSumFamily
  :: InterpretedValue
  -> (InterpretedValue -> Either InterpretingError InterpretedValue)
  -> InterpretedValue
  -> InterpretedValue
withDependentSumFamily domain fibreAt value =
  mapDependentSumView
    (\dependent -> dependent
      { evaluatedDependentSumDomain = Just domain
      , evaluatedDependentSumFibreAt = Just fibreAt
      })
    value

-- | Retain a structural target that contains every identifier admitted by
-- the dependent family.  Nested projections use this for the named argument
-- pass before selecting one concrete fibre.
withDependentSumReservationTarget
  :: InterpretedValue
  -> InterpretedValue
  -> InterpretedValue
withDependentSumReservationTarget target value =
  mapDependentSumView
    (\dependent -> dependent
      { evaluatedDependentSumReservationTarget = Just target })
    value

mapDependentSumView
  :: (EvaluatedDependentSum -> EvaluatedDependentSum)
  -> InterpretedValue
  -> InterpretedValue
mapDependentSumView operation value =
  case interpretedForm value of
    DependentSumForm dependent ->
      value { interpretedForm = DependentSumForm (operation dependent) }
    _ -> value
      { interpretedDependentSumView = operation
          <$> interpretedDependentSumView value
      }

-- | A lazily indexed Atlas map.  This is the erased runtime presentation of
-- a dependent family's page projection; values are demanded through normal
-- Atlas access rather than materialized eagerly.
makeLazyMapValue
  :: Ordinal
  -> (Ordinal -> Maybe InterpretedValue)
  -> InterpretedValue
makeLazyMapValue orderType valueAt =
  makeCheckedLazyMapValue orderType (Right . valueAt)

-- | A lazily indexed Atlas map whose demanded members may fail evaluation.
-- The ordinary ordered view remains available for structural operations, but
-- checked access preserves a binding failure instead of confusing it with an
-- unavailable ordinal.
makeCheckedLazyMapValue
  :: Ordinal
  -> (Ordinal -> Either InterpretingError (Maybe InterpretedValue))
  -> InterpretedValue
makeCheckedLazyMapValue orderType valueAt =
  withOrderedAtlasMapValues values
    (makeInterpretedValue
      structuralDatraType
      MapForm
      NoInsertion
      valueMap
      (SingletonAtlasMapFederation valueMap)
      NonTotalInterpretedMap
      (MapSemantics 1 []))
  where
    values = OrdinalOrderedValues orderType
      (either (const Nothing) id . valueAt)
    valueMap = InterpretedMap
        1
        values
        valueAt
        []

interpretedValueHasTotalMap :: InterpretedValue -> Bool
interpretedValueHasTotalMap = maybe False (const True) . interpretedTotalAtlasMap

-- | Totality at the Datra type level. Begin/yield blocks are singleton types
-- even when the yielded value denotes a wider federation.
interpretedTypeIsTotal :: InterpretedValue -> Bool
interpretedTypeIsTotal value =
  interpretedValueHasTotalMap value
    || case datraTypeFamily
        (interpretedDatraType value) of
      TotalBlockTypeFamily -> True
      FunctionTypeFamily -> case interpretedFunction value of
        Just function -> maybe False (const True) (functionSource function)
        Nothing -> False
      _ -> False

-- | Retain evaluation provenance without changing the semantic map or codec.
withEvaluationSource :: Maybe String -> InterpretedValue -> InterpretedValue
withEvaluationSource source value =
  value
    { interpretedDatraType =
        maybe
          (interpretedDatraType value)
          (const totalBlockDatraType)
          source
    , interpretedEvaluationSource = source
    }

interpretedCanonicalResult :: InterpretedValue -> CanonicalResult
interpretedCanonicalResult = canonicalResult . interpretedSemantics

-- | Presentation-free identity for type checks and semantic comparisons.
interpretedSemanticResult :: InterpretedValue -> CanonicalResult
interpretedSemanticResult = semanticCanonicalResult . interpretedSemantics

-- | Runtime operations inspect the denoted value, never its retained name.
interpretedSemanticSemantics :: InterpretedValue -> ValueSemantics
interpretedSemanticSemantics = semanticValueSemantics . interpretedSemantics

withInterpretedSemantics
  :: ValueSemantics
  -> InterpretedValue
  -> InterpretedValue
withInterpretedSemantics semantics value = value
  { interpretedSemantics = semantics }

interpretedCanonicalPresentation
  :: InterpretedValue
  -> Maybe ([PresentationDependency], CanonicalResult)
interpretedCanonicalPresentation = canonicalPresentation . interpretedSemantics

withCanonicalReference
  :: [PresentationDependency]
  -> String
  -> InterpretedValue
  -> InterpretedValue
withCanonicalReference dependencies name value = value
  { interpretedSemantics = PresentedSemantics
      dependencies
      (AtomicPresentation (CanonicalReference name))
      (interpretedSemantics value)
  }

withCanonicalNamedAccess
  :: [PresentationDependency]
  -> CanonicalResult
  -> String
  -> InterpretedValue
  -> InterpretedValue
withCanonicalNamedAccess dependencies operand name value = value
  { interpretedSemantics = PresentedSemantics
      dependencies
      (AtomicPresentation (CanonicalNamedAccess operand name))
      (interpretedSemantics value)
  }

withCanonicalApplication
  :: InterpretedValue
  -> InterpretedValue
  -> InterpretedValue
  -> InterpretedValue
withCanonicalApplication function argument value =
  case ( interpretedCanonicalPresentation function
       , interpretedCanonicalPresentation argument
       ) of
    (Nothing, Nothing) -> value
    _ -> value
      { interpretedSemantics = PresentedSemantics
          []
          (ApplicationPresentation
            (presentationForSemantics (interpretedSemantics function))
            (presentationForSemantics (interpretedSemantics argument)))
          (interpretedSemantics value)
      }

withoutCanonicalPresentation :: InterpretedValue -> InterpretedValue
withoutCanonicalPresentation value = value
  { interpretedSemantics = semanticValueSemantics (interpretedSemantics value) }

withoutCanonicalDependencies
  :: [PresentationDependency]
  -> InterpretedValue
  -> InterpretedValue
withoutCanonicalDependencies dependencies value = value
  { interpretedSemantics =
      stripPresentedDependencies dependencies (interpretedSemantics value) }

interpretedValueKind :: InterpretedValue -> InterpretedValueKind
interpretedValueKind value =
  case interpretedForm value of
    NeverForm -> MapValueKind
    BuiltinMetaTypeForm (ASTMetaType _) -> FunctionValueKind
    FunctionBodyForm _ -> FunctionValueKind
    BuiltinMetaTypeForm TemplateMetaType -> AsciiStringValueKind
    BuiltinMetaTypeForm _ -> RangeValueKind
    FunctionForm _ -> FunctionValueKind
    ExplicitForm (EvaluatedExplicit _ NaturalOrigin _) -> NaturalValueKind
    ExplicitForm _ -> ExplicitOrdinalValueKind
    IntegerForm _ -> IntegerValueKind
    BooleanForm _ -> BooleanValueKind
    NothingForm -> MapValueKind
    FormulationForm _ -> FormulationValueKind
    RangeForm _ -> RangeValueKind
    NaturalRangeForm _ -> RangeValueKind
    ValuedNaturalRangeForm _ -> RangeValueKind
    IntegerRangeForm _ -> RangeValueKind
    ValuedIntegerRangeForm _ -> RangeValueKind
    EitherForm _ -> EitherValueKind
    ArgumentMapForm _ _ -> MapValueKind
    SkipForm _ -> FormulationValueKind
    FederationSpecificationForm _ _ _ -> SpecificationValueKind
    RangeConcatenationForm _ _ -> RangeConcatenationValueKind
    AsciiStringForm _ -> AsciiStringValueKind
    IdentifierValueTypeForm -> AsciiStringValueKind
    ToStringForm -> AsciiStringValueKind
    TemplateForm _ -> AsciiStringValueKind
    SpecificationForm _ -> SpecificationValueKind
    AssignmentForm _ -> SpecificationValueKind
    DependentIdentifierTypeForm _ -> DependentIdentifierTypeValueKind
    IdentifierStringProjectionForm _ -> DependentIdentifierTypeValueKind
    DependentSumForm _ -> MapValueKind
    CoalizationForm _ -> MapValueKind
    SequentialMapForm -> MapValueKind
    ExpansionMapForm _ _ -> MapValueKind
    ConcatenatedMapForm _ _ -> MapValueKind
    MapForm -> MapValueKind

interpretedExplicitOrdinal
  :: InterpretedValue
  -> Maybe (Natural, Ordinal)
interpretedExplicitOrdinal value =
  case interpretedForm value of
    ExplicitForm explicitValue -> Just (explicitOrdinal explicitValue)
    _ -> Nothing

interpretedSpecificationSourceValue
  :: InterpretedValue
  -> Maybe InterpretedValue
interpretedSpecificationSourceValue value =
  case interpretedForm value of
    SpecificationForm specification ->
      Just (evaluatedSpecificationSourceValue specification)
    _ -> Nothing

interpretedFederationSpecificationBranches
  :: InterpretedValue
  -> Maybe [InterpretedValue]
interpretedFederationSpecificationBranches value =
  case interpretedForm value of
    FederationSpecificationForm _ _ branches -> Just branches
    _ -> Nothing

interpretedFederationSpecificationSourceValue
  :: InterpretedValue
  -> Maybe InterpretedValue
interpretedFederationSpecificationSourceValue value =
  case interpretedForm value of
    FederationSpecificationForm source _ _ -> Just source
    _ -> Nothing

interpretedInteger :: InterpretedValue -> Maybe Integer
interpretedInteger value =
  case interpretedForm value of
    IntegerForm integer -> Just integer
    ExplicitForm (EvaluatedExplicit 1 _ explicitValue) ->
      toInteger <$> naturalAtOrdinal (superEllipsisValueOrdinal explicitValue)
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
    NaturalRangeForm valueRange ->
      Just (rangeDescription (naturalRangeAsEvaluatedRange valueRange))
    ValuedNaturalRangeForm valueRange ->
      Just (rangeDescription (valuedNaturalRangeAsEvaluatedRange valueRange))
    _ -> Nothing

interpretedMapFinalOrderType :: InterpretedMap -> Ordinal
interpretedMapFinalOrderType =
  ordinalOrderedValuesOrderType . interpretedMapFinalValues

interpretedMapValueAt
  :: InterpretedMap
  -> Ordinal
  -> Maybe InterpretedValue
interpretedMapValueAt = ordinalOrderedValueAt . interpretedMapFinalValues

interpretedMapValueAtChecked
  :: InterpretedMap
  -> Ordinal
  -> Either InterpretingError (Maybe InterpretedValue)
interpretedMapValueAtChecked = interpretedMapCheckedValueAt

-- | Recover ASCII characters from a finite interpreted map. String operators
-- use this after delegating their ordering to the ordinary map operations.
asciiStringFromInterpretedMap :: InterpretedMap -> Maybe String
asciiStringFromInterpretedMap valueMap = do
  cardinality <- naturalAtOrdinal (interpretedMapFinalOrderType valueMap)
  traverse characterAt (finitePositions cardinality)
  where
    characterAt position = do
      value <- interpretedMapValueAt valueMap position
      (_, ordinalValue) <- interpretedExplicitOrdinal value
      characterCode <- naturalAtOrdinal ordinalValue
      guard (characterCode < 256)
      pure (chr (fromIntegral characterCode))

    finitePositions = map finiteOrdinal . naturalsBelow

explicitOrdinal :: EvaluatedExplicit -> (Natural, Ordinal)
explicitOrdinal (EvaluatedExplicit level _ value) =
  (level, superEllipsisValueOrdinal value)

explicitInsertion :: EvaluatedExplicit -> SomeSuperEllipsisInsertion
explicitInsertion (EvaluatedExplicit _ _ value) =
  eraseSuperEllipsisInsertion (superEllipsisValueInsertion value)

rangeDescription
  :: EvaluatedRange
  -> Range.SuperEllipsisRangeDescription
rangeDescription (EvaluatedRange _ _ valueRange) =
  Range.describeSuperEllipsisRange valueRange

evaluatedRangeLevel :: EvaluatedRange -> Natural
evaluatedRangeLevel (EvaluatedRange level _ _) = level

evaluatedRangeAccessPolicy :: EvaluatedRange -> RangeAccessPolicy
evaluatedRangeAccessPolicy (EvaluatedRange _ policy _) = policy

rangeInsertion :: EvaluatedRange -> SomeSuperEllipsisInsertion
rangeInsertion (EvaluatedRange _ _ valueRange) =
  eraseSuperEllipsisInsertion
    (Range.superEllipsisRangeInsertion valueRange)

naturalRangeAsEvaluatedRange :: EvaluatedNaturalRange -> EvaluatedRange
naturalRangeAsEvaluatedRange (EvaluatedNaturalRange valueRange) =
  EvaluatedRange
    1
    ClippableRangeFederation
    (NaturalRange.naturalRangeEllipsisRange valueRange)

valuedNaturalRangeAsEvaluatedRange
  :: EvaluatedValuedNaturalRange
  -> EvaluatedRange
valuedNaturalRangeAsEvaluatedRange
    (EvaluatedValuedNaturalRange valueRange) =
  EvaluatedRange
    1
    ExactRangeInsertion
    (ValuedNaturalRange.valuedNaturalRangeEllipsisRange valueRange)

valueRanges :: InterpretedValue -> Maybe [EvaluatedRange]
valueRanges value =
  case interpretedForm value of
    RangeForm valueRange -> Just [valueRange]
    NaturalRangeForm valueRange ->
      Just [naturalRangeAsEvaluatedRange valueRange]
    ValuedNaturalRangeForm valueRange ->
      Just [valuedNaturalRangeAsEvaluatedRange valueRange]
    RangeConcatenationForm ranges _ -> Just ranges
    _ -> Nothing

emptyInterpretedMap :: InterpretedMap
emptyInterpretedMap = InterpretedMap
  0
  emptyOrdinalOrderedValues
  (const (Right Nothing))
  []

singletonMap :: ValueSemantics -> InterpretedValue -> InterpretedMap
singletonMap semantics value =
  InterpretedMap
    1
    (singletonOrdinalOrderedValues value)
    (Right . ordinalOrderedValueAt (singletonOrdinalOrderedValues value))
    [semantics]
