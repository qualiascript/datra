-- | Total constructors for primitive evaluated Datra values.
module Evaluation.Construction
  ( makeNothing
  , makeNatural
  , makeInteger
  , makeAsciiString
  , makeStringType
  , makeIdentifierValueType
  , makeExplicit
  , makeExplicitValue
  , makeFormulation
  , mapFromInsertion
  ) where

import Data.Char (ord)
import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (PrimitiveAtlasMapFederation) )
import DatraOrdinal (Ordinal, finiteOrdinal)
import Evaluation.Value
import IntegerRange.Encoding (integerSingletonInsertion)
import Numeric.Natural (Natural)
import NumericalOperators.NumericalOperand (someSuperEllipsis)
import SuperEllipsisValue
  ( canonicalSuperEllipsisValue
  , minimumSuperEllipsisValueRank
  )
import SuperEllipsisInsertion
  ( eraseSuperEllipsisInsertion
  , fullSomeSuperEllipsisInsertion
  , someSuperEllipsisInsertionOrderType
  , someSuperEllipsisInsertionPositionAt
  )

makeNatural :: Natural -> InterpretedValue
makeNatural = makeExplicit NaturalOrigin . finiteOrdinal

-- | Canonical finite signed value. Nonnegative results retain their existing
-- natural representation; negative results use the complemented @Nat x 2@
-- insertion.
makeInteger :: Integer -> InterpretedValue
makeInteger integer
  | integer >= 0 = makeNatural (fromInteger integer)
  | otherwise =
      integerSingletonInsertion integer $ \valueInsertion ->
        let semantics = IntegerSemantics integer
            value =
              makeSingletonInterpretedValue
                structuralDatraType
                (IntegerForm integer)
                (ValidInsertion (eraseSuperEllipsisInsertion valueInsertion))
                (singletonMap semantics value)
                TotalInterpretedMap
                semantics
        in value

-- | Construct the semantic two-page presentation of a nonempty ASCII string,
-- or the canonical empty presentation for an empty string.
makeAsciiString :: String -> InterpretedValue
makeAsciiString "Nothing" = makeNothing
makeAsciiString characters = value
  where
    characterValues =
      map (makeNatural . fromIntegral . ord) characters
    finalValues =
      foldl'
        appendOrdinalOrderedValues
        emptyOrdinalOrderedValues
        (map singletonOrdinalOrderedValues characterValues)
    semantics = AsciiStringSemantics characters
    valueMap =
      InterpretedMap
        (if null characters then 0 else 2)
        finalValues
        [semantics]
    value =
      makeSingletonInterpretedValue
        structuralDatraType
        (AsciiStringForm characters)
        NoInsertion
        valueMap
        TotalInterpretedMap
        semantics

-- | The federation of all finite ASCII strings.
makeStringType :: InterpretedValue
makeStringType =
  makeInterpretedValue
    structuralDatraType
    StringTypeForm
    NoInsertion
    emptyInterpretedMap
    (PrimitiveAtlasMapFederation StringTypeAtlasMapFederation)
    NonTotalInterpretedMap
    StringTypeSemantics

-- | The federation of strings accepted by compact @$...@ syntax.
makeIdentifierValueType :: InterpretedValue
makeIdentifierValueType =
  makeInterpretedValue
    structuralDatraType
    IdentifierValueTypeForm
    NoInsertion
    emptyInterpretedMap
    (PrimitiveAtlasMapFederation IdentifierValueTypeAtlasMapFederation)
    NonTotalInterpretedMap
    IdentifierValueTypeSemantics

makeExplicit :: ExplicitOrigin -> Ordinal -> InterpretedValue
makeExplicit origin = explicitInterpretedValue . makeExplicitValue origin

makeExplicitValue :: ExplicitOrigin -> Ordinal -> EvaluatedExplicit
makeExplicitValue origin ordinalValue =
  canonicalSuperEllipsisValue ordinalValue $ \value ->
    EvaluatedExplicit level origin value
  where
    level = minimumSuperEllipsisValueRank ordinalValue

explicitInterpretedValue :: EvaluatedExplicit -> InterpretedValue
explicitInterpretedValue explicitValue = value
  where
    (level, ordinalValue) = explicitOrdinal explicitValue
    insertion = explicitInsertion explicitValue
    semantics = ExplicitSemantics level ordinalValue
    valueMap = singletonMap semantics value
    value =
      makeSingletonInterpretedValue
        structuralDatraType
        (ExplicitForm explicitValue)
        (ValidInsertion insertion)
        valueMap
        TotalInterpretedMap
        semantics

makeFormulation :: Natural -> InterpretedValue
makeFormulation level = value
  where
    formulation = someSuperEllipsis level
    insertion = fullSomeSuperEllipsisInsertion level
    values =
      OrdinalOrderedValues
        (someSuperEllipsisInsertionOrderType insertion)
        (\position -> do
          absolute <- someSuperEllipsisInsertionPositionAt insertion position
          pure (makeExplicit ComputedOrigin absolute))
    valueMap = InterpretedMap 1 values [semantics]
    value =
      makeSingletonInterpretedValue
        structuralDatraType
        (FormulationForm formulation)
        (ValidInsertion insertion)
        valueMap
        TotalInterpretedMap
        semantics
    semantics = FormulationSemantics level

mapFromInsertion
  :: SomeSuperEllipsisInsertion
  -> [ValueSemantics]
  -> InterpretedMap
mapFromInsertion insertion components =
  InterpretedMap
    (if isEmpty then 0 else 1)
    (OrdinalOrderedValues
      (someSuperEllipsisInsertionOrderType insertion)
      (\position -> do
        absolute <- someSuperEllipsisInsertionPositionAt insertion position
        pure (makeExplicit ComputedOrigin absolute)))
    (if isEmpty then [] else components)
  where
    isEmpty =
      someSuperEllipsisInsertionOrderType insertion == finiteOrdinal 0

-- | The distinguished absent value, rendered canonically as @Nothing : ()@.
makeNothing :: InterpretedValue
makeNothing = value
  where
    unitSemantics = MapSemantics 0 []
    semantics =
      DependentIdentifierTypeSemantics
        (SimpleIdentifierDependency "Nothing")
        unitSemantics
        True
    value =
      makeSingletonInterpretedValue
        structuralDatraType
        NothingForm
        NoInsertion
        emptyInterpretedMap
        TotalInterpretedMap
        semantics
