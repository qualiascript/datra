-- | The language-level coalization operation.
--
-- Coalization forgets an Atlas's page decomposition and includes the
-- resulting carrier back as a single-page Atlas. Ranked final-page values are
-- retained, so ordinary access still observes the operand's members.
module Evaluation.Coalization
  ( coalizeValue
  , coalizeMapMemberAt
  , federationIsCoalized
  , federationIsCoalition
  , valueIsCoalition
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (..)
  )
import Evaluation.Value
import Numeric.Natural (Natural)

coalizeValue :: InterpretedValue -> InterpretedValue
coalizeValue value
  | CoalizationForm _ <- interpretedForm value = value
  | otherwise =
      makeInterpretedValue
        (interpretedDatraType value)
        (CoalizationForm value)
        (interpretedInsertionCapability value)
        coalizedMap
        (CoalizedAtlasMapFederation
          (interpretedAtlasMapFederation value))
        totality
        (CoalizationSemantics operandSemantics)
  where
    operandSemantics
      | valueIsCharacterList value = CharacterListSemantics
      | otherwise = interpretedSemantics value
    operandMap = interpretedMap value
    coalizedMap = operandMap
      { interpretedMapPageCardinality = 1
      , interpretedMapComponents = [interpretedSemantics value]
      }
    totality
      | interpretedValueHasTotalMap value = TotalInterpretedMap
      | otherwise = NonTotalInterpretedMap

-- | The recursive list constructor and the character family retain explicit
-- structural provenance.  Coalization uses that evidence for string
-- behavior without replacing or unwrapping the coalization value itself.
valueIsCharacterList :: InterpretedValue -> Bool
valueIsCharacterList value =
  case interpretedForm value of
    DependentSumForm dependent ->
      case evaluatedDependentSumStructure dependent of
        ListDependentSum elementType -> valueIsCharacterType elementType
        _ -> False
    SpecificationForm specification ->
      valueIsCharacterList (evaluatedSpecificationTarget specification)
    AssignmentForm specification ->
      valueIsCharacterList (evaluatedSpecificationTarget specification)
    _ -> False
  where
    valueIsCharacterType elementType =
      case interpretedForm elementType of
        DependentSumForm dependent ->
          case evaluatedDependentSumStructure dependent of
            CharacterDependentSum -> True
            _ -> False
        SpecificationForm specification ->
          valueIsCharacterType (evaluatedSpecificationTarget specification)
        AssignmentForm specification ->
          valueIsCharacterType (evaluatedSpecificationTarget specification)
        _ -> False

-- | Materialize the boundary previously inferred by canonical rendering: a
-- map-valued member whose page reaches the surrounding page must be coalized
-- to remain one operand when its source is parsed again.
coalizeMapMemberAt :: Natural -> InterpretedValue -> InterpretedValue
coalizeMapMemberAt outerCardinality value =
  case interpretedSemantics value of
    MapSemantics memberCardinality _
      | memberCardinality >= outerCardinality -> coalizeValue value
    _ -> value

-- | A coalition federation contributes one stable position when used as an
-- operand of a sequential construction. Primitive valued ranges and dependent
-- identifier families are intrinsically coalitions; the coalization node is
-- the explicit construction for every other federation.
federationIsCoalition :: InterpretedAtlasMapFederation -> Bool
federationIsCoalition federation =
  case federation of
    CoalizedAtlasMapFederation _ -> True
    PrimitiveAtlasMapFederation
        (ValuedNaturalRangeAtlasMapFederation _) -> True
    PrimitiveAtlasMapFederation
        (ValuedIntegerRangeAtlasMapFederation _) -> True
    PrimitiveAtlasMapFederation
        (DependentIdentifierTypeAtlasMapFederation _) -> True
    PrimitiveAtlasMapFederation
        (EitherAtlasMapFederation alternatives) ->
      federationIsCoalition
        (interpretedAtlasMapFederation (evaluatedEitherLeft alternatives))
        && federationIsCoalition
          (interpretedAtlasMapFederation (evaluatedEitherRight alternatives))
    _ -> False

-- | Whether the federation carries the explicit construction witness. Unlike
-- intrinsic valued-range coalitions, two coalized operands have positional
-- boundaries even when their underlying member sets overlap.
federationIsCoalized :: InterpretedAtlasMapFederation -> Bool
federationIsCoalized (CoalizedAtlasMapFederation _) = True
federationIsCoalized _ = False

valueIsCoalition :: InterpretedValue -> Bool
valueIsCoalition = federationIsCoalition . interpretedAtlasMapFederation
