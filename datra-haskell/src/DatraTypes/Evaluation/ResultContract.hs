-- | Conservatively decide whether a semantic result contract's complete
-- representation is public.  This is a structural property of the evaluated
-- contract; individual protection policies decide whether to use the proof.
module Evaluation.ResultContract
  ( decideClosedPublicResultContract
  ) where

import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import Evaluation.Specification.Decision
  ( Decision (..)
  , decideAll
  , mapDecision
  )
import Evaluation.Specification.String (valueProducesStrings)
import Evaluation.Value

decideClosedPublicResultContract
  :: InterpretedValue
  -> Decision ()
decideClosedPublicResultContract = go 256
  where
    go :: Int -> InterpretedValue -> Decision ()
    go fuel value
      | fuel <= 0 = DecisionUndecidable
      | interpretedScopeProtection value /= Nothing = DecisionRefuted
      | valueProducesStrings value = DecisionProved ()
      | otherwise =
          case interpretedForm value of
            NeverForm -> eligible
            BuiltinMetaTypeForm OrdinalMetaType -> eligible
            BuiltinMetaTypeForm NatRangeMetaType -> eligible
            BuiltinMetaTypeForm IntRangeMetaType -> eligible
            BuiltinMetaTypeForm NatValRangeMetaType -> eligible
            BuiltinMetaTypeForm IntValRangeMetaType -> eligible
            BuiltinMetaTypeForm _ -> ineligible
            FunctionForm _ -> ineligible
            ExplicitForm _ -> eligible
            IntegerForm _ -> eligible
            BooleanForm _ -> eligible
            NothingForm -> eligible
            FormulationForm _ -> ineligible
            RangeForm _ -> eligible
            NaturalRangeForm _ -> eligible
            ValuedNaturalRangeForm _ -> eligible
            IntegerRangeForm _ -> eligible
            ValuedIntegerRangeForm _ -> eligible
            EitherForm alternatives -> combine
              [ descend (evaluatedEitherLeft alternatives)
              , descend (evaluatedEitherRight alternatives)
              ]
            ArgumentMapForm members _ -> combine (map descend members)
            SkipForm _ -> ineligible
            FederationSpecificationForm _ target branches ->
              combine (descend target : map descend branches)
            RangeConcatenationForm _ _ -> eligible
            AsciiStringForm _ -> eligible
            IdentifierValueTypeForm -> eligible
            ToStringForm -> eligible
            TemplateForm underlying -> descend underlying
            SpecificationForm specification ->
              descend (evaluatedSpecificationTarget specification)
            AssignmentForm specification ->
              descend (evaluatedSpecificationTarget specification)
            DependentIdentifierTypeForm identifier ->
              case evaluatedIdentifierDependency identifier of
                SimpleIdentifierDependency _ ->
                  case ( evaluatedIdentifierNameFederation identifier
                       , evaluatedIdentifierNameFamily identifier
                       ) of
                    (Nothing, Nothing) ->
                      descend (evaluatedIdentifierUnderlying identifier)
                    _ -> ineligible
                DependentIdentifierDependency {} -> ineligible
            IdentifierStringProjectionForm _ -> ineligible
            DependentSumForm _ -> ineligible
            CoalizationForm operand -> descend operand
            SequentialMapForm -> finiteMapMembers value
            ExpansionMapForm left right ->
              combine [descend left, descend right]
            ConcatenatedMapForm left right ->
              combine [descend left, descend right]
            MapForm -> finiteMapMembers value
      where
        descend = go (fuel - 1)
        finiteMapMembers contract =
          case naturalAtOrdinal
              (interpretedMapFinalOrderType (interpretedMap contract)) of
            Nothing -> ineligible
            Just count -> combine
              [ maybe DecisionUndecidable descend
                  (interpretedMapValueAt
                    (interpretedMap contract) (finiteOrdinal position))
              | position <- if count == 0 then [] else [0 .. count - 1]
              ]

    eligible = DecisionProved ()
    ineligible = DecisionRefuted

    combine = mapDecision (const ()) . decideAll
