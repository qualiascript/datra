-- | Finite membership decisions for total strings against string federations.
module Evaluation.Specification.String
  ( federationProducesStrings
  , selectStringFederationMember
  ) where

import AtlasMapFederationExpression
  ( AtlasMapFederationExpression (..)
  )
import Evaluation.Construction (makeInteger, makeNatural)
import Evaluation.Specification.Decision
  ( Decision (..)
  , decideAny
  , mapDecision
  )
import Evaluation.Value
import Numeric.Natural (Natural)

-- | Whether every member described by a federation is an ASCII string.
federationProducesStrings :: InterpretedAtlasMapFederation -> Bool
federationProducesStrings federation =
  case federation of
    SingletonAtlasMapFederation valueMap ->
      case interpretedMapComponents valueMap of
        [AsciiStringSemantics _] -> True
        _ -> False
    PrimitiveAtlasMapFederation primitive ->
      case primitive of
        StringTypeAtlasMapFederation -> True
        ToStringAtlasMapFederation _ -> True
        _ -> False
    ConcatenatedAtlasMapFederation left right ->
      federationProducesStrings left && federationProducesStrings right
    SequentialAtlasMapFederation _ -> False
    ExpansionAtlasMapFederation _ _ -> False

-- | Select a concrete string by traversing the retained string-federation
-- expression. Concatenations are split only at the finitely many character
-- boundaries of the source string.
selectStringFederationMember
  :: SelectMember
  -> InterpretedValue
  -> InterpretedValue
  -> Maybe (Decision EvaluatedAtlasMapFederationMember)
selectStringFederationMember selectMember source target = do
  characters <-
    case interpretedCanonicalResult source of
      CanonicalAsciiString value -> Just value
      _ -> Nothing
  selectCharacters
    selectMember characters (interpretedAtlasMapFederation target)

selectCharacters
  :: SelectMember
  -> String
  -> InterpretedAtlasMapFederation
  -> Maybe (Decision EvaluatedAtlasMapFederationMember)
selectCharacters selectMember characters federation =
  case federation of
    SingletonAtlasMapFederation valueMap ->
      case interpretedMapComponents valueMap of
        [AsciiStringSemantics expected] ->
          Just
            (if characters == expected
              then
                DecisionProved
                  (EvaluatedSingletonAtlasMapMember
                    (CanonicalAsciiString expected))
              else DecisionRefuted)
        _ -> Nothing
    PrimitiveAtlasMapFederation primitive ->
      case primitive of
        StringTypeAtlasMapFederation ->
          Just (DecisionProved (EvaluatedAsciiStringMember characters))
        ToStringAtlasMapFederation source ->
          Just
            (case parseCanonicalMember source characters of
              ParsedCanonicalMember candidate ->
                mapDecision
                  EvaluatedToStringMember
                  (selectMember candidate source)
              RejectedCanonicalMember -> DecisionRefuted
              UnsupportedCanonicalMember -> DecisionUndecidable)
        _ -> Nothing
    ConcatenatedAtlasMapFederation left right -> do
      decisions <-
        traverse
          (uncurry (selectConcatenatedCharacters selectMember left right))
          (characterSplits characters)
      pure (decideAny decisions)
    SequentialAtlasMapFederation _ -> Nothing
    ExpansionAtlasMapFederation _ _ -> Nothing

selectConcatenatedCharacters
  :: SelectMember
  -> InterpretedAtlasMapFederation
  -> InterpretedAtlasMapFederation
  -> String
  -> String
  -> Maybe (Decision EvaluatedAtlasMapFederationMember)
selectConcatenatedCharacters selectMember left right leftText rightText = do
  leftDecision <- selectCharacters selectMember leftText left
  rightDecision <- selectCharacters selectMember rightText right
  pure (combineConcatenatedDecisions leftDecision rightDecision)

combineConcatenatedDecisions
  :: Decision EvaluatedAtlasMapFederationMember
  -> Decision EvaluatedAtlasMapFederationMember
  -> Decision EvaluatedAtlasMapFederationMember
combineConcatenatedDecisions
    (DecisionProved left)
    (DecisionProved right) =
      DecisionProved (EvaluatedConcatenatedAtlasMapMember [left, right])
combineConcatenatedDecisions DecisionRefuted _ = DecisionRefuted
combineConcatenatedDecisions _ DecisionRefuted = DecisionRefuted
combineConcatenatedDecisions _ _ = DecisionUndecidable

type SelectMember =
  InterpretedValue
  -> InterpretedValue
  -> Decision EvaluatedAtlasMapFederationMember

characterSplits :: String -> [(String, String)]
characterSplits characters =
  [splitAt position characters | position <- [0 .. length characters]]

data CanonicalMemberParse
  = ParsedCanonicalMember InterpretedValue
  | RejectedCanonicalMember
  | UnsupportedCanonicalMember

parseCanonicalMember
  :: InterpretedValue
  -> String
  -> CanonicalMemberParse
parseCanonicalMember source characters =
  case interpretedForm source of
    ValuedNaturalRangeForm _ ->
      maybe RejectedCanonicalMember
        (ParsedCanonicalMember . makeNatural)
        (readCanonical characters :: Maybe Natural)
    ValuedIntegerRangeForm _ ->
      maybe RejectedCanonicalMember
        (ParsedCanonicalMember . makeInteger)
        (readCanonical characters :: Maybe Integer)
    _ -> UnsupportedCanonicalMember

readCanonical :: (Read value, Show value) => String -> Maybe value
readCanonical characters =
  case reads characters of
    [(value, "")]
      | show value == characters -> Just value
    _ -> Nothing
