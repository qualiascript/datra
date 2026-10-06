-- | Access through the two-position map view of an identifier type.
module Evaluation.Access.Identifier
  ( accessDependentIdentifierType
  ) where

import Data.Bifunctor qualified as Bifunctor
import DatraOrdinal
  ( Ordinal
  , finiteOrdinal
  , naturalAtOrdinal
  , omegaPower
  )
import Evaluation.Access.Federation (requireInsertion)
import Evaluation.Construction (makeAsciiString)
import Evaluation.Error (InterpretingError (AccessRejected))
import Evaluation.Identifier
  ( identifierStringProjectionValue
  )
import Evaluation.Map (makeAtlasMap)
import Evaluation.Value
import MapOperators.AccessOperator (validateAccessSelection)
import Numeric.Natural (Natural)
import SuperEllipsisInsertion
  ( someSuperEllipsisInsertionOrderType
  , someSuperEllipsisInsertionPositionAt
  , someSuperEllipsisInsertionRank
  )

accessDependentIdentifierType
  :: InterpretedValue
  -> EvaluatedDependentIdentifierType
  -> InterpretedValue
  -> Either InterpretingError InterpretedValue
accessDependentIdentifierType original identifier insertionValue = do
  insertion <- requireInsertion insertionValue
  let insertionOrderType = someSuperEllipsisInsertionOrderType insertion
  Bifunctor.first AccessRejected
    (validateAccessSelection
      (omegaPower (someSuperEllipsisInsertionRank insertion))
      insertionOrderType
      sourceOrderType
      (someSuperEllipsisInsertionPositionAt insertion))
  case naturalAtOrdinal insertionOrderType of
    Nothing ->
      -- Validation against a two-position map always rejects this case.
      pure (makeAtlasMap 0 [])
    Just cardinality -> do
      positions <- traverse (selectedPosition insertion) (finitePositions cardinality)
      accessPositions positions
  where
    underlying = evaluatedIdentifierUnderlying identifier
    dependency = evaluatedIdentifierDependency identifier
    identifierStringValue =
      case dependency of
        SimpleIdentifierDependency identifierString ->
          makeAsciiString identifierString
        DependentIdentifierDependency _ _ ->
          identifierStringProjectionValue identifier

    accessPositions [] = Right (makeAtlasMap 0 [])
    accessPositions [position] = maybe
      (Right (makeAtlasMap 0 []))
      Right
      (valueAt position)
    accessPositions positions
      | positions == map finiteOrdinal (finitePositions sourceCardinality) =
          Right original
      | otherwise =
          Right
            (makeAtlasMap
              2
              [ value
              | position <- positions
              , Just value <- [valueAt position]
              ])

    valueAt position
      | position == finiteOrdinal 0 = Just identifierStringValue
      | position == finiteOrdinal 1 = Just underlying
      | otherwise = interpretedMapValueAt sourceMap position

    sourceMap = interpretedMap original
    sourceOrderType = interpretedMapFinalOrderType sourceMap
    sourceCardinality = maybe 0 id (naturalAtOrdinal sourceOrderType)

selectedPosition
  :: SomeSuperEllipsisInsertion
  -> Natural
  -> Either InterpretingError Ordinal
selectedPosition insertion position =
  case someSuperEllipsisInsertionPositionAt insertion (finiteOrdinal position) of
    Just selected -> Right selected
    Nothing -> Right (finiteOrdinal 0)

finitePositions :: Natural -> [Natural]
finitePositions 0 = []
finitePositions cardinality = [0 .. cardinality - 1]
