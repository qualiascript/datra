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
      (finiteOrdinal 2)
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
    accessPositions [position]
      | position == finiteOrdinal 0 = Right identifierStringValue
      | position == finiteOrdinal 1 = Right underlying
    accessPositions positions
      | positions == [finiteOrdinal 0, finiteOrdinal 1] = Right original
      | otherwise =
          Right
            (makeAtlasMap
              2
              (map valueAt positions))

    valueAt position
      | position == finiteOrdinal 0 = identifierStringValue
      | otherwise = underlying

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
