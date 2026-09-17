{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Ordered access to the final page of an ordinal-indexed Atlas map.
--
-- A 'SuperEllipsisInsertion' supplies both the absolute final-page indices and
-- the order in which they are requested.  Successful access constructs a
-- fresh two-page chained Atlas map in precisely that order.  Failure means
-- that the insertion was empty or could not be certified to lie inside the
-- left Atlas's final order type.
module MapOperators.AccessOperator
  ( IndexedAtlasMap
  , indexedAtlasMap
  , indexedAtlasMapFromChain
  , indexedAtlasAtlas
  , indexedAtlasAtlasMap
  , indexedAtlasChain
  , indexedAtlasDominion
  , indexedAtlasCardinality
  , indexedAtlasValueAt
  , indexedAtlasValueAtOrdinal
  , AccessMapOperand (AccessValue, accessMap)
  , AccessElement
  , accessElementPosition
  , accessElementSource
  , accessElementValue
  , AccessOperand (AccessSource)
  , accessOperator
  ) where

import Chain
  ( chain
  , chainIndex
  , chainObjectAt
  , chainOrderType
  , chainPosition
  )
import DatraOrdinal
  ( Ordinal
  , finiteOrdinal
  , naturalAtOrdinal
  , ordinalLT
  )
import Data.Kind (Type)
import Dominion (dominion, rank, unrank)
import MapOperators.IndexedAtlasMap
  ( IndexedAtlasMap
  , indexedAtlasAtlas
  , indexedAtlasAtlasMap
  , indexedAtlasCardinality
  , indexedAtlasChain
  , indexedAtlasDominion
  , indexedAtlasMap
  , indexedAtlasMapFromChain
  , indexedAtlasValueAt
  , indexedAtlasValueAtOrdinal
  )
import StableConfederalData (StableConfederalData)
import SuperEllipsis
  ( SuperEllipsisTarget
  , SuperEllipsisTerminal
  , superEllipsisDominion
  , superEllipsisRankOrderType
  , superEllipsisTargetRank
  )
import SuperEllipsisInsertion
  ( SuperEllipsisInsertion
  , SuperEllipsisInsertionMap (..)
  , applySuperEllipsisInsertion
  , fullSuperEllipsisInsertion
  , superEllipsisInsertionChain
  , superEllipsisInsertionFirst
  , superEllipsisInsertionPosition
  , superEllipsisInsertionPreimage
  , superEllipsisInsertionRank
  , superEllipsisInsertionMap
  )
import SuperEllipsisRange
  ( SuperEllipsisRange
  , SuperEllipsisRangeElement
  , superEllipsisRangeAtlasMap
  , superEllipsisRangeInsertion
  )

-- | A value that can supply the nonempty indexed Atlas map on the left of
-- access.  Empty insertion maps deliberately have no indexed form.
class AccessMapOperand operand where
  type AccessValue operand :: Type
  accessMap :: operand -> Maybe (IndexedAtlasMap (AccessValue operand))

instance AccessMapOperand (IndexedAtlasMap value) where
  type AccessValue (IndexedAtlasMap value) = value
  accessMap = Just

instance AccessMapOperand (SuperEllipsisInsertionMap source) where
  type AccessValue (SuperEllipsisInsertionMap source) = source
  accessMap insertionMap =
    case insertionMap of
      EmptySuperEllipsisInsertionMap _ -> Nothing
      IndexedSuperEllipsisInsertionMap valueMap -> Just valueMap

instance AccessMapOperand (SuperEllipsisInsertion target source) where
  type AccessValue (SuperEllipsisInsertion target source) = source
  accessMap = accessMap . superEllipsisInsertionMap

instance AccessMapOperand (SuperEllipsisRange (target :: Type) scope) where
  type AccessValue (SuperEllipsisRange target scope) =
    SuperEllipsisRangeElement target scope
  accessMap = accessMap . superEllipsisRangeAtlasMap

-- | A selected final-page value together with the insertion source that
-- requested it and its new position in the accessed map.
type role AccessElement representational representational
data AccessElement source value = AccessElement
  { accessElementPosition :: Ordinal
  , accessElementSource :: source
  , accessElementValue :: value
  }
  deriving (Eq, Show)

-- | An access operand supplies an ordered insertion into a super-ellipsis
-- target.  A formulation denotes the identity insertion of its complete
-- underlying range; it is never truncated to fit the accessed map.
class AccessOperand operand where
  type AccessSource operand :: Type
  withAccessOperandInsertion
    :: operand
    -> (forall (target :: Type).
          SuperEllipsisInsertion target (AccessSource operand) -> result)
    -> result

instance AccessOperand
    (SuperEllipsisInsertion (target :: Type) source) where
  type AccessSource (SuperEllipsisInsertion target source) = source
  withAccessOperandInsertion insertion useInsertion =
    useInsertion insertion

instance AccessOperand (SuperEllipsisRange (target :: Type) scope) where
  type AccessSource (SuperEllipsisRange target scope) =
    SuperEllipsisRangeElement target scope
  withAccessOperandInsertion valueRange useInsertion =
    useInsertion (superEllipsisRangeInsertion valueRange)

instance SuperEllipsisTarget target =>
    AccessOperand (StableConfederalData target) where
  type AccessSource (StableConfederalData target) =
    SuperEllipsisTerminal target
  withAccessOperandInsertion _ useInsertion =
    useInsertion
      (fullSuperEllipsisInsertion superEllipsisTargetRank)

-- | Access final-page indices in insertion-chain order.  In particular, the
-- insertion's image need not be monotone, so this operation can reorder the
-- source Atlas's values.
accessOperator
  :: (AccessMapOperand mapOperand, AccessOperand operand)
  => mapOperand
  -> operand
  -> Maybe
       (IndexedAtlasMap
         (AccessElement (AccessSource operand) (AccessValue mapOperand)))
accessOperator mapOperand operand = do
  valueAtlas <- accessMap mapOperand
  withAccessOperandInsertion operand (accessInsertionOperator valueAtlas)

accessInsertionOperator
  :: IndexedAtlasMap value
  -> SuperEllipsisInsertion target source
  -> Maybe (IndexedAtlasMap (AccessElement source value))
accessInsertionOperator valueAtlas insertion = do
  validateFits
  firstSource <- superEllipsisInsertionFirst insertion
  first <- selectedValue firstSource
  pure (indexedAtlasMapFromChain first selectedChain selectedDominion)
  where
    insertionChain = superEllipsisInsertionChain insertion
    insertionRank = superEllipsisInsertionRank insertion
    targetOrderType = superEllipsisRankOrderType insertionRank
    mapOrderType = chainOrderType (indexedAtlasChain valueAtlas)

    validateFits
      | targetOrderType == mapOrderType
          || ordinalLT targetOrderType mapOrderType = Just ()
      | otherwise = do
          finiteOrderType <- naturalAtOrdinal (chainOrderType insertionChain)
          validateFinite 0 finiteOrderType

    validateFinite position cardinality
      | position == cardinality = Just ()
      | otherwise = do
          sourceIndex <- chainIndex insertionChain (finiteOrdinal position)
          _ <- selectedValue (chainObjectAt sourceIndex)
          validateFinite (position + 1) cardinality

    selectedValue source = do
      value <- indexedAtlasValueAtOrdinal
        valueAtlas
        (superEllipsisInsertionPosition insertion source)
      pure
        (AccessElement
          (chainPosition insertionChain source)
          source
          value)

    selectedChain =
      chain
        (chainOrderType insertionChain)
        accessElementPosition
        (\position -> do
          sourceIndex <- chainIndex insertionChain position
          selectedValue (chainObjectAt sourceIndex))
        (const ())
        (\_ _ -> ())
        (const ())

    targetDominion = superEllipsisDominion insertionRank
    selectedDominion =
      dominion
        (rank targetDominion
          . applySuperEllipsisInsertion insertion
          . accessElementSource)
        (\valueRank -> do
          terminal <- unrank targetDominion valueRank
          source <- superEllipsisInsertionPreimage insertion terminal
          selectedValue source)
        (const ())
