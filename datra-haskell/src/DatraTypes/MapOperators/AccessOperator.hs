{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

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
  , OrderedAtlasMap (..)
  , HasOrderedAtlasMap (OrderedAtlasElement, orderedAtlasMap)
  , AccessElement
  , accessElementPosition
  , accessElementSource
  , accessElementValue
  , HasSuperEllipsisInsertion
      ( InsertionTarget
      , InsertionSource
      , superEllipsisInsertionOf
      )
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
import MapOperators.OrderedAtlasMap
  ( HasOrderedAtlasMap (..)
  , OrderedAtlasMap (..)
  , orderedAtlasMapIndexed
  )
import SuperEllipsis
  ( superEllipsisDominion
  , superEllipsisRankOrderType
  )
import SuperEllipsisInsertion
  ( HasSuperEllipsisInsertion (..)
  , SuperEllipsisInsertion
  , applySuperEllipsisInsertion
  , superEllipsisInsertionChain
  , superEllipsisInsertionFirst
  , superEllipsisInsertionPosition
  , superEllipsisInsertionPreimage
  , superEllipsisInsertionRank
  )

-- | A selected final-page value together with the insertion source that
-- requested it and its new position in the accessed map.
type role AccessElement representational representational
data AccessElement source value = AccessElement
  { accessElementPosition :: Ordinal
  , accessElementSource :: source
  , accessElementValue :: value
  }
  deriving (Eq, Show)

-- | Access final-page indices in insertion-chain order.  In particular, the
-- insertion's image need not be monotone, so this operation can reorder the
-- source Atlas's values.
accessOperator
  :: (HasOrderedAtlasMap mapOperand, HasSuperEllipsisInsertion operand)
  => mapOperand
  -> operand
  -> Maybe
       (IndexedAtlasMap
         (AccessElement
           (InsertionSource operand)
           (OrderedAtlasElement mapOperand)))
accessOperator mapOperand operand = do
  valueAtlas <- orderedAtlasMapIndexed (orderedAtlasMap mapOperand)
  accessInsertionOperator valueAtlas (superEllipsisInsertionOf operand)

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
