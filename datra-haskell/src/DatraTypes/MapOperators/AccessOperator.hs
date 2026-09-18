{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

-- | Ordered access to the final page of an ordinal-indexed Atlas map.
--
-- A 'SuperEllipsisInsertion' supplies both the absolute final-page indices and
-- the order in which they are requested. Nonempty access constructs a fresh
-- two-page chained Atlas map in precisely that order; an empty source or
-- selection produces 'EmptyOrderedAtlasMap'. Detailed failures explain why a
-- nonempty insertion could not be certified inside the left Atlas.
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
  , orderedAtlasMapCardinality
  , orderedAtlasMapValueAt
  , orderedAtlasMapValueAtOrdinal
  , HasOrderedAtlasMap (OrderedAtlasElement, orderedAtlasMap)
  , AccessElement
  , accessElementPosition
  , accessElementSource
  , accessElementValue
  , AccessError (..)
  , HasSuperEllipsisInsertion
      ( InsertionTarget
      , InsertionSource
      , superEllipsisInsertionOf
      )
  , accessOperator
  , accessOperatorEither
  ) where

import Chain
  ( chain
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
  , orderedAtlasMapCardinality
  , orderedAtlasMapValueAt
  , orderedAtlasMapValueAtOrdinal
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
  , superEllipsisInsertionPosition
  , superEllipsisInsertionPreimage
  , superEllipsisInsertionRank
  , withSuperEllipsisInsertionSources
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

data AccessError
  = AccessInsertionRankExceedsMap Ordinal Ordinal
  | AccessPositionOutOfBounds Ordinal Ordinal
  deriving (Eq, Show)

-- | Access final-page indices in insertion-chain order.  In particular, the
-- insertion's image need not be monotone, so this operation can reorder the
-- source Atlas's values.
accessOperator
  :: (HasOrderedAtlasMap mapOperand, HasSuperEllipsisInsertion operand)
  => mapOperand
  -> operand
  -> Maybe
       (OrderedAtlasMap
         (AccessElement
           (InsertionSource operand)
           (OrderedAtlasElement mapOperand)))
accessOperator mapOperand operand =
  case accessOperatorEither mapOperand operand of
    Left _ -> Nothing
    Right result -> Just result

accessOperatorEither
  :: (HasOrderedAtlasMap mapOperand, HasSuperEllipsisInsertion operand)
  => mapOperand
  -> operand
  -> Either
       AccessError
       (OrderedAtlasMap
         (AccessElement
           (InsertionSource operand)
           (OrderedAtlasElement mapOperand)))
accessOperatorEither mapOperand operand =
  case orderedAtlasMap mapOperand of
    EmptyOrderedAtlasMap -> Right EmptyOrderedAtlasMap
    NonEmptyOrderedAtlasMap valueAtlas ->
      accessInsertionOperatorEither
        valueAtlas
        (superEllipsisInsertionOf operand)

accessInsertionOperatorEither
  :: IndexedAtlasMap value
  -> SuperEllipsisInsertion target source
  -> Either
       AccessError
       (OrderedAtlasMap (AccessElement source value))
accessInsertionOperatorEither valueAtlas insertion =
  withSuperEllipsisInsertionSources
    insertion
    (Right EmptyOrderedAtlasMap) $ \firstSource sourceAt -> do
      validateFits sourceAt
      first <- selectedValue firstSource
      pure
        (NonEmptyOrderedAtlasMap
          (indexedAtlasMapFromChain
            first
            (selectedChain sourceAt)
            selectedDominion))
  where
    insertionChain = superEllipsisInsertionChain insertion
    insertionRank = superEllipsisInsertionRank insertion
    targetOrderType = superEllipsisRankOrderType insertionRank
    mapOrderType = chainOrderType (indexedAtlasChain valueAtlas)

    validateFits sourceAt
      | targetOrderType == mapOrderType
          || ordinalLT targetOrderType mapOrderType = Right ()
      | otherwise =
          case naturalAtOrdinal (chainOrderType insertionChain) of
            Nothing ->
              Left
                (AccessInsertionRankExceedsMap
                  targetOrderType mapOrderType)
            Just finiteOrderType ->
              validateFinite sourceAt 0 finiteOrderType

    validateFinite sourceAt position cardinality
      | position == cardinality = Right ()
      | otherwise = do
          _ <- selectedValue (sourceAt (finiteOrdinal position))
          validateFinite sourceAt (position + 1) cardinality

    selectedValue source =
      let selectedPosition =
            superEllipsisInsertionPosition insertion source
      in case indexedAtlasValueAtOrdinal valueAtlas selectedPosition of
          Nothing ->
            Left (AccessPositionOutOfBounds selectedPosition mapOrderType)
          Just value ->
            Right
              (AccessElement
                (chainPosition insertionChain source)
                source
                value)

    selectedValueMaybe source =
      case selectedValue source of
        Left _ -> Nothing
        Right value -> Just value

    selectedChain sourceAt =
      chain
        (chainOrderType insertionChain)
        accessElementPosition
        (selectedValueMaybe . sourceAt)
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
          selectedValueMaybe source)
        (const ())
