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
  , validateAccessSelection
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
      validateAccessSelection
        targetOrderType
        (chainOrderType insertionChain)
        mapOrderType
        (Just . superEllipsisInsertionPosition insertion . sourceAt)
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

-- | Validate an ordinal-indexed selection independently of its concrete
-- map and insertion witnesses. Existential interpreters can therefore use
-- the same checked access boundary as the statically typed operator.
validateAccessSelection
  :: Ordinal
  -> Ordinal
  -> Ordinal
  -> (Ordinal -> Maybe Ordinal)
  -> Either AccessError ()
validateAccessSelection insertionRankLimit insertionOrderType mapOrderType
    selectedPositionAt
  | insertionRankLimit == mapOrderType
      || ordinalLT insertionRankLimit mapOrderType = Right ()
  | otherwise =
      case naturalAtOrdinal insertionOrderType of
        Nothing ->
          Left
            (AccessInsertionRankExceedsMap
              insertionRankLimit mapOrderType)
        Just cardinality -> validateFinite 0 cardinality
  where
    validateFinite position cardinality
      | position == cardinality = Right ()
      | otherwise =
          case selectedPositionAt (finiteOrdinal position) of
            Nothing -> validateFinite (position + 1) cardinality
            Just selectedPosition
              | ordinalLT selectedPosition mapOrderType ->
                  validateFinite (position + 1) cardinality
              | otherwise ->
                  Left
                    (AccessPositionOutOfBounds
                      selectedPosition mapOrderType)
