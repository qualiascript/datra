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
  , AccessElement
  , accessElementPosition
  , accessElementSource
  , accessElementValue
  , AccessOperand (AccessSource)
  , accessOperator
  ) where

import AtlasMap (AtlasMap)
import Chain
  ( Chain
  , chain
  , chainIndex
  , chainObjectAt
  , chainOrderType
  , chainPosition
  )
import ChainedDominionAtlas
  ( ChainedDominionAtlas
  , ChainedDominionAtlasObject
  , chainedDominionAtlas
  , chainedDominionAtlasMap
  )
import Control.Monad ((>=>))
import DatraOrdinal
  ( Ordinal
  , finiteOrdinal
  , naturalAtOrdinal
  , ordinalLT
  )
import Data.Kind (Type)
import Dominion (Dominion, dominion, rank, unrank)
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
  , applySuperEllipsisInsertion
  , fullSuperEllipsisInsertion
  , superEllipsisInsertionChain
  , superEllipsisInsertionFirst
  , superEllipsisInsertionPosition
  , superEllipsisInsertionPreimage
  , superEllipsisInsertionRank
  )
import Numeric.Natural (Natural)

-- | A nonempty value-indexed Atlas map whose final chain may have any order
-- type below omega to the omega.
type role IndexedAtlasMap nominal
data IndexedAtlasMap value = IndexedAtlasMap
  { indexedAtlasCardinality :: Ordinal
  , indexedAtlasChain :: Chain value
  , indexedAtlasDominion :: Dominion value
  , indexedAtlasAtlas :: ChainedDominionAtlas value
  , indexedAtlasAtlasMap
      :: AtlasMap (ChainedDominionAtlasObject value)
  }

-- | Build a two-page indexed Atlas map from a dense finite dominion.
-- The supplied first value is nonemptiness evidence.
indexedAtlasMap
  :: Natural
  -> value
  -> Dominion value
  -> IndexedAtlasMap value
indexedAtlasMap cardinality first valueDominion =
  indexedAtlasMapFromChain first valueChain valueDominion
  where
    valueChain =
      chain
        (finiteOrdinal cardinality)
        (finiteOrdinal . rank valueDominion)
        (naturalAtOrdinal >=> unrank valueDominion)
        (const ())
        (\_ _ -> ())
        (const ())

-- | Build an indexed Atlas map from an arbitrary nonempty ordinal chain and
-- a countable dominion of the same values.
indexedAtlasMapFromChain
  :: value
  -> Chain value
  -> Dominion value
  -> IndexedAtlasMap value
indexedAtlasMapFromChain first valueChain valueDominion =
  IndexedAtlasMap
    { indexedAtlasCardinality = chainOrderType valueChain
    , indexedAtlasChain = valueChain
    , indexedAtlasDominion = valueDominion
    , indexedAtlasAtlas =
        chainedDominionAtlas first valueChain valueDominion
    , indexedAtlasAtlasMap =
        chainedDominionAtlasMap first valueChain valueDominion
    }

-- | Look up a final-page value by its finite page index.
indexedAtlasValueAt
  :: IndexedAtlasMap value
  -> Natural
  -> Maybe value
indexedAtlasValueAt valueAtlas =
  indexedAtlasValueAtOrdinal valueAtlas . finiteOrdinal

-- | Look up a final-page value by an arbitrary ordinal page index.
indexedAtlasValueAtOrdinal
  :: IndexedAtlasMap value
  -> Ordinal
  -> Maybe value
indexedAtlasValueAtOrdinal valueAtlas position =
  chainObjectAt <$> chainIndex (indexedAtlasChain valueAtlas) position

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
  :: AccessOperand operand
  => IndexedAtlasMap value
  -> operand
  -> Maybe
       (IndexedAtlasMap (AccessElement (AccessSource operand) value))
accessOperator valueAtlas operand =
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
