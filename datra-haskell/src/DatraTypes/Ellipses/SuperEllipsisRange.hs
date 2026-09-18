{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

-- | Ordered ordinal ranges inside a finite-rank 'SuperEllipsis'.
module SuperEllipsisRange
  ( SuperEllipsisRange
  , SuperEllipsisRangeTarget (..)
  , SuperEllipsisRangeElement
  , SuperEllipsisRangeMap
  , SuperEllipsisRangeConcatValues
  , SuperEllipsisRangeConcatValue
  , SuperEllipsisRangeConcatOrderedMap
  , SuperEllipsisRangeConcat
  , superEllipsisRange
  , superEllipsisRangeRank
  , superEllipsisRangeStart
  , superEllipsisRangeTarget
  , superEllipsisRangeLowerBound
  , superEllipsisRangeUpperBound
  , superEllipsisRangeOrderType
  , superEllipsisRangeElement
  , superEllipsisRangeElementPosition
  , superEllipsisRangeInsertion
  , superEllipsisRangeOrderedMap
  , superEllipsisRangeMap
  , concatSuperEllipsisRangeOrderedMaps
  , concatSuperEllipsisRanges
  , mergeSuperEllipsisRanges
  , superEllipsisRangeConcatMap
  , superEllipsisRangeConcatValue
  , superEllipsisRangeConcatInsertion
  , superEllipsisRangeConcatOrderedMap
  , concatSuperEllipsisRangeInsertion
  ) where

import AtlasConfederation
  ( AtlasConfederation
  , AtlasConfederationObject
  , MergedAtlasConfederationScope
  , SingletonAtlasConfederationScope
  , identityAtlasConfederationHom
  , singletonAtlasConfederation
  )
import Chain (Chain, chain, sumChains)
import ChainedDominionAtlas
  ( ChainedDominionAtlasObject
  , chainedDominionAtlas
  , chainedDominionAtlasMap
  )
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  , ordinalLT
  , splitFiniteTail
  , subtractOrdinal
  )
import Dominion (Dominion, dominion, rank, unrank)
import MapOperators.ConcatOperator
  ( Concat (ConcatResult, concatOperands)
  , ConcatOperatorValue
  , ConcatOperatorValues
  , concatValue
  )
import MapOperators.IndexedAtlasMap (indexedAtlasMapFromChain)
import MapOperators.OrderedAtlasMap
  ( HasOrderedAtlasMap (..)
  , OrderedAtlasMap (..)
  )
import MapOperators.Syntax.ConcatOperatorSyntax ((<.>))
import StableConfederalData
  ( EmbeddedAtlasMap
  , StableConfederalData
  , embedAtlasMap
  )
import SuperEllipsis
  ( SuperEllipsisRank
  , superEllipsisDominion
  , superEllipsisRankOrderType
  , superEllipsisTerminal
  , superEllipsisTerminalPosition
  , superEllipsisZeroTerminal
  )
import SuperEllipsisInsertion
  ( SuperEllipsisInsertion
  , HasSuperEllipsisInsertion (..)
  , mergeDisjointSuperEllipsisInsertions
  , superEllipsisInsertion
  , superEllipsisInsertionOrderedMap
  )

data SuperEllipsisRangeTarget
  = GivenTarget Ordinal
  | MinusSign
  | PlusSign
  deriving (Eq, Show)

type role SuperEllipsisRange nominal nominal
data SuperEllipsisRange (target :: Type) (scope :: Type) = SuperEllipsisRange
  { superEllipsisRangeRank :: SuperEllipsisRank target
  , superEllipsisRangeStart :: Ordinal
  , superEllipsisRangeTarget :: SuperEllipsisRangeTarget
  }

superEllipsisRangeLowerBound
  :: SuperEllipsisRange target scope
  -> Ordinal
superEllipsisRangeLowerBound = superEllipsisRangeStart

superEllipsisRangeUpperBound
  :: SuperEllipsisRange target scope
  -> Maybe Ordinal
superEllipsisRangeUpperBound valueRange =
  case superEllipsisRangeTarget valueRange of
    GivenTarget target -> Just target
    MinusSign -> Nothing
    PlusSign -> Nothing

type role SuperEllipsisRangeElement nominal nominal
newtype SuperEllipsisRangeElement target (scope :: Type) =
  SuperEllipsisRangeElement
    { superEllipsisRangeElementPosition :: Ordinal
    }
  deriving (Eq, Show)

type SuperEllipsisRangeMap target scope =
  EmbeddedAtlasMap
    (ChainedDominionAtlasObject (SuperEllipsisRangeElement target scope))

type SuperEllipsisRangeConfederationScope target scope =
  SingletonAtlasConfederationScope
    (ChainedDominionAtlasObject (SuperEllipsisRangeElement target scope))

type SuperEllipsisRangeConcatValues target leftScope rightScope =
  ConcatOperatorValues
    (SuperEllipsisRangeMap target leftScope)
    (SuperEllipsisRangeMap target rightScope)

type SuperEllipsisRangeConcatObject target leftScope rightScope =
  AtlasConfederationObject
    (MergedAtlasConfederationScope
      (SuperEllipsisRangeConfederationScope target leftScope)
      (SuperEllipsisRangeConfederationScope target rightScope))
    (Either () ())

type SuperEllipsisRangeConcatValue target leftScope rightScope =
  ConcatOperatorValue
    (SuperEllipsisRangeMap target leftScope)
    (SuperEllipsisRangeMap target rightScope)
    (SuperEllipsisRangeConcatObject target leftScope rightScope)

type SuperEllipsisRangeConcatOrderedMap target leftScope rightScope =
  OrderedAtlasMap
    (Either
      (SuperEllipsisRangeElement target leftScope)
      (SuperEllipsisRangeElement target rightScope))

data SuperEllipsisRangeConcat
    (target :: Type) leftScope rightScope = SuperEllipsisRangeConcat
  { superEllipsisRangeConcatOrderedMap
      :: SuperEllipsisRangeConcatOrderedMap target leftScope rightScope
  , superEllipsisRangeConcatMap
      :: StableConfederalData
           (SuperEllipsisRangeConcatValues target leftScope rightScope)
  , superEllipsisRangeConcatValue
      :: SuperEllipsisRangeConcatValue target leftScope rightScope
  , superEllipsisRangeConcatInsertion
      :: Maybe
           (SuperEllipsisInsertion
             target
             (Either
               (SuperEllipsisRangeElement target leftScope)
               (SuperEllipsisRangeElement target rightScope)))
  }

instance HasOrderedAtlasMap
    (SuperEllipsisRangeConcat target leftScope rightScope) where
  type OrderedAtlasElement
      (SuperEllipsisRangeConcat target leftScope rightScope) =
    Either
      (SuperEllipsisRangeElement target leftScope)
      (SuperEllipsisRangeElement target rightScope)
  orderedAtlasMap = superEllipsisRangeConcatOrderedMap

-- | Introduce a range after checking both endpoints against its rank.  The
-- first endpoint is always explicit; callers must pass zero rather than omit
-- it.
-- Descending ranges are admitted only when both endpoints have the same
-- limit part, so every step removes one element from a finite tail.
superEllipsisRange
  :: SuperEllipsisRank target
  -> Ordinal
  -> SuperEllipsisRangeTarget
  -> (forall scope. SuperEllipsisRange target scope -> result)
  -> Maybe result
superEllipsisRange valueRank start target useRange = do
  validateStart
  validateTarget
  validateDirection
  pure (useRange (SuperEllipsisRange valueRank start target))
  where
    rankLimit = superEllipsisRankOrderType valueRank

    validateStart
      | ordinalLT start rankLimit = Just ()
      | otherwise = Nothing

    validateTarget =
      case target of
        GivenTarget targetValue
          | targetValue == rankLimit || ordinalLT targetValue rankLimit ->
              Just ()
          | otherwise -> Nothing
        MinusSign -> Just ()
        PlusSign -> Just ()

    validateDirection =
      case target of
        GivenTarget targetValue
          | ordinalLT targetValue start
              && not (sameFiniteBase start targetValue) -> Nothing
          | otherwise -> Just ()
        _ -> Just ()

superEllipsisRangeElement
  :: SuperEllipsisRange target scope
  -> Ordinal
  -> Maybe (SuperEllipsisRangeElement target scope)
superEllipsisRangeElement valueRange position
  | positionInRange valueRange position =
      Just (SuperEllipsisRangeElement position)
  | otherwise = Nothing

rangeDominion
  :: SuperEllipsisRange target scope
  -> Dominion (SuperEllipsisRangeElement target scope)
rangeDominion valueRange = dominion elementRank elementAt (const ())
  where
    targetDominion =
      superEllipsisDominion (superEllipsisRangeRank valueRange)

    elementRank element =
      case superEllipsisTerminal
        (superEllipsisRangeRank valueRange)
        (superEllipsisRangeElementPosition element) of
          Just terminal -> rank targetDominion terminal
          Nothing -> 0

    elementAt valueRank = do
      terminal <- unrank targetDominion valueRank
      superEllipsisRangeElement
        valueRange
        (superEllipsisTerminalPosition terminal)

superEllipsisRangeInsertion
  :: SuperEllipsisRange target scope
  -> SuperEllipsisInsertion
       target (SuperEllipsisRangeElement target scope)
superEllipsisRangeInsertion valueRange =
  superEllipsisInsertion
    (superEllipsisRangeRank valueRange)
    (rangeChain valueRange)
    forward
    backward
    (const ())
  where
    forward element =
      fromMaybe
        (superEllipsisZeroTerminal (superEllipsisRangeRank valueRange))
        (superEllipsisTerminal
          (superEllipsisRangeRank valueRange)
          (superEllipsisRangeElementPosition element))

    backward terminal =
      superEllipsisRangeElement
        valueRange
        (superEllipsisTerminalPosition terminal)

-- | Convert a range through its underlying insertion to the Atlas map it
-- presents.  An empty range becomes the empty map.
superEllipsisRangeOrderedMap
  :: SuperEllipsisRange target scope
  -> OrderedAtlasMap
       (SuperEllipsisRangeElement target scope)
superEllipsisRangeOrderedMap =
  superEllipsisInsertionOrderedMap . superEllipsisRangeInsertion

instance HasSuperEllipsisInsertion (SuperEllipsisRange target scope) where
  type InsertionTarget (SuperEllipsisRange target scope) = target
  type InsertionSource (SuperEllipsisRange target scope) =
    SuperEllipsisRangeElement target scope
  superEllipsisInsertionOf = superEllipsisRangeInsertion

instance HasOrderedAtlasMap (SuperEllipsisRange target scope) where
  type OrderedAtlasElement (SuperEllipsisRange target scope) =
    SuperEllipsisRangeElement target scope
  orderedAtlasMap = superEllipsisRangeOrderedMap

rangeFirstElement
  :: SuperEllipsisRange target scope
  -> Maybe (SuperEllipsisRangeElement target scope)
rangeFirstElement valueRange
  | superEllipsisRangeOrderType valueRange == finiteOrdinal 0 = Nothing
  | otherwise = Just (rangeSeedElement valueRange)

rangeSeedElement
  :: SuperEllipsisRange target scope
  -> SuperEllipsisRangeElement target scope
rangeSeedElement =
  SuperEllipsisRangeElement . superEllipsisRangeStart

rangeChain
  :: SuperEllipsisRange target scope
  -> Chain (SuperEllipsisRangeElement target scope)
rangeChain valueRange =
  chain
    (superEllipsisRangeOrderType valueRange)
    (relativePosition valueRange . superEllipsisRangeElementPosition)
    (elementAtRelativePosition valueRange)
    (const ())
    (\_ _ -> ())
    (const ())

elementAtRelativePosition
  :: SuperEllipsisRange target scope
  -> Ordinal
  -> Maybe (SuperEllipsisRangeElement target scope)
elementAtRelativePosition valueRange offset = do
  absolute <-
    case superEllipsisRangeTarget valueRange of
      GivenTarget target
        | ordinalLT target start -> descendingAt
        | otherwise -> Just (addOrdinals start offset)
      MinusSign -> descendingAt
      PlusSign -> Just (addOrdinals start offset)
  superEllipsisRangeElement valueRange absolute
  where
    start = superEllipsisRangeStart valueRange
    descendingAt = do
      let (base, startTail) = splitFiniteTail start
          (offsetBase, offsetTail) = splitFiniteTail offset
      if offsetBase == finiteOrdinal 0 && offsetTail <= startTail
        then Just
          (addOrdinals base (finiteOrdinal (startTail - offsetTail)))
        else Nothing

relativePosition
  :: SuperEllipsisRange target scope
  -> Ordinal
  -> Ordinal
relativePosition valueRange position =
  case superEllipsisRangeTarget valueRange of
    GivenTarget target
      | ordinalLT target start -> descendingDifference
      | otherwise -> ascendingDifference
    MinusSign -> descendingDifference
    PlusSign -> ascendingDifference
  where
    start = superEllipsisRangeStart valueRange
    ascendingDifference =
      fromMaybe (finiteOrdinal 0) (subtractOrdinal start position)

    descendingDifference =
      fromMaybe (finiteOrdinal 0) (finiteTailDifference start position)

superEllipsisRangeOrderType
  :: SuperEllipsisRange target scope
  -> Ordinal
superEllipsisRangeOrderType valueRange =
  case superEllipsisRangeTarget valueRange of
    GivenTarget target
      | ordinalLT target start ->
          fromMaybe (finiteOrdinal 0) (finiteTailDifference start target)
      | otherwise -> ordinalDifference start target
    MinusSign ->
      let (_, finiteTail) = splitFiniteTail start
      in finiteOrdinal (finiteTail + 1)
    PlusSign ->
      ordinalDifference
        start
        (superEllipsisRankOrderType (superEllipsisRangeRank valueRange))
  where
    start = superEllipsisRangeStart valueRange
    ordinalDifference left right =
      fromMaybe (finiteOrdinal 0) (subtractOrdinal left right)

rangeAtlas
  :: SuperEllipsisRange target scope
  -> AtlasConfederation
       (SuperEllipsisRangeConfederationScope target scope) ()
rangeAtlas valueRange =
  singletonAtlasConfederation
    (chainedDominionAtlas
      (rangeSeedElement valueRange)
      (rangeChain valueRange)
      (rangeDominion valueRange))

superEllipsisRangeMap
  :: SuperEllipsisRange target scope
  -> StableConfederalData (SuperEllipsisRangeMap target scope)
superEllipsisRangeMap valueRange =
  embedAtlasMap
    (chainedDominionAtlasMap
      (rangeSeedElement valueRange)
      (rangeChain valueRange)
      (rangeDominion valueRange))

rangeConcatValue
  :: SuperEllipsisRange target leftScope
  -> SuperEllipsisRange target rightScope
  -> SuperEllipsisRangeConcatValue target leftScope rightScope
rangeConcatValue first second =
  concatValue
    (rangeAtlas first)
    (rangeAtlas second)
    identityAtlasConfederationHom
    identityAtlasConfederationHom

-- | Concatenate two ranges as an Atlas map, retaining repeated target
-- positions as distinct left and right values.  This conversion is valid
-- whether or not the two ranges can also be merged as one insertion.
concatSuperEllipsisRangeOrderedMaps
  :: SuperEllipsisRange target leftScope
  -> SuperEllipsisRange target rightScope
  -> SuperEllipsisRangeConcatOrderedMap target leftScope rightScope
concatSuperEllipsisRangeOrderedMaps first second =
  case (rangeFirstElement first, rangeFirstElement second) of
    (Nothing, Nothing) -> EmptyOrderedAtlasMap
    (Just firstValue, _) -> indexed (Left firstValue)
    (Nothing, Just secondValue) -> indexed (Right secondValue)
  where
    valueChain = sumChains (rangeChain first) (rangeChain second)
    valueDominion =
      sumDominions (rangeDominion first) (rangeDominion second)
    indexed firstValue =
      NonEmptyOrderedAtlasMap
        (indexedAtlasMapFromChain firstValue valueChain valueDominion)

sumDominions
  :: Dominion left
  -> Dominion right
  -> Dominion (Either left right)
sumDominions left right =
  dominion sumRank sumUnrank (const ())
  where
    sumRank (Left value) = 2 * rank left value
    sumRank (Right value) = 2 * rank right value + 1

    sumUnrank valueRank
      | even valueRank = Left <$> unrank left (valueRank `div` 2)
      | otherwise = Right <$> unrank right (valueRank `div` 2)

concatSuperEllipsisRanges
  :: SuperEllipsisRange target leftScope
  -> SuperEllipsisRange target rightScope
  -> SuperEllipsisRangeConcat target leftScope rightScope
concatSuperEllipsisRanges first second =
  let atlasMap = concatSuperEllipsisRangeOrderedMaps first second
      valueMap =
        superEllipsisRangeMap first <.> superEllipsisRangeMap second
      value = rangeConcatValue first second
      insertion
        | rangesOverlap first second = Nothing
        | otherwise = Just
            (mergeDisjointSuperEllipsisInsertions
              (superEllipsisRangeInsertion first)
              (superEllipsisRangeInsertion second))
  in SuperEllipsisRangeConcat atlasMap valueMap value insertion

mergeSuperEllipsisRanges
  :: SuperEllipsisRange target leftScope
  -> SuperEllipsisRange target rightScope
  -> SuperEllipsisRangeConcat target leftScope rightScope
mergeSuperEllipsisRanges = concatSuperEllipsisRanges

concatSuperEllipsisRangeInsertion
  :: SuperEllipsisRange target leftScope
  -> SuperEllipsisRange target rightScope
  -> Maybe
       (SuperEllipsisInsertion
         target
         (Either
           (SuperEllipsisRangeElement target leftScope)
           (SuperEllipsisRangeElement target rightScope)))
concatSuperEllipsisRangeInsertion first second =
  superEllipsisRangeConcatInsertion
    (concatSuperEllipsisRanges first second)

positionInRange
  :: SuperEllipsisRange target scope
  -> Ordinal
  -> Bool
positionInRange valueRange position =
  case superEllipsisRangeTarget valueRange of
    GivenTarget target
      | ordinalLT start target ->
          not (ordinalLT position start) && ordinalLT position target
      | ordinalLT target start ->
          sameFiniteBase start position
            && ordinalLT target position
            && not (ordinalLT start position)
      | otherwise -> False
    MinusSign ->
      sameFiniteBase start position && not (ordinalLT start position)
    PlusSign ->
      not (ordinalLT position start)
        && ordinalLT position
             (superEllipsisRankOrderType
               (superEllipsisRangeRank valueRange))
  where
    start = superEllipsisRangeStart valueRange

rangesOverlap
  :: SuperEllipsisRange target leftScope
  -> SuperEllipsisRange target rightScope
  -> Bool
rangesOverlap first second =
  case (rangeImageBounds first, rangeImageBounds second) of
    (Nothing, _) -> False
    (_, Nothing) -> False
    (Just (firstLower, firstUpper), Just (secondLower, secondUpper)) ->
      ordinalLT firstLower secondUpper && ordinalLT secondLower firstUpper

rangeImageBounds
  :: SuperEllipsisRange target scope
  -> Maybe (Ordinal, Ordinal)
rangeImageBounds valueRange =
  case superEllipsisRangeTarget valueRange of
    GivenTarget target
      | ordinalLT start target -> Just (start, target)
      | ordinalLT target start ->
          Just (successor target, successor start)
      | otherwise -> Nothing
    MinusSign ->
      let (base, _) = splitFiniteTail start
      in Just (base, successor start)
    PlusSign ->
      Just
        ( start
        , superEllipsisRankOrderType (superEllipsisRangeRank valueRange)
        )
  where
    start = superEllipsisRangeStart valueRange
    successor value = addOrdinals value (finiteOrdinal 1)

sameFiniteBase :: Ordinal -> Ordinal -> Bool
sameFiniteBase left right =
  let (leftBase, _) = splitFiniteTail left
      (rightBase, _) = splitFiniteTail right
  in leftBase == rightBase

finiteTailDifference :: Ordinal -> Ordinal -> Maybe Ordinal
finiteTailDifference left right =
  let (leftBase, leftTail) = splitFiniteTail left
      (rightBase, rightTail) = splitFiniteTail right
  in if leftBase == rightBase && rightTail <= leftTail
      then Just (finiteOrdinal (leftTail - rightTail))
      else Nothing

instance
    Concat
      (SuperEllipsisRange target leftScope)
      (SuperEllipsisRange target rightScope) where
  type ConcatResult
      (SuperEllipsisRange target leftScope)
      (SuperEllipsisRange target rightScope) =
        SuperEllipsisRangeConcat target leftScope rightScope
  concatOperands = concatSuperEllipsisRanges
