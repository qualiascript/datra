{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Ordered ordinal ranges inside a finite-rank 'SuperEllipsis'.
module SuperEllipsisRange
  ( SuperEllipsisRange
  , SuperEllipsisRangeTarget (..)
  , SuperEllipsisRangeError (..)
  , SuperEllipsisRangeDescription (..)
  , SuperEllipsisRangeConcatAnalysis (..)
  , SuperEllipsisRangeConcatError (..)
  , SuperEllipsisRangeElement
  , SuperEllipsisRangeMember
  , SuperEllipsisRangeMap
  , SuperEllipsisRangeConcatValues
  , SuperEllipsisRangeConcatValue
  , SuperEllipsisRangeConcatOrderedMap
  , SuperEllipsisRangeConcat
  , superEllipsisRange
  , superEllipsisRangeEither
  , superEllipsisSingletonRange
  , finiteSuperEllipsisSingletonRange
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
  , superEllipsisRangeConcatInsertionResult
  , superEllipsisRangeConcatOrderedMap
  , concatSuperEllipsisRangeInsertion
  , concatSuperEllipsisRangeInsertionEither
  , describeSuperEllipsisRange
  , analyzeSuperEllipsisRangeConcat
  , analyzeSuperEllipsisRangeDescriptions
  , validateSuperEllipsisRangeDescriptions
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
  ( ChainedDominionAtlas
  , ChainedDominionAtlasObject
  , withChainedDominionAtlas
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
import Dot (Dot)
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
import Numeric.Natural (Natural)
import StableConfederalData
  ( EmbeddedAtlasMap
  , StableConfederalData
  , embedAtlasMap
  )
import SuperEllipsis
  ( MinimalSuperEllipsisOrdinal
  , SuperEllipsis
  , SuperEllipsisRank
  , dotSuperEllipsisRank
  , minimalSuperEllipsisOrdinalRank
  , minimalSuperEllipsisOrdinalValue
  , superEllipsisDominion
  , superEllipsisRankOrderType
  , superEllipsisTerminal
  , superEllipsisTerminalPosition
  , superEllipsisZeroTerminal
  , nextSuperEllipsisRank
  )
import SuperEllipsisInsertion
  ( SuperEllipsisInsertion
  , HasSuperEllipsisInsertion (..)
  , mergeDisjointSuperEllipsisInsertions
  , superEllipsisInsertion
  , superEllipsisInsertionOrderedMap
  )
import SuperEllipsisRange.Description
  ( SuperEllipsisRangeConcatAnalysis (..)
  , SuperEllipsisRangeConcatError (..)
  , SuperEllipsisRangeDescription (..)
  , SuperEllipsisRangeTarget (..)
  , analyzeSuperEllipsisRangeDescriptions
  , finiteTailDifference
  , rangeDescriptionOrderType
  , sameFiniteBase
  , validateSuperEllipsisRangeDescriptions
  )

-- | Reasons a range cannot be constructed at its selected rank.
data SuperEllipsisRangeError
  = SuperEllipsisRangeStartOutsideRank Ordinal Ordinal
  | SuperEllipsisRangeTargetOutsideRank Ordinal Ordinal
  | SuperEllipsisRangeInvalidDescendingBounds Ordinal Ordinal
  deriving (Eq, Show)

-- | Bounds are independent of the retained Atlas allocated from them.
data RangeDefinition target = RangeDefinition
  { definitionRank :: SuperEllipsisRank target
  , definitionStart :: Ordinal
  , definitionTarget :: SuperEllipsisRangeTarget
  }

data RangeScope owner pages membership

type family RangeOwner scope where
  RangeOwner (RangeScope owner pages membership) = owner
type family RangePages scope where
  RangePages (RangeScope owner pages membership) = pages
type family RangeMembership scope where
  RangeMembership (RangeScope owner pages membership) = membership

type role SuperEllipsisRange nominal nominal
data SuperEllipsisRange (target :: Type) (scope :: Type) = SuperEllipsisRange
  { rangeDefinition :: RangeDefinition target
  , rangeOwner :: ChainedDominionAtlas (RangeOwner scope) (RangePages scope)
      (SuperEllipsisRangeElement target (RangeMembership scope))
  }

superEllipsisRangeRank :: SuperEllipsisRange target scope -> SuperEllipsisRank target
superEllipsisRangeRank = definitionRank . rangeDefinition

superEllipsisRangeStart :: SuperEllipsisRange target scope -> Ordinal
superEllipsisRangeStart = definitionStart . rangeDefinition

superEllipsisRangeTarget :: SuperEllipsisRange target scope -> SuperEllipsisRangeTarget
superEllipsisRangeTarget = definitionTarget . rangeDefinition

-- | The callback hides both allocation scopes and the element membership tag.
withRangeDefinition :: RangeDefinition target
  -> (forall scope. SuperEllipsisRange target scope -> result) -> result
withRangeDefinition definition useRange =
  withChainedDominionAtlas (definitionSeed definition) (definitionChain definition)
    (definitionDominion definition) $ \owner ->
      useRange (retainRange definition owner)

retainRange :: RangeDefinition target -> ChainedDominionAtlas owner pages (SuperEllipsisRangeElement target membership)
  -> SuperEllipsisRange target (RangeScope owner pages membership)
retainRange = SuperEllipsisRange

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

-- | The element carrier associated with a particular retained range.
type SuperEllipsisRangeMember target scope = SuperEllipsisRangeElement target (RangeMembership scope)

type role SuperEllipsisRangeElement nominal nominal
newtype SuperEllipsisRangeElement target (scope :: Type) =
  SuperEllipsisRangeElement
    { superEllipsisRangeElementPosition :: Ordinal
    }
  deriving (Eq, Show)

type SuperEllipsisRangeMap target scope =
  EmbeddedAtlasMap
    (ChainedDominionAtlasObject (RangeOwner scope) (RangePages scope) (SuperEllipsisRangeMember target scope))

type SuperEllipsisRangeConfederationScope target scope =
  SingletonAtlasConfederationScope
    (ChainedDominionAtlasObject (RangeOwner scope) (RangePages scope) (SuperEllipsisRangeMember target scope))

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
      (SuperEllipsisRangeMember target leftScope)
      (SuperEllipsisRangeMember target rightScope))

data SuperEllipsisRangeConcat
    (target :: Type) leftScope rightScope = SuperEllipsisRangeConcat
  { superEllipsisRangeConcatOrderedMap
      :: SuperEllipsisRangeConcatOrderedMap target leftScope rightScope
  , superEllipsisRangeConcatMap
      :: StableConfederalData
           (SuperEllipsisRangeConcatValues target leftScope rightScope)
  , superEllipsisRangeConcatValue
      :: SuperEllipsisRangeConcatValue target leftScope rightScope
  , superEllipsisRangeConcatInsertionResult
      :: Either
           SuperEllipsisRangeConcatError
           (SuperEllipsisInsertion
             target
             (Either
               (SuperEllipsisRangeMember target leftScope)
               (SuperEllipsisRangeMember target rightScope)))
  }

instance HasOrderedAtlasMap
    (SuperEllipsisRangeConcat target leftScope rightScope) where
  type OrderedAtlasElement
      (SuperEllipsisRangeConcat target leftScope rightScope) =
    Either
      (SuperEllipsisRangeMember target leftScope)
      (SuperEllipsisRangeMember target rightScope)
  orderedAtlasMap = superEllipsisRangeConcatOrderedMap

-- | Compatibility projection for callers that do not need a diagnostic.
superEllipsisRangeConcatInsertion
  :: SuperEllipsisRangeConcat target leftScope rightScope
  -> Maybe
       (SuperEllipsisInsertion
         target
         (Either
           (SuperEllipsisRangeMember target leftScope)
           (SuperEllipsisRangeMember target rightScope)))
superEllipsisRangeConcatInsertion value =
  case superEllipsisRangeConcatInsertionResult value of
    Left _ -> Nothing
    Right insertion -> Just insertion

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
superEllipsisRange valueRank start target useRange =
  case superEllipsisRangeEither valueRank start target useRange of
    Left _ -> Nothing
    Right result -> Just result

-- | Detailed variant of 'superEllipsisRange'.
superEllipsisRangeEither
  :: SuperEllipsisRank target
  -> Ordinal
  -> SuperEllipsisRangeTarget
  -> (forall scope. SuperEllipsisRange target scope -> result)
  -> Either SuperEllipsisRangeError result
superEllipsisRangeEither valueRank start target useRange = do
  validateStart
  validateTarget
  validateDirection
  pure (withRangeDefinition (RangeDefinition valueRank start target) useRange)
  where
    rankLimit = superEllipsisRankOrderType valueRank

    validateStart
      | ordinalLT start rankLimit = Right ()
      | otherwise =
          Left (SuperEllipsisRangeStartOutsideRank start rankLimit)

    validateTarget =
      case target of
        GivenTarget targetValue
          | targetValue == rankLimit || ordinalLT targetValue rankLimit ->
              Right ()
          | otherwise ->
              Left
                (SuperEllipsisRangeTargetOutsideRank targetValue rankLimit)
        MinusSign -> Right ()
        PlusSign -> Right ()

    validateDirection =
      case target of
        GivenTarget targetValue
          | ordinalLT targetValue start
              && not (sameFiniteBase start targetValue) ->
                  Left
                    (SuperEllipsisRangeInvalidDescendingBounds
                      start targetValue)
          | otherwise -> Right ()
        _ -> Right ()

-- | Construct the singleton range certified by a minimal ordinal/rank pair.
-- Its successor cannot exceed that rank's limit, so no failure case is
-- exposed to callers.
superEllipsisSingletonRange
  :: MinimalSuperEllipsisOrdinal target
  -> (forall scope. SuperEllipsisRange target scope -> result)
  -> result
superEllipsisSingletonRange minimalValue useRange =
  withRangeDefinition
    (RangeDefinition
      (minimalSuperEllipsisOrdinalRank minimalValue)
      value
      (GivenTarget (addOrdinals value (finiteOrdinal 1)))) useRange
  where
    value = minimalSuperEllipsisOrdinalValue minimalValue

-- | Total singleton construction for a finite natural at rank one.
finiteSuperEllipsisSingletonRange
  :: Natural
  -> (forall scope.
       SuperEllipsisRange (SuperEllipsis Dot) scope
       -> result)
  -> result
finiteSuperEllipsisSingletonRange value useRange =
  withRangeDefinition
    (RangeDefinition
      (nextSuperEllipsisRank dotSuperEllipsisRank)
      (finiteOrdinal value)
      (GivenTarget (finiteOrdinal (value + 1)))) useRange

superEllipsisRangeElement :: SuperEllipsisRange target scope -> Ordinal
  -> Maybe (SuperEllipsisRangeMember target scope)
superEllipsisRangeElement = definitionElement . rangeDefinition

rangeDominion :: SuperEllipsisRange target scope -> Dominion (SuperEllipsisRangeMember target scope)
rangeDominion = definitionDominion . rangeDefinition

rangeSeedElement :: SuperEllipsisRange target scope -> SuperEllipsisRangeMember target scope
rangeSeedElement = definitionSeed . rangeDefinition

rangeChain :: SuperEllipsisRange target scope -> Chain (SuperEllipsisRangeMember target scope)
rangeChain = definitionChain . rangeDefinition

superEllipsisRangeOrderType :: SuperEllipsisRange target scope -> Ordinal
superEllipsisRangeOrderType = definitionOrderType . rangeDefinition

describeSuperEllipsisRange :: SuperEllipsisRange target scope -> SuperEllipsisRangeDescription
describeSuperEllipsisRange = describeDefinition . rangeDefinition

definitionElement
  :: RangeDefinition target
  -> Ordinal
  -> Maybe (SuperEllipsisRangeElement target scope)
definitionElement valueRange position
  | definitionContains valueRange position =
      Just (SuperEllipsisRangeElement position)
  | otherwise = Nothing

definitionDominion
  :: RangeDefinition target
  -> Dominion (SuperEllipsisRangeElement target scope)
definitionDominion valueRange = dominion elementRank elementAt (const ())
  where
    targetDominion =
      superEllipsisDominion (definitionRank valueRange)

    elementRank element =
      case superEllipsisTerminal
        (definitionRank valueRange)
        (superEllipsisRangeElementPosition element) of
          Just terminal -> rank targetDominion terminal
          Nothing -> 0

    elementAt valueRank = do
      terminal <- unrank targetDominion valueRank
      definitionElement
        valueRange
        (superEllipsisTerminalPosition terminal)

superEllipsisRangeInsertion
  :: SuperEllipsisRange target scope
  -> SuperEllipsisInsertion
       target (SuperEllipsisRangeMember target scope)
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
       (SuperEllipsisRangeMember target scope)
superEllipsisRangeOrderedMap =
  superEllipsisInsertionOrderedMap . superEllipsisRangeInsertion

instance HasSuperEllipsisInsertion (SuperEllipsisRange target scope) where
  type InsertionTarget (SuperEllipsisRange target scope) = target
  type InsertionSource (SuperEllipsisRange target scope) =
    SuperEllipsisRangeMember target scope
  superEllipsisInsertionOf = superEllipsisRangeInsertion

instance HasOrderedAtlasMap (SuperEllipsisRange target scope) where
  type OrderedAtlasElement (SuperEllipsisRange target scope) =
    SuperEllipsisRangeMember target scope
  orderedAtlasMap = superEllipsisRangeOrderedMap

rangeFirstElement
  :: SuperEllipsisRange target scope
  -> Maybe (SuperEllipsisRangeMember target scope)
rangeFirstElement valueRange
  | superEllipsisRangeOrderType valueRange == finiteOrdinal 0 = Nothing
  | otherwise = Just (rangeSeedElement valueRange)

definitionSeed
  :: RangeDefinition target
  -> SuperEllipsisRangeElement target scope
definitionSeed =
  SuperEllipsisRangeElement . definitionStart

definitionChain
  :: RangeDefinition target
  -> Chain (SuperEllipsisRangeElement target scope)
definitionChain valueRange =
  chain
    (definitionOrderType valueRange)
    (definitionRelativePosition valueRange . superEllipsisRangeElementPosition)
    (definitionElementAt valueRange)
    (const ())
    (\_ _ -> ())
    (const ())

definitionElementAt
  :: RangeDefinition target
  -> Ordinal
  -> Maybe (SuperEllipsisRangeElement target scope)
definitionElementAt valueRange offset = do
  absolute <-
    case definitionTarget valueRange of
      GivenTarget target
        | ordinalLT target start -> descendingAt
        | otherwise -> Just (addOrdinals start offset)
      MinusSign -> descendingAt
      PlusSign -> Just (addOrdinals start offset)
  definitionElement valueRange absolute
  where
    start = definitionStart valueRange
    descendingAt = do
      let (base, startTail) = splitFiniteTail start
          (offsetBase, offsetTail) = splitFiniteTail offset
      if offsetBase == finiteOrdinal 0 && offsetTail <= startTail
        then Just
          (addOrdinals base (finiteOrdinal (startTail - offsetTail)))
        else Nothing

definitionRelativePosition
  :: RangeDefinition target
  -> Ordinal
  -> Ordinal
definitionRelativePosition valueRange position =
  case definitionTarget valueRange of
    GivenTarget target
      | ordinalLT target start -> descendingDifference
      | otherwise -> ascendingDifference
    MinusSign -> descendingDifference
    PlusSign -> ascendingDifference
  where
    start = definitionStart valueRange
    ascendingDifference =
      fromMaybe (finiteOrdinal 0) (subtractOrdinal start position)

    descendingDifference =
      fromMaybe (finiteOrdinal 0) (finiteTailDifference start position)

definitionOrderType
  :: RangeDefinition target
  -> Ordinal
definitionOrderType valueRange =
  rangeDescriptionOrderType (describeDefinition valueRange)

rangeAtlas
  :: SuperEllipsisRange target scope
  -> AtlasConfederation
       (SuperEllipsisRangeConfederationScope target scope) ()
rangeAtlas valueRange =
  singletonAtlasConfederation
    (chainedDominionAtlas (rangeOwner valueRange))

superEllipsisRangeMap
  :: SuperEllipsisRange target scope
  -> StableConfederalData (SuperEllipsisRangeMap target scope)
superEllipsisRangeMap valueRange =
  embedAtlasMap
    (chainedDominionAtlasMap (rangeOwner valueRange))

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
        concatOperands
          (superEllipsisRangeMap first)
          (superEllipsisRangeMap second)
      value = rangeConcatValue first second
      insertion = concatSuperEllipsisRangeInsertionEither first second
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
           (SuperEllipsisRangeMember target leftScope)
           (SuperEllipsisRangeMember target rightScope)))
concatSuperEllipsisRangeInsertion first second =
  case concatSuperEllipsisRangeInsertionEither first second of
    Left _ -> Nothing
    Right insertion -> Just insertion

-- | Detailed insertion projection for a range concatenation. Overlapping
-- ranges still form a valid ordered map, but cannot form an injective
-- selection for map access.
concatSuperEllipsisRangeInsertionEither
  :: SuperEllipsisRange target leftScope
  -> SuperEllipsisRange target rightScope
  -> Either
       SuperEllipsisRangeConcatError
       (SuperEllipsisInsertion
         target
         (Either
           (SuperEllipsisRangeMember target leftScope)
           (SuperEllipsisRangeMember target rightScope)))
concatSuperEllipsisRangeInsertionEither first second =
  case analyzeSuperEllipsisRangeConcat first second of
    RangeConcatOverlapping
        firstDescription secondDescription lower upper ->
      Left
        (SuperEllipsisRangesOverlap
          firstDescription secondDescription lower upper)
    _ ->
      Right
        (mergeDisjointSuperEllipsisInsertions
          (superEllipsisRangeInsertion first)
          (superEllipsisRangeInsertion second))

describeDefinition
  :: RangeDefinition target
  -> SuperEllipsisRangeDescription
describeDefinition valueRange =
  SuperEllipsisRangeDescription
    { describedRangeRankLimit =
        superEllipsisRankOrderType (definitionRank valueRange)
    , describedRangeStart = definitionStart valueRange
    , describedRangeTarget = definitionTarget valueRange
    }

-- | Analyze an ordered pair without discarding ordering or duplicate-image
-- information. Empty ranges are identities. Adjacent ranges canonicalize
-- only when their traversal directions agree.
analyzeSuperEllipsisRangeConcat
  :: SuperEllipsisRange target leftScope
  -> SuperEllipsisRange target rightScope
  -> SuperEllipsisRangeConcatAnalysis
analyzeSuperEllipsisRangeConcat first second =
  analyzeSuperEllipsisRangeDescriptions
    (describeSuperEllipsisRange first)
    (describeSuperEllipsisRange second)

definitionContains
  :: RangeDefinition target
  -> Ordinal
  -> Bool
definitionContains valueRange position =
  case definitionTarget valueRange of
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
               (definitionRank valueRange))
  where
    start = definitionStart valueRange

instance
    Concat
      (SuperEllipsisRange target leftScope)
      (SuperEllipsisRange target rightScope) where
  type ConcatResult
      (SuperEllipsisRange target leftScope)
      (SuperEllipsisRange target rightScope) =
        SuperEllipsisRangeConcat target leftScope rightScope
  concatOperands = concatSuperEllipsisRanges
