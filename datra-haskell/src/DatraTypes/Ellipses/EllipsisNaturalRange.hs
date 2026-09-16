{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

-- | Ordered half-open natural ranges and their concatenations.
module EllipsisNaturalRange
  ( EllipsisNaturalRange
  , EllipsisNaturalRangeTarget (..)
  , EllipsisNaturalRangeElement
  , EllipsisNaturalRangeMap
  , EllipsisNaturalRangeConcatValues
  , EllipsisNaturalRangeConcatValue
  , EllipsisNaturalRangeConcatKind (..)
  , EllipsisNaturalRangeConcat (..)
  , SomeEllipsisNaturalRangeConcat (..)
  , ellipsisNaturalRange
  , ellipsisNaturalRangeStart
  , ellipsisNaturalRangeTarget
  , ellipsisNaturalRangeLowerBound
  , ellipsisNaturalRangeUpperBound
  , ellipsisNaturalRangeSize
  , ellipsisNaturalRangeElement
  , ellipsisNaturalRangeElementRank
  , ellipsisNaturalRangeInsertion
  , ellipsisNaturalRangeMap
  , concatEllipsisNaturalRanges
  , mergeEllipsisNaturalRanges
  , ellipsisNaturalRangeConcatMap
  , ellipsisNaturalRangeConcatValue
  , ellipsisNaturalRangeConcatInsertion
  , concatEllipsisNaturalRangeInsertion
  ) where

import AtlasConfederation
  ( AtlasConfederation
  , AtlasConfederationObject
  , MergedAtlasConfederationScope
  , SingletonAtlasConfederationScope
  , identityAtlasConfederationHom
  , singletonAtlasConfederation
  )
import ChainedDominionAtlas
  ( ChainedDominionAtlasObject
  , chainedDominionAtlas
  , chainedDominionAtlasMap
  )
import Chain (Chain, chain)
import Control.Monad ((>=>))
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import DatraOrdinal
  ( Ordinal
  , finiteOrdinal
  , naturalAtOrdinal
  , omega
  )
import Dominion (Dominion, dominion)
import Ellipsis (EllipsisTerminal (Terminal), terminalRank)
import EllipsisInsertion
  ( EllipsisInsertion
  , ellipsisInsertion
  , mergeDisjointEllipsisInsertions
  )
import MapOperators.ConcatOperator
  ( Concat (ConcatResult, concatOperands)
  , ConcatOperatorValue
  , ConcatOperatorValues
  , concatValue
  )
import MapOperators.Syntax.ConcatOperatorSyntax ((<.>))
import Numeric.Natural (Natural)
import StableConfederalData
  ( EmbeddedAtlasMap
  , StableConfederalData
  , embedAtlasMap
  )

-- | The second endpoint of a natural range. 'NegativeOne' is the special
-- target immediately below zero, while 'UnboundedTarget' retains the
-- existing upward-infinite range.
data EllipsisNaturalRangeTarget
  = FiniteTarget Natural
  | NegativeOne
  | UnboundedTarget
  deriving (Eq, Show)

-- | An ordered half-open interval of ellipsis ranks. A missing first endpoint
-- denotes zero except when paired with 'NegativeOne', which is rejected by
-- 'ellipsisNaturalRange' because it would mean descending from infinity.
type role EllipsisNaturalRange nominal
data EllipsisNaturalRange (scope :: Type) = EllipsisNaturalRange
  { ellipsisNaturalRangeStart :: Maybe Natural
  , ellipsisNaturalRangeTarget :: EllipsisNaturalRangeTarget
  }

-- | Backward-compatible name for the written first endpoint.
ellipsisNaturalRangeLowerBound
  :: EllipsisNaturalRange scope
  -> Maybe Natural
ellipsisNaturalRangeLowerBound = ellipsisNaturalRangeStart

-- | Recover a finite written target. Both special targets return 'Nothing'.
ellipsisNaturalRangeUpperBound
  :: EllipsisNaturalRange scope
  -> Maybe Natural
ellipsisNaturalRangeUpperBound valueRange =
  case ellipsisNaturalRangeTarget valueRange of
    FiniteTarget target -> Just target
    NegativeOne -> Nothing
    UnboundedTarget -> Nothing

-- | An ellipsis rank known to belong to one particular range.
type role EllipsisNaturalRangeElement nominal
newtype EllipsisNaturalRangeElement (scope :: Type) = EllipsisNaturalRangeElement
  { ellipsisNaturalRangeElementRank :: Natural
  }
  deriving (Eq, Show)

-- | The representable stable-confederal map whose final chain is exactly one
-- natural range.
type EllipsisNaturalRangeMap scope =
  EmbeddedAtlasMap
    (ChainedDominionAtlasObject (EllipsisNaturalRangeElement scope))

type EllipsisNaturalRangeConfederationScope scope =
  SingletonAtlasConfederationScope
    (ChainedDominionAtlasObject (EllipsisNaturalRangeElement scope))

-- | The stable-confederal carrier produced by ordered range concatenation.
type EllipsisNaturalRangeConcatValues leftScope rightScope =
  ConcatOperatorValues
    (EllipsisNaturalRangeMap leftScope)
    (EllipsisNaturalRangeMap rightScope)

type EllipsisNaturalRangeConcatObject leftScope rightScope =
  AtlasConfederationObject
    (MergedAtlasConfederationScope
      (EllipsisNaturalRangeConfederationScope leftScope)
      (EllipsisNaturalRangeConfederationScope rightScope))
    (Either () ())

-- | A concrete value of the ordered concatenation map.
type EllipsisNaturalRangeConcatValue leftScope rightScope =
  ConcatOperatorValue
    (EllipsisNaturalRangeMap leftScope)
    (EllipsisNaturalRangeMap rightScope)
    (EllipsisNaturalRangeConcatObject leftScope rightScope)

-- | Whether an ordered concatenation also has an injective interpretation as
-- a subtype of Ellipsis.
data EllipsisNaturalRangeConcatKind
  = EllipsisInsertionConcat
  | EllipsisMapConcat

-- | An ordered concat map, refined with an Ellipsis insertion exactly when
-- the two absolute range images are disjoint. The map is retained in both
-- constructors because concatenation is ordered even when its image set is
-- the same after swapping operands.
data EllipsisNaturalRangeConcat
    (kind :: EllipsisNaturalRangeConcatKind)
    leftScope
    rightScope where
  ConcatenatedEllipsisInsertion
    :: StableConfederalData
         (EllipsisNaturalRangeConcatValues leftScope rightScope)
    -> EllipsisNaturalRangeConcatValue leftScope rightScope
    -> EllipsisInsertion
         (Either
           (EllipsisNaturalRangeElement leftScope)
           (EllipsisNaturalRangeElement rightScope))
    -> EllipsisNaturalRangeConcat
         'EllipsisInsertionConcat leftScope rightScope
  ConcatenatedEllipsisMap
    :: StableConfederalData
         (EllipsisNaturalRangeConcatValues leftScope rightScope)
    -> EllipsisNaturalRangeConcatValue leftScope rightScope
    -> EllipsisNaturalRangeConcat
         'EllipsisMapConcat leftScope rightScope

-- | Existentially package the capability selected from runtime bounds.
data SomeEllipsisNaturalRangeConcat leftScope rightScope where
  SomeEllipsisNaturalRangeConcat
    :: EllipsisNaturalRangeConcat kind leftScope rightScope
    -> SomeEllipsisNaturalRangeConcat leftScope rightScope

-- | Introduce an ordered range with a fresh abstract scope. Equal finite
-- endpoints produce the empty range; a smaller finite target produces a
-- descending range. The sole invalid form is @..NegativeOne@ with no first
-- endpoint, since that would imply counting down from infinity.
ellipsisNaturalRange
  :: Maybe Natural
  -> EllipsisNaturalRangeTarget
  -> (forall scope. EllipsisNaturalRange scope -> result)
  -> Maybe result
ellipsisNaturalRange Nothing NegativeOne _ = Nothing
ellipsisNaturalRange start target useRange =
  Just (useRange (EllipsisNaturalRange start target))

-- | Refine an absolute ellipsis rank to membership in this range.
ellipsisNaturalRangeElement
  :: EllipsisNaturalRange scope
  -> Natural
  -> Maybe (EllipsisNaturalRangeElement scope)
ellipsisNaturalRangeElement valueRange rankValue
  | rankInRange valueRange rankValue =
      Just (EllipsisNaturalRangeElement rankValue)
  | otherwise = Nothing

ellipsisNaturalRangeDominion
  :: EllipsisNaturalRange scope
  -> Dominion (EllipsisNaturalRangeElement scope)
ellipsisNaturalRangeDominion valueRange =
  dominion
    ellipsisNaturalRangeElementRank
    (ellipsisNaturalRangeElement valueRange)
    (const ())

-- | Insert exactly the terminals in the half-open range into 'Ellipsis'.
ellipsisNaturalRangeInsertion
  :: EllipsisNaturalRange scope
  -> EllipsisInsertion (EllipsisNaturalRangeElement scope)
ellipsisNaturalRangeInsertion valueRange =
  ellipsisInsertion
    (rangeFirstElement valueRange)
    (rangeChain valueRange)
    (Terminal . ellipsisNaturalRangeElementRank)
    (ellipsisNaturalRangeElement valueRange . terminalRank)
    (const ())

rangeFirstElement
  :: EllipsisNaturalRange scope
  -> Maybe (EllipsisNaturalRangeElement scope)
rangeFirstElement valueRange
  | ellipsisNaturalRangeSize valueRange == Just 0 = Nothing
  | otherwise = Just (rangeSeedElement valueRange)

rangeSeedElement
  :: EllipsisNaturalRange scope
  -> EllipsisNaturalRangeElement scope
rangeSeedElement = EllipsisNaturalRangeElement . rangeStartValue

rangeChain
  :: EllipsisNaturalRange scope
  -> Chain (EllipsisNaturalRangeElement scope)
rangeChain valueRange =
  chain
    (rangeOrderType valueRange)
    (finiteOrdinal . relativeRank)
    (naturalAtOrdinal >=> elementAtOffset)
    (const ())
    (\_ _ -> ())
    (const ())
  where
    rangeStart = rangeStartValue valueRange

    elementAtOffset offset =
      ellipsisNaturalRangeElement valueRange
        (case ellipsisNaturalRangeTarget valueRange of
          FiniteTarget target
            | rangeStart <= target -> rangeStart + offset
            | offset <= rangeStart -> rangeStart - offset
            | otherwise -> 0
          NegativeOne
            | offset <= rangeStart -> rangeStart - offset
            | otherwise -> 0
          UnboundedTarget -> rangeStart + offset)

    relativeRank element =
      let elementRank = ellipsisNaturalRangeElementRank element
      in case ellipsisNaturalRangeTarget valueRange of
          FiniteTarget target
            | rangeStart <= target -> elementRank - rangeStart
            | otherwise -> rangeStart - elementRank
          NegativeOne -> rangeStart - elementRank
          UnboundedTarget -> elementRank - rangeStart

rangeAtlas
  :: EllipsisNaturalRange scope
  -> AtlasConfederation
       (EllipsisNaturalRangeConfederationScope scope)
       ()
rangeAtlas valueRange =
  singletonAtlasConfederation
    (chainedDominionAtlas
      (rangeSeedElement valueRange)
      (rangeChain valueRange)
      (ellipsisNaturalRangeDominion valueRange))

-- | Interpret a range as the representable map with its exact finite or
-- omega-length final chain.
ellipsisNaturalRangeMap
  :: EllipsisNaturalRange scope
  -> StableConfederalData (EllipsisNaturalRangeMap scope)
ellipsisNaturalRangeMap valueRange =
  embedAtlasMap
    (chainedDominionAtlasMap
      (rangeSeedElement valueRange)
      (rangeChain valueRange)
      (ellipsisNaturalRangeDominion valueRange))

rangeConcatValue
  :: EllipsisNaturalRange leftScope
  -> EllipsisNaturalRange rightScope
  -> EllipsisNaturalRangeConcatValue leftScope rightScope
rangeConcatValue first second =
  concatValue
    (rangeAtlas first)
    (rangeAtlas second)
    identityAtlasConfederationHom
    identityAtlasConfederationHom

-- | Concatenate ranges from left to right. Swapping the operands changes the
-- resulting ordinal sum. Disjoint absolute images additionally produce the
-- insertion capability required for constructing an Ellipsis subtype;
-- overlapping images deliberately return only the map presentation.
concatEllipsisNaturalRanges
  :: EllipsisNaturalRange leftScope
  -> EllipsisNaturalRange rightScope
  -> SomeEllipsisNaturalRangeConcat leftScope rightScope
concatEllipsisNaturalRanges first second =
  let valueMap =
        ellipsisNaturalRangeMap first <.> ellipsisNaturalRangeMap second
      value = rangeConcatValue first second
  in if rangesOverlap first second
      then SomeEllipsisNaturalRangeConcat
        (ConcatenatedEllipsisMap valueMap value)
      else SomeEllipsisNaturalRangeConcat
        (ConcatenatedEllipsisInsertion
          valueMap
          value
          (mergeDisjointEllipsisInsertions
            (ellipsisNaturalRangeInsertion first)
            (ellipsisNaturalRangeInsertion second)))

-- | Range merging is ordered concatenation; this name is retained for the
-- domain operation while making its noncommutative semantics explicit in the
-- result value.
mergeEllipsisNaturalRanges
  :: EllipsisNaturalRange leftScope
  -> EllipsisNaturalRange rightScope
  -> SomeEllipsisNaturalRangeConcat leftScope rightScope
mergeEllipsisNaturalRanges = concatEllipsisNaturalRanges

ellipsisNaturalRangeConcatMap
  :: EllipsisNaturalRangeConcat kind leftScope rightScope
  -> StableConfederalData
       (EllipsisNaturalRangeConcatValues leftScope rightScope)
ellipsisNaturalRangeConcatMap
    (ConcatenatedEllipsisInsertion valueMap _ _) = valueMap
ellipsisNaturalRangeConcatMap (ConcatenatedEllipsisMap valueMap _) = valueMap

ellipsisNaturalRangeConcatValue
  :: EllipsisNaturalRangeConcat kind leftScope rightScope
  -> EllipsisNaturalRangeConcatValue leftScope rightScope
ellipsisNaturalRangeConcatValue
    (ConcatenatedEllipsisInsertion _ value _) = value
ellipsisNaturalRangeConcatValue (ConcatenatedEllipsisMap _ value) = value

ellipsisNaturalRangeConcatInsertion
  :: EllipsisNaturalRangeConcat
       'EllipsisInsertionConcat leftScope rightScope
  -> EllipsisInsertion
       (Either
         (EllipsisNaturalRangeElement leftScope)
         (EllipsisNaturalRangeElement rightScope))
ellipsisNaturalRangeConcatInsertion
    (ConcatenatedEllipsisInsertion _ _ insertion) = insertion

-- | Request only the subtype capability. Overlapping concatenations return
-- 'Nothing' while remaining available through 'concatEllipsisNaturalRanges'
-- as ordered maps.
concatEllipsisNaturalRangeInsertion
  :: EllipsisNaturalRange leftScope
  -> EllipsisNaturalRange rightScope
  -> Maybe
       (EllipsisInsertion
         (Either
           (EllipsisNaturalRangeElement leftScope)
           (EllipsisNaturalRangeElement rightScope)))
concatEllipsisNaturalRangeInsertion first second =
  case concatEllipsisNaturalRanges first second of
    SomeEllipsisNaturalRangeConcat
        (ConcatenatedEllipsisInsertion _ _ insertion) -> Just insertion
    SomeEllipsisNaturalRangeConcat (ConcatenatedEllipsisMap _ _) -> Nothing

rangeStartValue :: EllipsisNaturalRange scope -> Natural
rangeStartValue = fromMaybe 0 . ellipsisNaturalRangeStart

-- | The finite number of elements, or 'Nothing' for an upward-unbounded
-- range.
ellipsisNaturalRangeSize
  :: EllipsisNaturalRange scope
  -> Maybe Natural
ellipsisNaturalRangeSize valueRange =
  case ellipsisNaturalRangeTarget valueRange of
    FiniteTarget target
      | start <= target -> Just (target - start)
      | otherwise -> Just (start - target)
    NegativeOne -> Just (start + 1)
    UnboundedTarget -> Nothing
  where
    start = rangeStartValue valueRange

rangeOrderType :: EllipsisNaturalRange scope -> Ordinal
rangeOrderType valueRange =
  maybe omega finiteOrdinal (ellipsisNaturalRangeSize valueRange)

rankInRange :: EllipsisNaturalRange scope -> Natural -> Bool
rankInRange valueRange rankValue =
  case ellipsisNaturalRangeTarget valueRange of
    FiniteTarget target
      | start < target -> start <= rankValue && rankValue < target
      | start > target -> target < rankValue && rankValue <= start
      | otherwise -> False
    NegativeOne -> rankValue <= start
    UnboundedTarget -> start <= rankValue
  where
    start = rangeStartValue valueRange

rangesOverlap
  :: EllipsisNaturalRange leftScope
  -> EllipsisNaturalRange rightScope
  -> Bool
rangesOverlap first second =
  case (rangeImageBounds first, rangeImageBounds second) of
    (Nothing, _) -> False
    (_, Nothing) -> False
    (Just firstBounds, Just secondBounds) ->
      not
        (imageBefore firstBounds secondBounds
          || imageBefore secondBounds firstBounds)

-- Inclusive minimum and optional inclusive maximum of a nonempty image.
rangeImageBounds
  :: EllipsisNaturalRange scope
  -> Maybe (Natural, Maybe Natural)
rangeImageBounds valueRange =
  case ellipsisNaturalRangeTarget valueRange of
    FiniteTarget target
      | start < target -> Just (start, Just (target - 1))
      | start > target -> Just (target + 1, Just start)
      | otherwise -> Nothing
    NegativeOne -> Just (0, Just start)
    UnboundedTarget -> Just (start, Nothing)
  where
    start = rangeStartValue valueRange

imageBefore
  :: (Natural, Maybe Natural)
  -> (Natural, Maybe Natural)
  -> Bool
imageBefore (_, Nothing) _ = False
imageBefore (_, Just firstMaximum) (secondMinimum, _) =
  firstMaximum < secondMinimum

instance
    Concat
      (EllipsisNaturalRange leftScope)
      (EllipsisNaturalRange rightScope) where
  type ConcatResult
      (EllipsisNaturalRange leftScope)
      (EllipsisNaturalRange rightScope) =
        SomeEllipsisNaturalRangeConcat leftScope rightScope
  concatOperands = concatEllipsisNaturalRanges
