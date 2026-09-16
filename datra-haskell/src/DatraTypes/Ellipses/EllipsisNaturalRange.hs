{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

-- | Nonempty half-open natural ranges and their ordered concatenations.
module EllipsisNaturalRange
  ( EllipsisNaturalRange
  , EllipsisNaturalRangeElement
  , EllipsisNaturalRangeMap
  , EllipsisNaturalRangeConcatValues
  , EllipsisNaturalRangeConcatValue
  , EllipsisNaturalRangeConcatKind (..)
  , EllipsisNaturalRangeConcat (..)
  , SomeEllipsisNaturalRangeConcat (..)
  , ellipsisNaturalRange
  , ellipsisNaturalRangeLowerBound
  , ellipsisNaturalRangeUpperBound
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
import Data.Kind (Type)
import Data.Maybe (fromMaybe)
import DatraOrdinal
  ( finiteOrdinal
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
  ( Concat (..)
  , ConcatOperatorValue
  , ConcatOperatorValues
  , concatValue
  , (<.>)
  )
import Numeric.Natural (Natural)
import StableConfederalData
  ( EmbeddedAtlasMap
  , StableConfederalData
  , embedAtlasMap
  )

-- | A half-open interval of ellipsis ranks. A missing bound leaves that side
-- unrestricted.
type role EllipsisNaturalRange nominal
data EllipsisNaturalRange (scope :: Type) = EllipsisNaturalRange
  { ellipsisNaturalRangeLowerBound :: Maybe Natural
  , ellipsisNaturalRangeUpperBound :: Maybe Natural
  }

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

-- | Validate optional natural-number bounds and introduce the resulting range
-- with a fresh abstract scope. The range must be nonempty, treating a missing
-- lower bound as zero.
ellipsisNaturalRange
  :: Maybe Natural
  -> Maybe Natural
  -> (forall scope. EllipsisNaturalRange scope -> result)
  -> Maybe result
ellipsisNaturalRange lower upper useRange
  | validOrder lower upper =
      Just (useRange (EllipsisNaturalRange lower upper))
  | otherwise = Nothing

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
  -> EllipsisNaturalRangeElement scope
rangeFirstElement =
  EllipsisNaturalRangeElement . fromMaybe 0
    . ellipsisNaturalRangeLowerBound

rangeChain
  :: EllipsisNaturalRange scope
  -> Chain (EllipsisNaturalRangeElement scope)
rangeChain valueRange =
  chain
    rangeOrderType
    (finiteOrdinal . relativeRank)
    (\position -> do
      offset <- naturalAtOrdinal position
      ellipsisNaturalRangeElement valueRange (rangeStart + offset))
    (const ())
    (\_ _ -> ())
    (const ())
  where
    rangeStart =
      fromMaybe 0 (ellipsisNaturalRangeLowerBound valueRange)

    rangeOrderType =
      case ellipsisNaturalRangeUpperBound valueRange of
        Just upper -> finiteOrdinal (upper - rangeStart)
        Nothing -> omega

    relativeRank element =
      ellipsisNaturalRangeElementRank element - rangeStart

rangeAtlas
  :: EllipsisNaturalRange scope
  -> AtlasConfederation
       (EllipsisNaturalRangeConfederationScope scope)
       ()
rangeAtlas valueRange =
  singletonAtlasConfederation
    (chainedDominionAtlas
      (rangeFirstElement valueRange)
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
      (rangeFirstElement valueRange)
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

validOrder :: Maybe Natural -> Maybe Natural -> Bool
validOrder maybeLower (Just upper) = fromMaybe 0 maybeLower < upper
validOrder _ Nothing = True

rankInRange :: EllipsisNaturalRange scope -> Natural -> Bool
rankInRange valueRange rankValue =
  maybe True (<= rankValue)
    (ellipsisNaturalRangeLowerBound valueRange)
    && maybe True (rankValue <)
      (ellipsisNaturalRangeUpperBound valueRange)

rangesOverlap
  :: EllipsisNaturalRange leftScope
  -> EllipsisNaturalRange rightScope
  -> Bool
rangesOverlap first second =
  not (rangeBefore first second || rangeBefore second first)

rangeBefore
  :: EllipsisNaturalRange firstScope
  -> EllipsisNaturalRange secondScope
  -> Bool
rangeBefore first second =
  case ellipsisNaturalRangeUpperBound first of
    Nothing -> False
    Just firstUpper ->
      firstUpper <= fromMaybe 0 (ellipsisNaturalRangeLowerBound second)

instance
    Concat
      (EllipsisNaturalRange leftScope)
      (EllipsisNaturalRange rightScope) where
  type ConcatResult
      (EllipsisNaturalRange leftScope)
      (EllipsisNaturalRange rightScope) =
        SomeEllipsisNaturalRangeConcat leftScope rightScope
  (<.>) = concatEllipsisNaturalRanges
