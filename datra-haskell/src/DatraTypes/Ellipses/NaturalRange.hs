{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

-- | Natural ranges as the rank-one specialization of 'SuperEllipsisRange'.
module NaturalRange
  ( NaturalRange
  , NaturalRangeTarget (..)
  , NaturalRangeElement
  , NaturalRangeMap
  , NaturalRangeConcatValues
  , NaturalRangeConcatValue
  , NaturalRangeConcatKind (..)
  , NaturalRangeConcat (..)
  , SomeNaturalRangeConcat (..)
  , naturalRange
  , naturalRangeFromSuperEllipsisRange
  , naturalRangeSuperEllipsisRange
  , naturalRangeStart
  , naturalRangeTarget
  , naturalRangeLowerBound
  , naturalRangeUpperBound
  , naturalRangeSize
  , naturalRangeElement
  , naturalRangeElementRank
  , naturalRangeInsertion
  , naturalRangeMap
  , concatNaturalRanges
  , mergeNaturalRanges
  , naturalRangeConcatMap
  , naturalRangeConcatValue
  , naturalRangeConcatInsertion
  , concatNaturalRangeInsertion
  ) where

import Control.Monad ((>=>))
import DatraOrdinal (finiteOrdinal, naturalAtOrdinal)
import Ellipsis (Ellipsis, ellipsisRank)
import EllipsisInsertion (EllipsisInsertion)
import MapOperators.ConcatOperator
  ( Concat (ConcatResult, concatOperands)
  )
import Numeric.Natural (Natural)
import StableConfederalData (StableConfederalData)
import SuperEllipsisRange
  ( SomeSuperEllipsisRangeConcat (SomeSuperEllipsisRangeConcat)
  , SuperEllipsisRange
  , SuperEllipsisRangeConcat
      ( ConcatenatedSuperEllipsisInsertion
      , ConcatenatedSuperEllipsisMap
      )
  , SuperEllipsisRangeConcatValues
  , SuperEllipsisRangeConcatValue
  , SuperEllipsisRangeElement
  , SuperEllipsisRangeMap
  , SuperEllipsisRangeTarget
  , concatSuperEllipsisRanges
  , superEllipsisRange
  , superEllipsisRangeElement
  , superEllipsisRangeElementPosition
  , superEllipsisRangeInsertion
  , superEllipsisRangeLowerBound
  , superEllipsisRangeMap
  , superEllipsisRangeOrderType
  , superEllipsisRangeStart
  , superEllipsisRangeTarget
  , superEllipsisRangeUpperBound
  )
import qualified SuperEllipsisRange as Super

data NaturalRangeTarget
  = FiniteTarget Natural
  | NegativeOne
  | UnboundedTarget
  deriving (Eq, Show)

newtype NaturalRange scope = NaturalRange
  { unNaturalRange :: SuperEllipsisRange Ellipsis scope
  }

naturalRangeFromSuperEllipsisRange
  :: SuperEllipsisRange Ellipsis scope
  -> NaturalRange scope
naturalRangeFromSuperEllipsisRange = NaturalRange

naturalRangeSuperEllipsisRange
  :: NaturalRange scope
  -> SuperEllipsisRange Ellipsis scope
naturalRangeSuperEllipsisRange = unNaturalRange

type NaturalRangeElement = SuperEllipsisRangeElement Ellipsis

type NaturalRangeMap scope = SuperEllipsisRangeMap Ellipsis scope

type NaturalRangeConcatValues leftScope rightScope =
  SuperEllipsisRangeConcatValues Ellipsis leftScope rightScope

type NaturalRangeConcatValue leftScope rightScope =
  SuperEllipsisRangeConcatValue Ellipsis leftScope rightScope

data NaturalRangeConcatKind
  = NaturalInsertionConcat
  | NaturalMapConcat

data NaturalRangeConcat
    (kind :: NaturalRangeConcatKind)
    leftScope
    rightScope where
  ConcatenatedNaturalInsertion
    :: StableConfederalData
         (NaturalRangeConcatValues leftScope rightScope)
    -> NaturalRangeConcatValue leftScope rightScope
    -> EllipsisInsertion
         (Either
           (NaturalRangeElement leftScope)
           (NaturalRangeElement rightScope))
    -> NaturalRangeConcat 'NaturalInsertionConcat leftScope rightScope
  ConcatenatedNaturalMap
    :: StableConfederalData
         (NaturalRangeConcatValues leftScope rightScope)
    -> NaturalRangeConcatValue leftScope rightScope
    -> NaturalRangeConcat 'NaturalMapConcat leftScope rightScope

data SomeNaturalRangeConcat leftScope rightScope where
  SomeNaturalRangeConcat
    :: NaturalRangeConcat kind leftScope rightScope
    -> SomeNaturalRangeConcat leftScope rightScope

naturalRange
  :: Maybe Natural
  -> NaturalRangeTarget
  -> (forall scope. NaturalRange scope -> result)
  -> Maybe result
naturalRange start target useRange =
  superEllipsisRange
    ellipsisRank
    (finiteOrdinal <$> start)
    (toSuperTarget target)
    (useRange . NaturalRange)

toSuperTarget :: NaturalRangeTarget -> SuperEllipsisRangeTarget
toSuperTarget (FiniteTarget target) = Super.FiniteTarget (finiteOrdinal target)
toSuperTarget NegativeOne = Super.NegativeOne
toSuperTarget UnboundedTarget = Super.UnboundedTarget

naturalRangeStart :: NaturalRange scope -> Maybe Natural
naturalRangeStart =
  superEllipsisRangeStart . unNaturalRange >=> naturalAtOrdinal

naturalRangeTarget :: NaturalRange scope -> NaturalRangeTarget
naturalRangeTarget valueRange =
  case superEllipsisRangeTarget (unNaturalRange valueRange) of
    Super.FiniteTarget target ->
      maybe UnboundedTarget FiniteTarget
        (naturalAtOrdinal target)
    Super.NegativeOne -> NegativeOne
    Super.UnboundedTarget -> UnboundedTarget

naturalRangeLowerBound :: NaturalRange scope -> Maybe Natural
naturalRangeLowerBound =
  superEllipsisRangeLowerBound . unNaturalRange >=> naturalAtOrdinal

naturalRangeUpperBound :: NaturalRange scope -> Maybe Natural
naturalRangeUpperBound =
  superEllipsisRangeUpperBound . unNaturalRange >=> naturalAtOrdinal

naturalRangeSize :: NaturalRange scope -> Maybe Natural
naturalRangeSize valueRange =
  case naturalRangeTarget valueRange of
    UnboundedTarget -> Nothing
    _ -> naturalAtOrdinal
      (superEllipsisRangeOrderType (unNaturalRange valueRange))

naturalRangeElement
  :: NaturalRange scope
  -> Natural
  -> Maybe (NaturalRangeElement scope)
naturalRangeElement valueRange =
  superEllipsisRangeElement (unNaturalRange valueRange) . finiteOrdinal

naturalRangeElementRank :: NaturalRangeElement scope -> Natural
naturalRangeElementRank element =
  case naturalAtOrdinal (superEllipsisRangeElementPosition element) of
    Just value -> value
    Nothing -> 0

naturalRangeInsertion
  :: NaturalRange scope
  -> EllipsisInsertion (NaturalRangeElement scope)
naturalRangeInsertion =
  superEllipsisRangeInsertion . unNaturalRange

naturalRangeMap
  :: NaturalRange scope
  -> StableConfederalData (NaturalRangeMap scope)
naturalRangeMap = superEllipsisRangeMap . unNaturalRange

concatNaturalRanges
  :: NaturalRange leftScope
  -> NaturalRange rightScope
  -> SomeNaturalRangeConcat leftScope rightScope
concatNaturalRanges first second =
  case concatSuperEllipsisRanges
    (unNaturalRange first) (unNaturalRange second) of
      SomeSuperEllipsisRangeConcat
          (ConcatenatedSuperEllipsisInsertion valueMap value insertion) ->
        SomeNaturalRangeConcat
          (ConcatenatedNaturalInsertion valueMap value insertion)
      SomeSuperEllipsisRangeConcat
          (ConcatenatedSuperEllipsisMap valueMap value) ->
        SomeNaturalRangeConcat (ConcatenatedNaturalMap valueMap value)

mergeNaturalRanges
  :: NaturalRange leftScope
  -> NaturalRange rightScope
  -> SomeNaturalRangeConcat leftScope rightScope
mergeNaturalRanges = concatNaturalRanges

naturalRangeConcatMap
  :: NaturalRangeConcat kind leftScope rightScope
  -> StableConfederalData
       (NaturalRangeConcatValues leftScope rightScope)
naturalRangeConcatMap (ConcatenatedNaturalInsertion valueMap _ _) = valueMap
naturalRangeConcatMap (ConcatenatedNaturalMap valueMap _) = valueMap

naturalRangeConcatValue
  :: NaturalRangeConcat kind leftScope rightScope
  -> NaturalRangeConcatValue leftScope rightScope
naturalRangeConcatValue (ConcatenatedNaturalInsertion _ value _) = value
naturalRangeConcatValue (ConcatenatedNaturalMap _ value) = value

naturalRangeConcatInsertion
  :: NaturalRangeConcat 'NaturalInsertionConcat leftScope rightScope
  -> EllipsisInsertion
       (Either
         (NaturalRangeElement leftScope)
         (NaturalRangeElement rightScope))
naturalRangeConcatInsertion
    (ConcatenatedNaturalInsertion _ _ insertion) = insertion

concatNaturalRangeInsertion
  :: NaturalRange leftScope
  -> NaturalRange rightScope
  -> Maybe
       (EllipsisInsertion
         (Either
           (NaturalRangeElement leftScope)
           (NaturalRangeElement rightScope)))
concatNaturalRangeInsertion first second =
  case concatNaturalRanges first second of
    SomeNaturalRangeConcat
        (ConcatenatedNaturalInsertion _ _ insertion) -> Just insertion
    SomeNaturalRangeConcat (ConcatenatedNaturalMap _ _) -> Nothing

instance Concat (NaturalRange leftScope) (NaturalRange rightScope) where
  type ConcatResult
      (NaturalRange leftScope)
      (NaturalRange rightScope) =
        SomeNaturalRangeConcat leftScope rightScope
  concatOperands = concatNaturalRanges
