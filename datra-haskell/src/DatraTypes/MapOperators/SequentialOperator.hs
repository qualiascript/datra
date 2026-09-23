{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Associatively flattened, ordered Atlas expansion.
module MapOperators.SequentialOperator
  ( SequentialOperatorValues
  , SequentialOperatorValue
  , SequentialPresentation
  , withSequentialPresentationAtlas
  , SequentialAtlasTraversal
  , sequentialAtlasTraversalPosition
  , withSequentialAtlasTraversal
  , sequentialValue
  , sequentialOperator
  , sequentialToHorizontalSum
  , withSequentialAtlasTraversals
  ) where

import Atlas (Atlas, AtlasObject)
import AtlasConfederation
  ( AtlasConfederation
  , AtlasConfederationObject
  , MergedAtlasConfederationScope
  , withAtlasConfederationResultingAtlas
  )
import AtlasSequence
  ( AtlasSequenceDatum
  , AtlasSequenceMember
  , AtlasSequencePageCell
  , atlasSequence
  , atlasSequenceMember
  , atlasSequenceMemberOrderedTransposal
  , withAtlasSequenceMember
  )
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty (..))
import HorizontalSum
  ( HorizontalSumValue (..)
  , HorizontalSumValues
  , horizontalSumValue
  )
import HorizontalSum.Syntax ((|+|))
import Numeric.Natural (Natural)
import OrderedAtlasTransposal (OrderedAtlasTransposal)
import MapOperators.Internal
  ( forgetStableConfederalDataWrapper
  , wrapStableConfederalData
  )
import StableConfederalData
  ( StableConfederalData
  , StableConfederalDataHom
  , StableConfederalDataValue
  )

-- | Defunctionalized binary carrier. Nested occurrences are flattened by
-- 'SequentialPresentation', so their geometric presentation is associative even
-- though the Haskell carrier records the expression's binary parse tree.
data SequentialOperatorValues (left :: Type) (right :: Type)

type role SequentialOperatorValue nominal nominal nominal
newtype SequentialOperatorValue left right object =
  SequentialOperatorValue
    (HorizontalSumValue left right object)

type instance
  StableConfederalDataValue
    (SequentialOperatorValues left right)
    object =
      SequentialOperatorValue left right object

-- | Interpret a stable-confederal value as one or more sequential operands.
-- Ordinary values contribute one resulting Atlas. Sequential values
-- recursively contribute their leaves. The instances make flattening work
-- through either parenthesization.
class SequentialPresentation values where
  sequentialPresentationMembers
    :: AtlasConfederation scope index
    -> StableConfederalDataValue
         values (AtlasConfederationObject scope index)
    -> NonEmpty AtlasSequenceMember
  sequentialPresentationMembers confederation value =
    withSequentialPresentationAtlas confederation value $ \valueAtlas ->
      atlasSequenceMember valueAtlas :| []

  -- | Evaluate the Atlas that should be treated as one operand when a
  -- non-flattening operator places a boundary around this value.
  withSequentialPresentationAtlas
    :: AtlasConfederation scope index
    -> StableConfederalDataValue
         values (AtlasConfederationObject scope index)
    -> (forall atlasScope paginationScope cellData origin final.
         Atlas atlasScope paginationScope cellData origin final
         -> result)
    -> result

instance {-# OVERLAPPABLE #-} SequentialPresentation values where
  withSequentialPresentationAtlas confederation _ =
    withAtlasConfederationResultingAtlas confederation

instance {-# OVERLAPPING #-}
    (SequentialPresentation left, SequentialPresentation right) =>
    SequentialPresentation (SequentialOperatorValues left right) where
  sequentialPresentationMembers _
      (SequentialOperatorValue
        (HorizontalSumValue left right _ leftValue rightValue)) =
    sequentialPresentationMembers left leftValue
      <> sequentialPresentationMembers right rightValue

  withSequentialPresentationAtlas _ value useAtlas =
    withSequentialAtlasTraversals value $ \valueAtlas _ ->
      useAtlas valueAtlas

-- | One member's canonical ordered traversal into the flattened result.
data SequentialAtlasTraversal target where
  SequentialAtlasTraversal
    :: Natural
    -> Atlas atlasScope paginationScope cellData origin final
    -> OrderedAtlasTransposal
         (AtlasObject atlasScope paginationScope cellData)
         target
    -> SequentialAtlasTraversal target

sequentialAtlasTraversalPosition
  :: SequentialAtlasTraversal target
  -> Natural
sequentialAtlasTraversalPosition
    (SequentialAtlasTraversal position _ _) = position

withSequentialAtlasTraversal
  :: SequentialAtlasTraversal target
  -> (forall atlasScope paginationScope cellData origin final.
       Natural
       -> Atlas atlasScope paginationScope cellData origin final
       -> OrderedAtlasTransposal
            (AtlasObject atlasScope paginationScope cellData)
            target
       -> result)
  -> result
withSequentialAtlasTraversal
    (SequentialAtlasTraversal position valueAtlas traversal)
    useTraversal =
  useTraversal position valueAtlas traversal

-- | Introduce a binary generator. If either supplied value is already
-- sequential, its leaves are retained for the flattened presentation.
sequentialValue
  :: (SequentialPresentation left, SequentialPresentation right)
  => AtlasConfederation leftScope leftIndex
  -> AtlasConfederation rightScope rightIndex
  -> StableConfederalDataValue
       left (AtlasConfederationObject leftScope leftIndex)
  -> StableConfederalDataValue
       right (AtlasConfederationObject rightScope rightIndex)
  -> SequentialOperatorValue
       left
       right
       (AtlasConfederationObject
         (MergedAtlasConfederationScope leftScope rightScope)
         (Either leftIndex rightIndex))
sequentialValue left right leftValue rightValue =
  SequentialOperatorValue
    (horizontalSumValue left right leftValue rightValue)

-- | Form a sequential universal object. Its presheaf action is inherited
-- from DatraCore's Day convolution; only its Atlas presentation is flattened.
sequentialOperator
  :: (SequentialPresentation left, SequentialPresentation right)
  => StableConfederalData left
  -> StableConfederalData right
  -> StableConfederalData (SequentialOperatorValues left right)
sequentialOperator left right =
  wrapStableConfederalData summed unwrap SequentialOperatorValue
  where
    summed = left |+| right
    unwrap (SequentialOperatorValue value) = value

-- | Forget the flattened geometric presentation, retaining the universal
-- morphism to the binary horizontal sum of the two parsed operands.
sequentialToHorizontalSum
  :: (SequentialPresentation left, SequentialPresentation right)
  => StableConfederalData left
  -> StableConfederalData right
  -> StableConfederalDataHom
       (SequentialOperatorValues left right)
       (HorizontalSumValues left right)
sequentialToHorizontalSum left right =
  forgetStableConfederalDataWrapper
    (sequentialOperator left right)
    (left |+| right)
    unwrap
  where
    unwrap (SequentialOperatorValue value) = value

makeTraversal
  :: NonEmpty AtlasSequenceMember
  -> Atlas
       mergeAtlasScope
       mergeScope
       AtlasSequenceDatum
       ()
       AtlasSequencePageCell
  -> Natural
  -> AtlasSequenceMember
  -> SequentialAtlasTraversal
       (AtlasObject mergeAtlasScope mergeScope AtlasSequenceDatum)
makeTraversal members mergedAtlas position member =
  withAtlasSequenceMember member $ \sourceAtlas ->
    SequentialAtlasTraversal
      position
      sourceAtlas
      (atlasSequenceMemberOrderedTransposal
        members position sourceAtlas mergedAtlas)

indexedTraversals
  :: NonEmpty AtlasSequenceMember
  -> Atlas
       mergeAtlasScope
       mergeScope
       AtlasSequenceDatum
       ()
       AtlasSequencePageCell
  -> [SequentialAtlasTraversal
       (AtlasObject mergeAtlasScope mergeScope AtlasSequenceDatum)]
indexedTraversals members mergedAtlas =
  zipWith
    (makeTraversal members mergedAtlas)
    [0 ..]
    (toList members)

-- | Evaluate the flattened geometric presentation. The result has one
-- page-1 cell per recursively flattened operand, in source order, and one
-- canonical ordered Atlas traversal for each such cell.
withSequentialAtlasTraversals
  :: (SequentialPresentation left, SequentialPresentation right)
  => SequentialOperatorValue left right object
  -> (forall mergeAtlasScope mergePaginationScope.
       Atlas
         mergeAtlasScope
         mergePaginationScope
         AtlasSequenceDatum
         ()
         AtlasSequencePageCell
       -> [SequentialAtlasTraversal
            (AtlasObject
              mergeAtlasScope mergePaginationScope AtlasSequenceDatum)]
       -> result)
  -> result
withSequentialAtlasTraversals
    (SequentialOperatorValue
      (HorizontalSumValue left right _ leftValue rightValue))
    useSequence =
  let members =
        sequentialPresentationMembers left leftValue
          <> sequentialPresentationMembers right rightValue
  in atlasSequence members $ \mergedAtlas ->
      useSequence
        mergedAtlas
        (indexedTraversals members mergedAtlas)

toList :: NonEmpty value -> [value]
toList (value :| values) = value : values
