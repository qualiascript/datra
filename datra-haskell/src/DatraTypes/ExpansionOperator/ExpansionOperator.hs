{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | A non-associative grouping boundary for stable-confederal data.
module ExpansionOperator
  ( ExpansionOperatorValues
  , ExpansionOperatorValue
  , expansionValue
  , expansionOperator
  , expansionToHorizontalSum
  , withExpansionOrderedTransposals
  ) where

import Atlas (Atlas, AtlasObject)
import AtlasConfederation
  ( AtlasConfederation
  , AtlasConfederationObject
  , MergedAtlasConfederationScope
  )
import AtlasMerge
  ( AtlasMergeDatum
  , AtlasMergePageCell
  , atlasMerge
  , atlasMergeLeftOrderedTransposal
  , atlasMergeRightOrderedTransposal
  )
import Data.Kind (Type)
import HorizontalSum
  ( HorizontalSumValue (..)
  , HorizontalSumValues
  , horizontalSum
  , horizontalSumValue
  )
import OrderedAtlasTransposal (OrderedAtlasTransposal)
import SequentialOperator
  ( SequentialOperand
  , withSequentialOperandAtlas
  )
import StableConfederalData
  ( StableConfederalData
  , StableConfederalDataHom
  , StableConfederalDataValue
  , mapStableConfederalData
  , stableConfederalData
  , stableConfederalDataComposition
  , stableConfederalDataHom
  , stableConfederalDataIdentity
  )

-- | Defunctionalized carrier for one deliberately unflattened binary node.
data ExpansionOperatorValues (left :: Type) (right :: Type)

type role ExpansionOperatorValue nominal nominal nominal
newtype ExpansionOperatorValue left right object =
  ExpansionOperatorValue
    (HorizontalSumValue left right object)

type instance
  StableConfederalDataValue
    (ExpansionOperatorValues left right)
    object =
      ExpansionOperatorValue left right object

-- | Introduce one non-associative expansion node.
expansionValue
  :: AtlasConfederation leftScope leftIndex
  -> AtlasConfederation rightScope rightIndex
  -> StableConfederalDataValue
       left (AtlasConfederationObject leftScope leftIndex)
  -> StableConfederalDataValue
       right (AtlasConfederationObject rightScope rightIndex)
  -> ExpansionOperatorValue
       left
       right
       (AtlasConfederationObject
         (MergedAtlasConfederationScope leftScope rightScope)
         (Either leftIndex rightIndex))
expansionValue left right leftValue rightValue =
  ExpansionOperatorValue
    (horizontalSumValue left right leftValue rightValue)

-- | Form an explicitly grouped binary expansion. Reindexing remains the Day
-- convolution action; the grouping distinction appears in its Atlas
-- presentation.
expansionOperator
  :: StableConfederalData left
  -> StableConfederalData right
  -> StableConfederalData (ExpansionOperatorValues left right)
expansionOperator left right =
  stableConfederalData
    (\arrow (ExpansionOperatorValue value) ->
      ExpansionOperatorValue
        (mapStableConfederalData summed arrow value))
    (\(ExpansionOperatorValue value) ->
      stableConfederalDataIdentity summed value)
    (\second first (ExpansionOperatorValue value) ->
      stableConfederalDataComposition summed second first value)
  where
    summed = horizontalSum left right

-- | Forget the explicit grouping presentation to its horizontal sum.
expansionToHorizontalSum
  :: StableConfederalData left
  -> StableConfederalData right
  -> StableConfederalDataHom
       (ExpansionOperatorValues left right)
       (HorizontalSumValues left right)
expansionToHorizontalSum left right =
  stableConfederalDataHom
    (expansionOperator left right)
    (horizontalSum left right)
    unwrap
    (\_ _ -> ())
  where
    unwrap (ExpansionOperatorValue value) = value

-- | Evaluate the grouped geometry. Sequential operands are first evaluated
-- to their flattened Atlases and then each whole result is treated as one
-- side of this binary merge. Thus expansion preserves a chosen sequence
-- boundary instead of recursively flattening through it.
withExpansionOrderedTransposals
  :: (SequentialOperand left, SequentialOperand right)
  => ExpansionOperatorValue left right object
  -> (forall leftAtlasScope leftPaginationScope leftData leftOrigin leftFinal
       rightAtlasScope rightPaginationScope rightData rightOrigin rightFinal
       mergeAtlasScope mergePaginationScope.
       Atlas
         leftAtlasScope
         leftPaginationScope
         leftData
         leftOrigin
         leftFinal
       -> Atlas
            rightAtlasScope
            rightPaginationScope
            rightData
            rightOrigin
            rightFinal
       -> Atlas
            mergeAtlasScope
            mergePaginationScope
            AtlasMergeDatum
            ()
            AtlasMergePageCell
       -> OrderedAtlasTransposal
            (AtlasObject leftAtlasScope leftPaginationScope leftData)
            (AtlasObject
              mergeAtlasScope mergePaginationScope AtlasMergeDatum)
       -> OrderedAtlasTransposal
            (AtlasObject rightAtlasScope rightPaginationScope rightData)
            (AtlasObject
              mergeAtlasScope mergePaginationScope AtlasMergeDatum)
       -> result)
  -> result
withExpansionOrderedTransposals
    (ExpansionOperatorValue
      (HorizontalSumValue left right _ leftValue rightValue))
    useExpansion =
  withSequentialOperandAtlas left leftValue $ \leftAtlas ->
    withSequentialOperandAtlas right rightValue $ \rightAtlas ->
      atlasMerge leftAtlas rightAtlas $ \mergedAtlas ->
        useExpansion
          leftAtlas
          rightAtlas
          mergedAtlas
          (atlasMergeLeftOrderedTransposal
            leftAtlas rightAtlas mergedAtlas)
          (atlasMergeRightOrderedTransposal
            leftAtlas rightAtlas mergedAtlas)

-- Expansion is opaque when it appears inside another sequential expression:
-- its entire grouped Atlas contributes one sequential member.
instance {-# OVERLAPPING #-}
    (SequentialOperand left, SequentialOperand right) =>
    SequentialOperand (ExpansionOperatorValues left right) where
  withSequentialOperandAtlas _ value useAtlas =
    withExpansionOrderedTransposals value $
      \_ _ mergedAtlas _ _ -> useAtlas mergedAtlas
