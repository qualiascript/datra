-- | Atlas transposals whose object maps preserve the strict Atlas order.
--
-- This is the first restriction used to build Atlas transversals: it adds the
-- ordering clause from Lean's @IsTransversal@, but intentionally does not add
-- the covered-page-element clause.
{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

module OrderedAtlasTransposal
  ( OrderedAtlasTransposal
  , orderedAtlasTransposal
  , orderedAtlasTransposalTransposal
  , orderedAtlasTransposalHom
  , orderedAtlasTransposalPreservesOrder
  , orderedAtlasTransposalOwnedOrder
  , identityOrderedAtlasTransposal
  , composeOrderedAtlasTransposals
  , mapOrderedAtlasTransposalObject
  , orderedAtlasTransposalPreimage
  , orderedAtlasTransposalLeftInverse
  , orderedAtlasTransposalPagination
  , mapOrderedAtlasTransposalElement
  , mapOrderedAtlasTransposalArrow
  , mapOrderedAtlasTransposalData
  ) where

import OrderedAtlasTransposal.Internal
  ( OrderedAtlasTransposal
  , composeOrderedAtlasTransposals
  , identityOrderedAtlasTransposal
  , mapOrderedAtlasTransposalArrow
  , mapOrderedAtlasTransposalData
  , mapOrderedAtlasTransposalElement
  , mapOrderedAtlasTransposalObject
  , orderedAtlasTransposalHom
  , orderedAtlasTransposalLeftInverse
  , orderedAtlasTransposalPagination
  , orderedAtlasTransposalPreimage
  , orderedAtlasTransposalTransposal
  )

import qualified OrderedAtlasTransposal.Internal as Internal
  (orderedAtlasTransposal, orderedAtlasTransposalPreservesOrder, orderedAtlasTransposalOwnedOrder)
import Atlas (AtlasWitness)
import AtlasTransposal (AtlasTransposal, AtlasTransposalElement, atlasTransposalSourceValid,
  atlasTransposalPathValid, atlasTransposalElementValid, atlasTransposalElementLT, mapAtlasTransposalObject)

{-@ orderedAtlasTransposal :: transposal:AtlasTransposal source target
      -> (left:{AtlasTransposalElement source | atlasTransposalSourceValid transposal left}
           -> right:{AtlasTransposalElement source | atlasTransposalSourceValid transposal right && atlasTransposalElementLT left right}
           -> {atlasTransposalElementLT (mapAtlasTransposalObject transposal left) (mapAtlasTransposalObject transposal right)})
      -> {result:OrderedAtlasTransposal source target | orderedAtlasTransposalTransposal result == transposal} @-}
orderedAtlasTransposal :: AtlasTransposal source target
  -> (AtlasTransposalElement source -> AtlasTransposalElement source -> ()) -> OrderedAtlasTransposal source target
orderedAtlasTransposal transposal preserves = Internal.orderedAtlasTransposal transposal preserves

{-@ orderedAtlasTransposalPreservesOrder :: ordered:OrderedAtlasTransposal source target
      -> left:AtlasTransposalElement source -> right:AtlasTransposalElement source
      -> {atlasTransposalPathValid (orderedAtlasTransposalTransposal ordered) left
           && atlasTransposalPathValid (orderedAtlasTransposalTransposal ordered) right && atlasTransposalElementLT left right
           => atlasTransposalElementLT (mapOrderedAtlasTransposalObject ordered left) (mapOrderedAtlasTransposalObject ordered right)} @-}
orderedAtlasTransposalPreservesOrder :: OrderedAtlasTransposal source target
  -> AtlasTransposalElement source -> AtlasTransposalElement source -> ()
orderedAtlasTransposalPreservesOrder ordered left right = Internal.orderedAtlasTransposalPreservesOrder ordered left right

{-@ orderedAtlasTransposalOwnedOrder :: witness:AtlasWitness source
      -> ordered:{OrderedAtlasTransposal source target | TransposalOwnedBy witness (orderedAtlasTransposalTransposal ordered)}
      -> left:{AtlasTransposalElement source | atlasTransposalElementValid witness left}
      -> right:{AtlasTransposalElement source | atlasTransposalElementValid witness right && atlasTransposalElementLT left right}
      -> {atlasTransposalElementLT (mapOrderedAtlasTransposalObject ordered left) (mapOrderedAtlasTransposalObject ordered right)} @-}
orderedAtlasTransposalOwnedOrder :: AtlasWitness source -> OrderedAtlasTransposal source target
  -> AtlasTransposalElement source -> AtlasTransposalElement source -> ()
orderedAtlasTransposalOwnedOrder witness ordered left right = Internal.orderedAtlasTransposalOwnedOrder witness ordered left right
