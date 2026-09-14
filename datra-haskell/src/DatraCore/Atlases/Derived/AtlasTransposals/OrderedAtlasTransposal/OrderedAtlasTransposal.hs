-- | Atlas transposals whose object maps preserve the strict Atlas order.
--
-- This is the first restriction used to build Atlas transversals: it adds the
-- ordering clause from Lean's @IsTraversal@, but intentionally does not add
-- the covered-data clause.
module OrderedAtlasTransposal
  ( OrderedAtlasTransposal
  , orderedAtlasTransposal
  , orderedAtlasTransposalTransposal
  , orderedAtlasTransposalHom
  , orderedAtlasTransposalPreservesOrder
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
  , orderedAtlasTransposal
  , orderedAtlasTransposalHom
  , orderedAtlasTransposalLeftInverse
  , orderedAtlasTransposalPagination
  , orderedAtlasTransposalPreimage
  , orderedAtlasTransposalPreservesOrder
  , orderedAtlasTransposalTransposal
  )
