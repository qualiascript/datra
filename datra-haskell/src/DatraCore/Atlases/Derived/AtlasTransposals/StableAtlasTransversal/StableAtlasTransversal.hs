-- | Stable Atlas transversals: Atlas transversals whose object action sends the
-- source extent cell to the target extent cell.
module StableAtlasTransversal
  ( StableAtlasTransversal
  , stableAtlasTransversal
  , stableAtlasTransversalTransversal
  , stableAtlasTransversalOrderedTransposal
  , stableAtlasTransversalTransposal
  , stableAtlasTransversalHom
  , stableAtlasTransversalSourceWitness
  , stableAtlasTransversalPreservesExtent
  , identityStableAtlasTransversal
  , composeStableAtlasTransversals
  , mapStableAtlasTransversalObject
  , stableAtlasTransversalPreimage
  , stableAtlasTransversalLeftInverse
  , stableAtlasTransversalPreservesOrder
  , stableAtlasTransversalPreservesCoverage
  , stableAtlasTransversalPagination
  , mapStableAtlasTransversalElement
  , mapStableAtlasTransversalArrow
  , mapStableAtlasTransversalData
  , mapStableAtlasTransversalCoveredPageElement
  ) where

import StableAtlasTransversal.Internal
  ( StableAtlasTransversal
  , composeStableAtlasTransversals
  , identityStableAtlasTransversal
  , mapStableAtlasTransversalArrow
  , mapStableAtlasTransversalCoveredPageElement
  , mapStableAtlasTransversalData
  , mapStableAtlasTransversalElement
  , mapStableAtlasTransversalObject
  , stableAtlasTransversal
  , stableAtlasTransversalHom
  , stableAtlasTransversalSourceWitness
  , stableAtlasTransversalLeftInverse
  , stableAtlasTransversalOrderedTransposal
  , stableAtlasTransversalPagination
  , stableAtlasTransversalPreimage
  , stableAtlasTransversalPreservesCoverage
  , stableAtlasTransversalPreservesExtent
  , stableAtlasTransversalPreservesOrder
  , stableAtlasTransversalTransposal
  , stableAtlasTransversalTransversal
  )
