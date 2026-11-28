{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}

-- | Stable Atlas transversals: Atlas transversals whose object action sends the
-- source extent cell to the target extent cell.
module StableAtlasTransversal
  ( StableAtlasTransversal
  , stableAtlasTransversal
  , stableAtlasTransversalTransversal
  , stableAtlasTransversalOrderedTransposal
  , stableAtlasTransversalTransposal
  , stableAtlasTransversalHom
  , stableCoalitionSourceOwner, stableCoalitionTargetOwner, stableCoalitionOwnersEmpty
  , ScopedInsertionData, stableCoalitionInsertionData
  , scopedInsertionSource, scopedInsertionTarget, scopedInsertionValue
  , scopedInsertionForwardCodes, scopedInsertionInverseCodes
  , scopedInsertionForwardObservation, scopedInsertionInverseObservation
  , coalitionCodeExtensionality, coalitionMaybeCode, coalitionIdentityCode
  , stableAtlasTransversalSourceWitness
  , withStableAtlasTransversalCoalitionInsertion
  , withStableAtlasTransversalCoalitionPreimage
  , stableAtlasTransversalPreservesExtent
  -- Identity exposes both scalar code models; normalization preserves their
  -- pointwise forward and inverse observations alongside the endpoint owners.
  , identityStableAtlasTransversal
  , composeStableAtlasTransversals
  , normalizedForwardCodes, normalizedInverseCodes
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
  , normalizedForwardCodes, normalizedInverseCodes
  , identityStableAtlasTransversal
  , mapStableAtlasTransversalArrow
  , mapStableAtlasTransversalCoveredPageElement
  , mapStableAtlasTransversalData
  , mapStableAtlasTransversalElement
  , mapStableAtlasTransversalObject
  , stableAtlasTransversal
  , stableAtlasTransversalHom
  , stableCoalitionSourceOwner, stableCoalitionTargetOwner, stableCoalitionOwnersEmpty
  , ScopedInsertionData, stableCoalitionInsertionData
  , scopedInsertionSource, scopedInsertionTarget, scopedInsertionValue
  , scopedInsertionForwardCodes, scopedInsertionInverseCodes
  , scopedInsertionForwardObservation, scopedInsertionInverseObservation
  , coalitionCodeExtensionality, coalitionMaybeCode, coalitionIdentityCode
  , stableAtlasTransversalSourceWitness
  , withStableAtlasTransversalCoalitionInsertion
  , withStableAtlasTransversalCoalitionPreimage
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
