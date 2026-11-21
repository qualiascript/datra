{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}
-- All carrier and law contracts are explicit. Avoid inferring refinements on
-- the partially applied carrier family as though it were a cell datum.
{-@ LIQUID "--fast" @-}

-- | Assemble the certified cached action through the public Atlas interface.
module Charter.LiquidInternal (chartedPresentation) where

import Atlas
  ( Atlas, AtlasPresentation, atlasPresentationForPredicate
  , atlasPresentationPagination, atlasPresentationAction, atlasPagination )
import Atlas.Construction (AtlasDataConstruction (..))
import Charter.Data
  ( ChartedDatum, chartedDatumValid, chartedAction
  , chartedNormalizedIdentityLaw, chartedNormalizedCompositionLaw
  , chartedNormalizedCoherenceLaw, chartedNormalizedDisjointLaw )

{-@ opaque-reflect chartedAction @-}

{-@ opaque-reflect atlasPresentationPagination @-}
{-@ opaque-reflect atlasPresentationAction @-}

-- | Certify the owning pagination and the complete normalized data assignment.
-- ALIGN: CHARTER-PRESENTATION-INTERPRETATION.
{-@ chartedPresentation :: owner:Atlas a s d o f
      -> {presentation:AtlasPresentation s (ChartedDatum a s d) o f |
           atlasPresentationPagination presentation == atlasPagination owner
           && atlasPresentationAction presentation == chartedAction owner} @-}
chartedPresentation :: Atlas a s d o f -> AtlasPresentation s (ChartedDatum a s d) o f
chartedPresentation owner =
  atlasPresentationForPredicate (atlasPagination owner) (chartedDatumValid owner) (chartedAction owner)
    (chartedNormalizedIdentityLaw owner)
    (chartedNormalizedCompositionLaw owner)
    (chartedNormalizedCoherenceLaw owner)
    (chartedNormalizedDisjointLaw owner)

-- The canonical cached-data recipe is fixed for this data-family constructor.
instance AtlasDataConstruction ChartedDatum where
  atlasDataPresentation = chartedPresentation
