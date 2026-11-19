{-# LANGUAGE CPP #-}
#include "../../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ qualif MergeAccepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | The checked insertion carried by an actual full-spine merge arrow.
module AtlasMerge.Action (mergeDataMap) where

import Atlas.Internal (Atlas)
import AtlasMerge.Data (AtlasMergeDatum, mergeDatumInsertion)
import AtlasMerge.Resolution (mergeCellContains)
import AtlasMerge.Transport (mergeOccurrenceTraceValid, mergeCellContainsPreserved)
import DomanialInsertion.Core (DomanialInsertion)
import PageElements.Structure (PageElementArrow, arrowSource, arrowTarget)

-- ALIGN: MERGE-DATA-INSERTION.
-- ALIGN: MERGE-DATA-INTERPRETATION.
-- ALIGN: MERGE-DATA-IDENTITY.
-- ALIGN: MERGE-DATA-COMPOSITION.
-- ALIGN: MERGE-RESOLVED-ARROW.
-- ALIGN: MERGE-ATLAS-DATA-INTERPRETATION.
-- ALIGN: MERGE-BOUQUET-DATA-NATURALITY.
-- ALIGN: MERGE-RAW-DATA-INSERTION.
{-@ mergeDataMap :: left:Atlas la ls ld lo lf -> right:Atlas ra rs rd ro rf
      -> arrow:{PageElementArrow ms source target |
           mergeOccurrenceTraceValid left right (arrowSource arrow)
           && mergeOccurrenceTraceValid left right (arrowTarget arrow)}
      -> DomanialInsertion
           ({datum:AtlasMergeDatum source | mergeCellContains left right (arrowSource arrow) datum})
           ({datum:AtlasMergeDatum target | mergeCellContains left right (arrowTarget arrow) datum}) @-}
mergeDataMap :: Atlas la ls ld lo lf -> Atlas ra rs rd ro rf
  -> PageElementArrow ms source target
  -> DomanialInsertion (AtlasMergeDatum source) (AtlasMergeDatum target)
mergeDataMap left right arrow =
  mergeDatumInsertion
    (mergeCellContains left right (arrowSource arrow))
    (mergeCellContains left right (arrowTarget arrow))
    (mergeCellContainsPreserved left right arrow)
