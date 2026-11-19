{-# LANGUAGE CPP #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ qualif Accepted(v:@(0), p:func(0, [@(0); bool])) { p v } @-}

-- | Shared origin and append operations retaining accepted page carriers.
module Folio.Assembly (collapseToOrigin, appendOrderedPage) where

import Chain.Internal (Chain, chainPosition)
import Chain.Order (chainPrecedes)
import Consolidation.Core (restrictedConsolidation)
import Consolidation.Ordered (OrderedConsolidation, orderedSource, orderedTarget, orderedConsolidation)
import DatraOrdinal.Laws (ordinalLTIrreflexive)
import Folio.Presentation (FolioData, appendPageData, folioLengthData, lastPageData)

-- ALIGN: FOLIO-COLLAPSE-ORIGIN.
{-@ collapseToOrigin :: contains:(a -> Bool)
      -> source:Chain {cell:a | contains cell} -> target:Chain ()
      -> chosen:{a | contains chosen}
      -> {result:OrderedConsolidation {cell:a | contains cell} () |
           orderedSource result == source && orderedTarget result == target} @-}
collapseToOrigin :: (a -> Bool) -> Chain a -> Chain ()
  -> a -> OrderedConsolidation a ()
{-@ ple collapseToOrigin @-}
collapseToOrigin contains source target chosen =
  orderedConsolidation source target
    (restrictedConsolidation contains unitContains collapseValue (collapseChosen chosen)
      (collapseMonotone target) (collapseInverse chosen))

{-@ reflect unitContains @-}
unitContains :: () -> Bool
unitContains () = True

{-@ reflect collapseValue @-}
collapseValue :: a -> ()
collapseValue _ = ()

{-@ reflect collapseChosen @-}
collapseChosen :: a -> () -> a
collapseChosen chosen () = chosen

{-@ collapseInverse :: chosen:a -> value:() -> {collapseValue (collapseChosen chosen value) == value} @-}
{-@ ple collapseInverse @-}
collapseInverse :: a -> () -> ()
collapseInverse _ () = ()

{-@ collapseMonotone :: target:Chain () -> first:a -> mappedFirst:() -> second:a
      -> {result:() | result == collapseValue second && unitContains result && chainPrecedes target mappedFirst result} @-}
{-@ ple collapseMonotone @-}
collapseMonotone :: Chain () -> a -> () -> a -> ()
collapseMonotone target _ () _ = ordinalLTIrreflexive (chainPosition target ()) `seq` ()

-- ALIGN: FOLIO-APPEND-ACCEPTED.
{-@ appendOrderedPage :: previousContains:(a -> Bool) -> nextContains:(b -> Bool)
      -> pages:FolioData origin {cell:a | previousContains cell}
      -> transition:{OrderedConsolidation {cell:b | nextContains cell} {cell:a | previousContains cell} |
           orderedTarget transition == lastPageData pages}
      -> {result:FolioData origin {cell:b | nextContains cell} |
           folioLengthData result == folioLengthData pages + 1 && lastPageData result == orderedSource transition} @-}
appendOrderedPage :: (a -> Bool) -> (b -> Bool)
  -> FolioData origin a -> OrderedConsolidation b a -> FolioData origin b
appendOrderedPage _ _ pages transition = appendPageData pages (orderedSource transition) transition
