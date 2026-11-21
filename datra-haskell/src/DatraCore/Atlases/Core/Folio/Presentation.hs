{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

-- | Typed finite folio presentations and their coherence laws.
module Folio.Presentation
  ( SingletonOrigin (..)
  , PageOrder (..)
  , pageOrder
  , FolioData (..)
  , FolioStep (..)
  , folioData
  , appendPageData
  , folioLengthData
  , originPageData
  , originValueData
  , originUniqueData
  , lastPageData
  , stepSource
  , identityFolioMap
  , composeFolioMaps
  , folioMapIdentity
  , folioMapComposition
  ) where

import Chain (Chain)
import Consolidation.Ordered (OrderedConsolidation, orderedSource, orderedTarget)
import Consolidation.Core
  ( Consolidation (..)
  , Coconsolidation (..)
  , applyConsolidation
  , identityConsolidation
  , composeCoconsolidations
  , coconsolidationIdentity
  , coconsolidationComposition
  , op
  , unop
  )
import Numeric.Natural (Natural)

{-@ embed Natural as int @-}
{-@ invariant {value:Natural | value >= 0} @-}

-- | The selected origin and the evidence that its carrier is a singleton.
{-@
data SingletonOrigin origin = SingletonOrigin
  { selectedOrigin :: origin
  , singletonOriginUnique :: value:origin ->
      { proof:() | value == selectedOrigin }
  }
@-}
data SingletonOrigin origin = SingletonOrigin
  { selectedOrigin :: origin
  , singletonOriginUnique :: origin -> ()
  }

-- | A proof-carrying ordered pair of indices on the spine.
{-@
data PageOrder = PageOrder
  { pageOrderSource :: Natural
  , pageOrderTarget :: { target:Natural | pageOrderSource <= target }
  }
@-}
data PageOrder = PageOrder
  { pageOrderSource :: Natural
  , pageOrderTarget :: Natural
  }
  deriving (Eq, Show)

-- | Refine two dynamic indices to a spine-order certificate.
pageOrder :: Natural -> Natural -> Maybe PageOrder
pageOrder source target
  | source <= target = Just (PageOrder source target)
  | otherwise = Nothing

-- | A nonempty sequence of chains whose generating maps retain the exact
-- source and target orders before their intermediate carriers are hidden.
{-@ data FolioData origin final where
      OriginFolio :: count:{Natural | count == 1}
        -> originPage:Chain origin -> witness:SingletonOrigin origin
        -> FolioData origin origin
      SnocPage :: step:FolioStep origin previous final
        -> FolioData origin final @-}
data FolioData origin final where
  OriginFolio
    :: Natural
    -> Chain origin
    -> SingletonOrigin origin
    -> FolioData origin origin
  SnocPage :: FolioStep origin previous final -> FolioData origin final

-- | Certify the preceding page and exact transition endpoints before the
-- intermediate carrier is hidden by 'SnocPage'.
{-@ data FolioStep origin previous final = FolioStep
      { stepLength :: {count:Natural | count > 1}
      , stepPrevious :: {pages:FolioData origin previous |
           folioLengthData pages + 1 == stepLength}
      , stepTransition :: {mapping:OrderedConsolidation final previous |
           orderedTarget mapping == lastPageData stepPrevious}
      } @-}
data FolioStep origin previous final = FolioStep
  { stepLength :: Natural
  , stepPrevious :: FolioData origin previous
  , stepTransition :: OrderedConsolidation final previous
  }

-- | Construct the singleton origin page. LiquidHaskell checks that the
-- supplied witness identifies every origin value with the selected value.
{-@
folioData
  :: page:Chain origin
  -> selectedOrigin:origin
  -> (value:origin -> { proof:() | value == selectedOrigin })
  -> {result:FolioData origin origin | folioLengthData result == 1
       && lastPageData result == page && originPageData result == page
       && originValueData result == selectedOrigin}
@-}
folioData
  :: Chain origin
  -> origin
  -> (origin -> ())
  -> FolioData origin origin
folioData page selected unique =
  OriginFolio 1 page (SingletonOrigin selected unique)

-- | Append a genuine page and its certified generating coconsolidation.
-- ALIGN: FOLIO-APPEND-ORDERED.
{-@ reflect appendPageData @-}
{-@ appendPageData :: pages:FolioData origin previous -> nextPage:Chain next
      -> transition:{OrderedConsolidation next previous |
           orderedSource transition == nextPage
           && orderedTarget transition == lastPageData pages}
      -> {result:FolioData origin next | folioLengthData result == folioLengthData pages + 1
           && lastPageData result == nextPage && originPageData result == originPageData pages
           && originValueData result == originValueData pages} @-}
appendPageData
  :: FolioData origin previous
  -> Chain next
  -> OrderedConsolidation next previous
  -> FolioData origin next
appendPageData pages _ transition =
  let step = FolioStep (folioLengthData pages + 1) pages transition
  in stepSource step `seq` SnocPage step

-- | The number of genuine pages.
{-@ reflect folioLengthData @-}
-- ALIGN: FOLIO-SEMANTIC-LENGTH.
-- ALIGN: FOLIO-LENGTH-POSITIVE.
{-@ folioLengthData :: FolioData origin final -> {n:Natural | n > 0} @-}
folioLengthData :: FolioData origin final -> Natural
folioLengthData (OriginFolio count _ _) = count
folioLengthData (SnocPage step) = stepLength step

-- | The first page.
{-@ reflect originPageData @-}
originPageData :: FolioData origin final -> Chain origin
originPageData (OriginFolio _ value _) = value
originPageData (SnocPage (FolioStep _ pages _)) = originPageData pages

-- | The distinguished value of the singleton origin page.
{-@ reflect originValueData @-}
originValueData :: FolioData origin final -> origin
originValueData (OriginFolio _ _ witness) = selectedOrigin witness
originValueData (SnocPage (FolioStep _ pages _)) = originValueData pages

-- | Every value of the origin carrier is its distinguished value.
{-@
originUniqueData
  :: pages:FolioData origin final
  -> value:origin
  -> { proof:() | value == originValueData pages }
@-}
-- ALIGN: FOLIO-ORIGIN-UNIQUE.
originUniqueData :: FolioData origin final -> origin -> ()
originUniqueData (OriginFolio _ _ witness) value =
  singletonOriginUnique witness value
originUniqueData (SnocPage (FolioStep _ pages _)) value = originUniqueData pages value

-- | The final genuine page.
{-@ reflect lastPageData @-}
lastPageData :: FolioData origin final -> Chain final
lastPageData (OriginFolio _ value _) = value
lastPageData (SnocPage step) = stepSource step

-- Keep the existential carrier behind a checked accessor in reflected clients.
-- ALIGN: FOLIO-STEP-SOURCE.
{-@ opaque-reflect stepSource @-}
{-@ stepSource :: step:FolioStep origin previous final
      -> {result:Chain final | result == orderedSource (stepTransition step)} @-}
stepSource :: FolioStep origin previous final -> Chain final
stepSource (FolioStep _ _ transition) = orderedSource transition

-- | The identity map used for every identity interval in a folio.
{-@ reflect identityFolioMap @-}
{-@ identityFolioMap :: forall <pageLe :: page -> page -> Bool>.
      Coconsolidation <pageLe, pageLe> page page @-}
identityFolioMap :: Coconsolidation page page
identityFolioMap = op identityConsolidation

-- | Identity intervals transport every page value to itself.
{-@
folioMapIdentity
  :: value:page ->
     { proof:() |
       applyConsolidation (unop identityFolioMap) value == value }
@-}
folioMapIdentity :: page -> ()
folioMapIdentity = coconsolidationIdentity

-- | The composition operation used to derive every non-adjacent folio map.
{-@ reflect composeFolioMaps @-}
{-@ composeFolioMaps :: forall
       < sourceLe :: source -> source -> Bool
       , middleLe :: middle -> middle -> Bool
       , targetLe :: target -> target -> Bool >.
      Coconsolidation <middleLe, targetLe> middle target
      -> Coconsolidation <sourceLe, middleLe> source middle
      -> Coconsolidation <sourceLe, targetLe> source target @-}
composeFolioMaps
  :: Coconsolidation middle target
  -> Coconsolidation source middle
  -> Coconsolidation source target
composeFolioMaps = composeCoconsolidations

-- | Composed intervals transport exactly by the two constituent maps.
{-@
folioMapComposition
  :: second:Coconsolidation middle target
  -> first:Coconsolidation source middle
  -> value:target
  -> { proof:() |
       applyConsolidation (unop (composeFolioMaps second first)) value
         == applyConsolidation (unop first)
              (applyConsolidation (unop second) value) }
@-}
folioMapComposition
  :: Coconsolidation middle target
  -> Coconsolidation source middle
  -> target
  -> ()
folioMapComposition = coconsolidationComposition
