{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden representation of the category of cell occurrences.
module CellOccurrence.Internal
  ( CellOccurrenceCategory
  , CellOccurrence
  , CellOccurrenceArrow
  , cellOccurrenceCategory
  , cellOccurrence
  , occurrencePage
  , occurrencePosition
  , withCellOccurrence
  , cellOccurrenceArrow
  , arrowSource
  , arrowTarget
  , identityCellOccurrenceArrow
  , composeCellOccurrenceArrows
  , hasCellOccurrenceArrow
  ) where

import Chain (Chain, chainObjectAt, chainPosition)
import Consolidation
  ( runConsolidationTransport
  , transportCoconsolidation
  )
import DatraOrdinal (Ordinal)
import Folio
  ( Folio
  , withFolioMap
  , withPageAt
  )
import Numeric.Natural (Natural)

import Control.Monad (join)
import Data.Maybe (isJust)

-- | A folio viewed as its category of cell occurrences.  The generative
-- @scope@ prevents occurrences belonging to different folios from being
-- compared or composed.
type role CellOccurrenceCategory nominal nominal nominal
newtype CellOccurrenceCategory scope origin final =
  CellOccurrenceCategory (Folio origin final)

-- | A cell together with the genuine page on which it occurs.  The cell is
-- represented by its position in that page's chain so heterogeneous page
-- carrier types do not escape.
type role CellOccurrence nominal
data CellOccurrence scope = CellOccurrence
  { occurrencePage :: Natural
  , occurrencePosition :: Ordinal
  }
  deriving (Eq, Show)

-- | The unique arrow between two occurrences, when one exists.
--
-- Representation requirement: every value @f@ must have been accepted by
-- 'cellOccurrenceArrow' for the category identified by @scope@.  Thus, if
-- @x = arrowSource f@ and @y = arrowTarget f@, then:
--
-- * @occurrencePage x >= occurrencePage y@; and
-- * transporting the cell at @x@ along the folio map from @y@'s page to
--   @x@'s page has position @occurrencePosition y@ in @y@'s chain.
--
-- Thinness requirement: for any @f@ and @g@ in the same scope,
--
-- @
-- arrowSource f == arrowSource g && arrowTarget f == arrowTarget g
--   ==> f == g
-- @
--
-- This follows from the source-and-target-only representation, but is not yet
-- stated as a LiquidHaskell refinement.
type role CellOccurrenceArrow nominal
data CellOccurrenceArrow scope = CellOccurrenceArrow
  { arrowSource :: CellOccurrence scope
  , arrowTarget :: CellOccurrence scope
  }
  deriving (Eq, Show)

-- | Introduce the occurrence category of a folio with a fresh abstract scope.
cellOccurrenceCategory
  :: Folio origin final
  -> (forall scope.
        CellOccurrenceCategory scope origin final -> result)
  -> result
cellOccurrenceCategory pages useCategory =
  useCategory (CellOccurrenceCategory pages)

-- | Look up an occurrence by genuine page index and position in that page's
-- chain.
--
-- Success requires both @page < folioLength pages@ and
-- @chainObjectAt pageChain position /= Nothing@.  On success the result @x@
-- satisfies:
--
-- @
-- occurrencePage x == page
-- occurrencePosition x == position
-- @
cellOccurrence
  :: CellOccurrenceCategory scope origin final
  -> Natural
  -> Ordinal
  -> Maybe (CellOccurrence scope)
cellOccurrence (CellOccurrenceCategory pages) page position = do
  present <- withPageAt pages page $ \pageChain ->
    isJust (chainObjectAt pageChain position)
  if present
    then Just (CellOccurrence page position)
    else Nothing

-- | Recover the existential page carrier and cell represented by an
-- occurrence for the duration of a rank-2 callback.
withCellOccurrence
  :: CellOccurrenceCategory scope origin final
  -> CellOccurrence scope
  -> (forall cell. Chain cell -> cell -> result)
  -> Maybe result
withCellOccurrence
  (CellOccurrenceCategory pages)
  (CellOccurrence page position)
  useCell =
    join $ withPageAt pages page $ \pageChain ->
      useCell pageChain <$> chainObjectAt pageChain position

-- | Construct an arrow when folio transport sends the source cell exactly to
-- the target cell.  Occurrence arrows follow the opposite spine, so they run
-- from later pages to earlier pages.
--
-- More precisely, let @s@ be the cell represented by @source@, @targetChain@
-- the chain at @occurrencePage target@, and @q@ the coconsolidation returned
-- by:
--
-- @
-- withFolioMap pages (occurrencePage target) (occurrencePage source)
-- @
--
-- This function returns @Just f@ exactly when the page map exists and:
--
-- @
-- chainPosition targetChain
--   (runConsolidationTransport (transportCoconsolidation q) s)
--   == occurrencePosition target
-- @
--
-- A successful result must additionally satisfy
-- @arrowSource f == source@ and @arrowTarget f == target@.  These are the
-- arrow-construction obligations to encode when LiquidHaskell support is
-- added.
cellOccurrenceArrow
  :: CellOccurrenceCategory scope origin final
  -> CellOccurrence scope
  -> CellOccurrence scope
  -> Maybe (CellOccurrenceArrow scope)
cellOccurrenceArrow
  (CellOccurrenceCategory pages)
  source
  target
  | occurrencePage source < occurrencePage target = Nothing
  | otherwise = do
      transportedExactly <-
        withFolioMap
          pages
          (occurrencePage target)
          (occurrencePage source)
          (transportMatches source target)
      if transportedExactly
        then Just (CellOccurrenceArrow source target)
        else Nothing
  where
    transportMatches
      laterOccurrence
      earlierOccurrence
      earlierPage
      laterPage
      pageMap =
        case chainObjectAt laterPage (occurrencePosition laterOccurrence) of
          Nothing -> False
          Just laterCell ->
            let earlierCell =
                  runConsolidationTransport
                    (transportCoconsolidation pageMap)
                    laterCell
            in chainPosition earlierPage earlierCell
                 == occurrencePosition earlierOccurrence

-- | The identity arrow on an occurrence.
--
-- For every occurrence @x@ constructed in @category@, future verification
-- must establish all three identity requirements:
--
-- @
-- arrowSource (identityCellOccurrenceArrow x) == x
-- arrowTarget (identityCellOccurrenceArrow x) == x
-- cellOccurrenceArrow category x x
--   == Just (identityCellOccurrenceArrow x)
-- @
--
-- The final equation depends on the folio identity map transporting @x@'s
-- cell to itself.  Concretely, if @xCell@ is @x@'s represented cell and
-- @xChain@ is its page chain, the missing transport proof is:
--
-- @
-- chainPosition xChain
--   (runConsolidationTransport
--     (transportCoconsolidation identityPageMap) xCell)
--   == occurrencePosition x
-- @
--
-- It is intentionally documented rather than refined for now.
identityCellOccurrenceArrow
  :: CellOccurrence scope
  -> CellOccurrenceArrow scope
identityCellOccurrenceArrow occurrence =
  CellOccurrenceArrow occurrence occurrence

-- | Compose in categorical order: @composeCellOccurrenceArrows category g f@
-- means @g . f@.
--
-- The boundary requirement is @arrowTarget f == arrowSource g@.  A mismatch
-- must return 'Nothing'.  When the boundary matches, categorical closure
-- requires a result @Just composite@ satisfying:
--
-- @
-- arrowSource composite == arrowSource f
-- arrowTarget composite == arrowTarget g
-- @
--
-- Closure relies on folio transport composition: transporting the source cell
-- first as witnessed by @f@ and then as witnessed by @g@ must equal direct
-- transport between the outer pages.  If @x = arrowSource f@,
-- @y = arrowTarget f = arrowSource g@, @z = arrowTarget g@, and @T(a,b)@
-- denotes folio transport from page @a@ to the earlier page @b@, the required
-- equation is:
--
-- @
-- T(occurrencePage x, occurrencePage z) xCell
--   == T(occurrencePage y, occurrencePage z)
--        (T(occurrencePage x, occurrencePage y) xCell)
-- @
--
-- Both sides must have position @occurrencePosition z@ in @z@'s chain.  The
-- implementation rechecks the left side; LiquidHaskell must eventually prove
-- from this equation and the two input-arrow invariants that the check cannot
-- fail.
--
-- For every composable @f@, @g@, and @h@, verification must also establish:
--
-- @
-- composeCellOccurrenceArrows category
--   (identityCellOccurrenceArrow (arrowTarget f)) f == Just f
--
-- composeCellOccurrenceArrows category f
--   (identityCellOccurrenceArrow (arrowSource f)) == Just f
--
-- If
--   gf == the arrow in composeCellOccurrenceArrows category g f
-- and
--   hg == the arrow in composeCellOccurrenceArrows category h g,
-- then
--   composeCellOccurrenceArrows category h gf
--     == composeCellOccurrenceArrows category hg f
-- @
composeCellOccurrenceArrows
  :: CellOccurrenceCategory scope origin final
  -> CellOccurrenceArrow scope
  -> CellOccurrenceArrow scope
  -> Maybe (CellOccurrenceArrow scope)
composeCellOccurrenceArrows category second first
  | arrowTarget first /= arrowSource second = Nothing
  | otherwise =
      cellOccurrenceArrow category (arrowSource first) (arrowTarget second)

-- | Decide whether the category contains an arrow between two occurrences.
hasCellOccurrenceArrow
  :: CellOccurrenceCategory scope origin final
  -> CellOccurrence scope
  -> CellOccurrence scope
  -> Bool
hasCellOccurrenceArrow category source target =
  isJust (cellOccurrenceArrow category source target)
