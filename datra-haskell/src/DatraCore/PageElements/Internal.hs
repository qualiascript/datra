{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden representation of the category of cell occurrences.
module PageElements.Internal
  ( PageElements
  , PageElement
  , PageElementArrow
  , pageElements
  , pageElement
  , pageElementPage
  , pageElementPosition
  , withPageElement
  , pageElementArrow
  , arrowSource
  , arrowTarget
  , identityPageElementArrow
  , composePageElementArrows
  , hasPageElementArrow
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
type role PageElements nominal nominal nominal
newtype PageElements scope origin final =
  PageElements (Folio origin final)

-- | A cell together with the genuine page on which it occurs.  The cell is
-- represented by its position in that page's chain so heterogeneous page
-- carrier types do not escape.
type role PageElement nominal
data PageElement scope = PageElement
  { pageElementPage :: Natural
  , pageElementPosition :: Ordinal
  }
  deriving (Eq, Show)

-- | The unique arrow between two occurrences, when one exists.
--
-- Representation requirement: every value @f@ must have been accepted by
-- 'pageElementArrow' for the category identified by @scope@.  Thus, if
-- @x = arrowSource f@ and @y = arrowTarget f@, then:
--
-- * @pageElementPage x >= pageElementPage y@; and
-- * transporting the cell at @x@ along the folio map from @y@'s page to
--   @x@'s page has position @pageElementPosition y@ in @y@'s chain.
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
type role PageElementArrow nominal
data PageElementArrow scope = PageElementArrow
  { arrowSource :: PageElement scope
  , arrowTarget :: PageElement scope
  }
  deriving (Eq, Show)

-- | Introduce the occurrence category of a folio with a fresh abstract scope.
pageElements
  :: Folio origin final
  -> (forall scope.
        PageElements scope origin final -> result)
  -> result
pageElements pages useCategory =
  useCategory (PageElements pages)

-- | Look up an occurrence by genuine page index and position in that page's
-- chain.
--
-- Success requires both @page < folioLength pages@ and
-- @chainObjectAt pageChain position /= Nothing@.  On success the result @x@
-- satisfies:
--
-- @
-- pageElementPage x == page
-- pageElementPosition x == position
-- @
pageElement
  :: PageElements scope origin final
  -> Natural
  -> Ordinal
  -> Maybe (PageElement scope)
pageElement (PageElements pages) page position = do
  present <- withPageAt pages page $ \pageChain ->
    isJust (chainObjectAt pageChain position)
  if present
    then Just (PageElement page position)
    else Nothing

-- | Recover the existential page carrier and cell represented by an
-- occurrence for the duration of a rank-2 callback.
withPageElement
  :: PageElements scope origin final
  -> PageElement scope
  -> (forall cell. Chain cell -> cell -> result)
  -> Maybe result
withPageElement
  (PageElements pages)
  (PageElement page position)
  useCell =
    join $ withPageAt pages page $ \pageChain ->
      useCell pageChain <$> chainObjectAt pageChain position

-- | Construct an arrow when folio transport sends the source cell exactly to
-- the target cell.  Occurrence arrows follow the opposite spine, so they run
-- from later pages to earlier pages.
--
-- More precisely, let @s@ be the cell represented by @source@, @targetChain@
-- the chain at @pageElementPage target@, and @q@ the coconsolidation returned
-- by:
--
-- @
-- withFolioMap pages (pageElementPage target) (pageElementPage source)
-- @
--
-- This function returns @Just f@ exactly when the page map exists and:
--
-- @
-- chainPosition targetChain
--   (runConsolidationTransport (transportCoconsolidation q) s)
--   == pageElementPosition target
-- @
--
-- A successful result must additionally satisfy
-- @arrowSource f == source@ and @arrowTarget f == target@.  These are the
-- arrow-construction obligations to encode when LiquidHaskell support is
-- added.
pageElementArrow
  :: PageElements scope origin final
  -> PageElement scope
  -> PageElement scope
  -> Maybe (PageElementArrow scope)
pageElementArrow
  (PageElements pages)
  source
  target
  | pageElementPage source < pageElementPage target = Nothing
  | otherwise = do
      transportedExactly <-
        withFolioMap
          pages
          (pageElementPage target)
          (pageElementPage source)
          (transportMatches source target)
      if transportedExactly
        then Just (PageElementArrow source target)
        else Nothing
  where
    transportMatches
      laterOccurrence
      earlierOccurrence
      earlierPage
      laterPage
      pageMap =
        case chainObjectAt laterPage (pageElementPosition laterOccurrence) of
          Nothing -> False
          Just laterCell ->
            let earlierCell =
                  runConsolidationTransport
                    (transportCoconsolidation pageMap)
                    laterCell
            in chainPosition earlierPage earlierCell
                 == pageElementPosition earlierOccurrence

-- | The identity arrow on an occurrence.
--
-- For every occurrence @x@ constructed in @category@, future verification
-- must establish all three identity requirements:
--
-- @
-- arrowSource (identityPageElementArrow x) == x
-- arrowTarget (identityPageElementArrow x) == x
-- pageElementArrow category x x
--   == Just (identityPageElementArrow x)
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
--   == pageElementPosition x
-- @
--
-- It is intentionally documented rather than refined for now.
identityPageElementArrow
  :: PageElement scope
  -> PageElementArrow scope
identityPageElementArrow occurrence =
  PageElementArrow occurrence occurrence

-- | Compose in categorical order: @composePageElementArrows category g f@
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
-- T(pageElementPage x, pageElementPage z) xCell
--   == T(pageElementPage y, pageElementPage z)
--        (T(pageElementPage x, pageElementPage y) xCell)
-- @
--
-- Both sides must have position @pageElementPosition z@ in @z@'s chain.  The
-- implementation rechecks the left side; LiquidHaskell must eventually prove
-- from this equation and the two input-arrow invariants that the check cannot
-- fail.
--
-- For every composable @f@, @g@, and @h@, verification must also establish:
--
-- @
-- composePageElementArrows category
--   (identityPageElementArrow (arrowTarget f)) f == Just f
--
-- composePageElementArrows category f
--   (identityPageElementArrow (arrowSource f)) == Just f
--
-- If
--   gf == the arrow in composePageElementArrows category g f
-- and
--   hg == the arrow in composePageElementArrows category h g,
-- then
--   composePageElementArrows category h gf
--     == composePageElementArrows category hg f
-- @
composePageElementArrows
  :: PageElements scope origin final
  -> PageElementArrow scope
  -> PageElementArrow scope
  -> Maybe (PageElementArrow scope)
composePageElementArrows category second first
  | arrowTarget first /= arrowSource second = Nothing
  | otherwise =
      pageElementArrow category (arrowSource first) (arrowTarget second)

-- | Decide whether the category contains an arrow between two occurrences.
hasPageElementArrow
  :: PageElements scope origin final
  -> PageElement scope
  -> PageElement scope
  -> Bool
hasPageElementArrow category source target =
  isJust (pageElementArrow category source target)
