{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden representation of the category of cell occurrences.
module PageElements.Internal
  ( PageElements
  , PageElement
  , SomePageElement
  , PageElementArrow
  , pageElements
  , pageElement
  , pageElementPage
  , pageElementPosition
  , withPageElement
  , withPageElementValue
  , pageElementArrow
  , arrowSource
  , arrowTarget
  , identityPageElementArrow
  , composePageElementArrows
  ) where

import Chain (Chain, chainObjectAt)
import DatraOrdinal (Ordinal)
import Data.Kind (Type)
import Folio
  ( Folio
  , withPageAt
  )
import Numeric.Natural (Natural)

import Control.Monad (join)
import Data.Maybe (isJust)

-- | A folio viewed as its category of cell occurrences.  The generative
-- @scope@ prevents occurrences belonging to different folios from being
-- compared or composed.
type role PageElements nominal nominal nominal
newtype PageElements (scope :: Type) origin final =
  PageElements (Folio origin final)

-- | A cell together with the genuine page on which it occurs.  The cell is
-- represented by its position in that page's chain so heterogeneous page
-- carrier types do not escape.  The @object@ parameter gives this particular
-- category object a type-level identity used to align arrow composition.
type role PageElement nominal nominal
data PageElement (scope :: Type) (object :: Type) = PageElement
  { pageElementPage :: Natural
  , pageElementPosition :: Ordinal
  }
  deriving (Eq, Show)

-- | A page element whose fresh object identity is existentially hidden.
type role SomePageElement nominal
data SomePageElement (scope :: Type) where
  SomePageElement :: PageElement scope object -> SomePageElement scope

-- | The unique arrow between two occurrences, when one exists.
--
-- Representation requirement: every value @f@ must have been constructed by
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
type role PageElementArrow nominal nominal nominal
data PageElementArrow
  (scope :: Type)
  (source :: Type)
  (target :: Type) = PageElementArrow
  { arrowSource :: PageElement scope source
  , arrowTarget :: PageElement scope target
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
  -> Maybe (SomePageElement scope)
pageElement (PageElements pages) page position = do
  present <- withPageAt pages page $ \pageChain ->
    isJust (chainObjectAt pageChain position)
  if present
    then Just (SomePageElement (PageElement page position))
    else Nothing

-- | Eliminate the existential object identity of a dynamically looked-up page
-- element.  The callback receives a fresh @object@ type that can index total
-- arrow operations without escaping its scope.
withPageElement
  :: SomePageElement scope
  -> (forall object. PageElement scope object -> result)
  -> result
withPageElement (SomePageElement element) useElement = useElement element

-- | Recover the existential page carrier and cell value represented by a page
-- element for the duration of a rank-2 callback.
withPageElementValue
  :: PageElements scope origin final
  -> PageElement scope object
  -> (forall cell. Chain cell -> cell -> result)
  -> Maybe result
withPageElementValue
  (PageElements pages)
  (PageElement page position)
  useCell =
    join $ withPageAt pages page $ \pageChain ->
      useCell pageChain <$> chainObjectAt pageChain position

-- | Construct an arrow from a source page element to a target page element.
-- Occurrence arrows follow the opposite spine, so they run from later pages
-- to earlier pages.
--
-- More precisely, let @s@ be the cell represented by @source@, @targetChain@
-- the chain at @pageElementPage target@, and @q@ the coconsolidation returned
-- by:
--
-- @
-- withFolioMap pages (pageElementPage target) (pageElementPage source)
-- @
--
-- Construction requirement: the caller must only use this function when the
-- page map exists and:
--
-- @
-- chainPosition targetChain
--   (runConsolidationTransport (transportCoconsolidation q) s)
--   == pageElementPosition target
-- @
--
-- The result satisfies
-- @arrowSource f == source@ and @arrowTarget f == target@.  These are the
-- arrow-construction obligations to encode when LiquidHaskell support is
-- added.  Until then they are documented preconditions, matching the proof
-- supplied to @CategoryOfElements.homMk@ in Lean.
pageElementArrow
  :: PageElements scope origin final
  -> PageElement scope source
  -> PageElement scope target
  -> PageElementArrow scope source target
pageElementArrow _ = PageElementArrow

-- | The identity arrow on an occurrence.
--
-- For every occurrence @x@ constructed in @category@, future verification
-- must establish all three identity requirements:
--
-- @
-- arrowSource (identityPageElementArrow x) == x
-- arrowTarget (identityPageElementArrow x) == x
-- pageElementArrow category x x == identityPageElementArrow x
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
  :: PageElement scope object
  -> PageElementArrow scope object object
identityPageElementArrow occurrence =
  PageElementArrow occurrence occurrence

-- | Compose in categorical order: @composePageElementArrows g f@ means
-- @g . f@.  The arrow indices require @f@'s target to be exactly @g@'s
-- source, so composition is total and needs no runtime boundary check.
--
-- The result @composite@ satisfies:
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
-- eventual LiquidHaskell refinement must prove this equation from the two
-- input-arrow invariants.
--
-- For every composable @f@, @g@, and @h@, verification must also establish:
--
-- @
-- composePageElementArrows
--   (identityPageElementArrow (arrowTarget f)) f == f
--
-- composePageElementArrows f
--   (identityPageElementArrow (arrowSource f)) == f
--
-- If
--   gf == composePageElementArrows g f
-- and
--   hg == composePageElementArrows h g,
-- then
--   composePageElementArrows h gf == composePageElementArrows hg f
-- @
composePageElementArrows
  :: PageElementArrow scope middle target
  -> PageElementArrow scope source middle
  -> PageElementArrow scope source target
composePageElementArrows second first =
  PageElementArrow (arrowSource first) (arrowTarget second)
