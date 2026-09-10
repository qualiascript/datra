{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden representation of the category of cell occurrences.
module PageElements.Internal
  ( PageElements
  , PageElement
  , SomePageElement (..)
  , PageElementArrow
  , pageElements
  , pageElement
  , pageElementPage
  , pageElementPosition
  , withPageElement
  , withPageElementValue
  , pageElementArrow
  , pageElementTransported
  , arrowSource
  , arrowTarget
  , identityPageElementArrow
  , composePageElementArrows
  , pageElementArrowEndpoints
  , pageElementArrowThin
  , pageElementArrowLeftIdentity
  , pageElementArrowRightIdentity
  , pageElementArrowAssociativity
  ) where

import Chain (Chain, chainObjectAt, chainPosition)
import Consolidation
  ( runConsolidationTransport
  , transportCoconsolidation
  )
import DatraOrdinal (Ordinal)
import Data.Kind (Type)
import Folio
  ( Folio
  , withFolioMap
  , withPageAt
  )
import Numeric.Natural (Natural)
import PageElements.LiquidInternal
  ( PageElement (..)
  , PageElementArrow
  , arrowSource
  , arrowTarget
  , composePageElementArrows
  , identityPageElementArrow
  , pageElementAt
  , pageElementArrow
  , pageElementArrowAssociativity
  , pageElementArrowEndpoints
  , pageElementArrowLeftIdentity
  , pageElementArrowRightIdentity
  , pageElementArrowThin
  , pageElementTransported
  )

import Control.Monad (join)

-- | A folio viewed as its category of cell occurrences.  The generative
-- @scope@ prevents occurrences belonging to different folios from being
-- compared or composed.
type role PageElements nominal nominal nominal
newtype PageElements (scope :: Type) origin final =
  PageElements (Folio origin final)

-- | A page element whose fresh object identity is existentially hidden.
type role SomePageElement nominal
data SomePageElement (scope :: Type) where
  SomePageElement :: PageElement scope object -> SomePageElement scope

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
--
-- Its hidden trace is computed from the folio itself: entry @i@ is the exact
-- cell obtained by transporting the requested cell to page @page - i@. This is
-- the runtime fact used by the LiquidHaskell arrow refinement.
pageElement
  :: PageElements scope origin final
  -> Natural
  -> Ordinal
  -> Maybe (SomePageElement scope)
pageElement (PageElements pages) page position = do
  trace <- pageElementTraceAt pages page position
  case trace of
    [] -> Nothing
    currentPosition : earlierPositions ->
      Just
        (SomePageElement
          (pageElementAt page currentPosition earlierPositions))

-- | Build the complete sequence of exact adjacent transports from one cell
-- back through every earlier page to the origin.  The head is the requested
-- occurrence; every following position is computed using the corresponding
-- coconsolidation in the folio.
pageElementTraceAt
  :: Folio origin final
  -> Natural
  -> Ordinal
  -> Maybe [Ordinal]
pageElementTraceAt pages 0 position = do
  cellExists <- withPageAt pages 0 $ \pageChain ->
    case chainObjectAt pageChain position of
      Just _ -> True
      Nothing -> False
  if cellExists then Just [position] else Nothing
pageElementTraceAt pages page position = do
  earlierPosition <- previousPagePosition pages page position
  earlierTrace <- pageElementTraceAt pages (page - 1) earlierPosition
  pure (position : earlierTrace)

-- | Transport one cell position across one adjacent reverse-spine arrow.
previousPagePosition
  :: Folio origin final
  -> Natural
  -> Ordinal
  -> Maybe Ordinal
previousPagePosition pages laterPage position
  | laterPage == 0 = Nothing
  | otherwise =
      join $ withFolioMap pages (laterPage - 1) laterPage $
        \earlierChain laterChain pageMap -> do
          laterCell <- chainObjectAt laterChain position
          let earlierCell =
                runConsolidationTransport
                  (transportCoconsolidation pageMap)
                  laterCell
          pure (chainPosition earlierChain earlierCell)

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
  (PageElement page position _)
  useCell =
    join $ withPageAt pages page $ \pageChain ->
      useCell pageChain <$> chainObjectAt pageChain position
