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
  , pageElementArrowEndpoints
  , pageElementArrowThin
  , pageElementArrowLeftIdentity
  , pageElementArrowRightIdentity
  , pageElementArrowAssociativity
  ) where

import Chain (Chain, chainObjectAt)
import DatraOrdinal (Ordinal)
import Data.Kind (Type)
import Folio
  ( Folio
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
  )

import Control.Monad (join)
import Data.Maybe (isJust)

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
pageElement
  :: PageElements scope origin final
  -> Natural
  -> Ordinal
  -> Maybe (SomePageElement scope)
pageElement (PageElements pages) page position = do
  present <- withPageAt pages page $ \pageChain ->
    isJust (chainObjectAt pageChain position)
  if present
    then Just (SomePageElement (pageElementAt page position))
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
