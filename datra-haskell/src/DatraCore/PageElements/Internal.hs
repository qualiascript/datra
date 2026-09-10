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
  , somePageElementPrecedes
  , somePageElementTransported
  , somePageElementTransportedReflexive
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
import Folio.Internal
  ( Folio
  , lastChain
  , withPageDataAt
  )
import Folio.LiquidInternal (FolioData (..))
import Numeric.Natural (Natural)
import PageElements.LiquidInternal
  ( PageElement (..)
  , PageElementArrow
  , SomePageElement (..)
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
  , somePageElementPrecedes
  , somePageElementTransported
  , somePageElementTransportedReflexive
  )

-- | A folio viewed as its category of cell occurrences.  The generative
-- @scope@ prevents occurrences belonging to different folios from being
-- compared or composed.
type role PageElements nominal nominal nominal
newtype PageElements (scope :: Type) origin final =
  PageElements (Folio origin final)

-- | Introduce the occurrence category of a folio with a fresh abstract scope.
pageElements
  :: Folio origin final
  -> (forall scope.
        PageElements scope origin final -> result)
  -> result
pageElements pages useCategory =
  useCategory (PageElements pages)

-- | Look up an occurrence by page index and position on the infinite spine.
--
-- Pages after the finite presentation repeat its final chain, so lookup can
-- fail only when @chainObjectAt pageChain position == Nothing@.  On success
-- the result @x@ satisfies:
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
pageElement (PageElements pages) page position =
  withPageDataAt pages page $ \prefix padding ->
    case chainObjectAt (lastChain prefix) position of
      Nothing -> Nothing
      Just value ->
        Just
          (SomePageElement
            (pageElementAt
              page
              position
              (drop 1 (pageElementTraceAt prefix padding value))))

-- | Build the complete sequence of exact adjacent transports from one cell
-- back through every earlier page to the origin.  The head is the requested
-- occurrence; every following position is computed using the corresponding
-- coconsolidation in the folio.
pageElementTraceAt
  :: Folio origin page
  -> Natural
  -> page
  -> [Ordinal]
pageElementTraceAt pages padding value =
  prependCopies
    padding
    (chainPosition (lastChain pages) value)
    (genuinePageElementTrace pages value)

-- | Build the trace through the stored finite presentation.  Its input is an
-- actual cell, rather than an unchecked ordinal, so every transport is total.
genuinePageElementTrace
  :: Folio origin page
  -> page
  -> [Ordinal]
genuinePageElementTrace (OriginFolio _ pageChain _) value =
  [chainPosition pageChain value]
genuinePageElementTrace
  (SnocPage _ previous pageChain transition)
  value =
    chainPosition pageChain value
      : genuinePageElementTrace previous earlierValue
  where
    earlierValue =
      runConsolidationTransport
        (transportCoconsolidation transition)
        value

prependCopies :: Natural -> a -> [a] -> [a]
prependCopies 0 _ values = values
prependCopies count value values =
  value : prependCopies (count - 1) value values

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
    withPageDataAt pages page $ \prefix _ ->
      let pageChain = lastChain prefix
      in useCell pageChain <$> chainObjectAt pageChain position
