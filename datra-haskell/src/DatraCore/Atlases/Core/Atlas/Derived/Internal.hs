{-# LANGUAGE RankNTypes #-}

-- | Derived Atlas observations corresponding to the remainder of the Lean
-- Atlas section.
module Atlas.Derived.Internal
  ( withAtlasPageChain
  , atlasPageCell
  , atlasOriginCell
  , atlasElementLT
  , atlasCoherenceIdempotent
  ) where

import Atlas.Internal
  ( Atlas
  , atlasFolio
  , atlasPageElements
  , atlasPagination
  , normalizeAtlasElement
  )
import Chain
  ( Chain
  )
import DatraOrdinal
  ( Ordinal
  , ordinalLT
  )
import Folio
  ( withPageAt
  )
import Numeric.Natural (Natural)
import PageElements
  ( PageElement
  , PageElementIndex
  , SomePageElement
  )
import PageElements.LiquidInternal
  ( PageElement (..)
  )
import qualified PageElements.Internal as Elements
import Pagination (paginationCoherenceIdempotent)

-- | Eliminate the carrier of the @n@th page chain. Pages at or above the Atlas
-- cardinality are the padded copies of the final genuine chain.
withAtlasPageChain
  :: Atlas atlasScope scope cellData origin final
  -> Natural
  -> (forall page. Chain page -> result)
  -> result
withAtlasPageChain valueAtlas = withPageAt (atlasFolio valueAtlas)

-- | Construct a page cell from an index already certified against this
-- pagination's page-element spine. Refining an unchecked page and ordinal is
-- deliberately kept in 'PageElements.pageElementIndex'; once that witness
-- exists, the Atlas observation is total.
atlasPageCell
  :: Atlas atlasScope scope cellData origin final
  -> PageElementIndex scope
  -> SomePageElement scope
atlasPageCell _ = Elements.pageElement

-- | The unique origin cell of an Atlas.
atlasOriginCell
  :: Atlas atlasScope scope cellData origin final
  -> SomePageElement scope
atlasOriginCell = Elements.originPageElement . atlasPageElements

-- | Compare two cells after transporting them to their common earliest page.
-- Inputs on the padded tail are normalized first, matching Lean's use of
-- @collapseElements@ before @storedElementLT@.
atlasElementLT
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope leftObject
  -> PageElement scope rightObject
  -> Bool
atlasElementLT valueAtlas left right =
  let normalizedLeft = normalizeAtlasElement valueAtlas left
      normalizedRight = normalizeAtlasElement valueAtlas right
      commonPage = min
        (pageElementPage normalizedLeft)
        (pageElementPage normalizedRight)
  in case
      ( positionAtPage commonPage normalizedLeft
      , positionAtPage commonPage normalizedRight
      ) of
        (Just leftPosition, Just rightPosition) ->
          ordinalLT leftPosition rightPosition
        _ -> False

positionAtPage
  :: Natural
  -> PageElement scope object
  -> Maybe Ordinal
positionAtPage page occurrence =
  case drop offset (pageElementTrace occurrence) of
    position : _ -> Just position
    [] -> Nothing
  where
    offset = fromIntegral (pageElementPage occurrence - page)

-- | Pointwise idempotence of the Atlas coherence map.
atlasCoherenceIdempotent
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> ()
atlasCoherenceIdempotent valueAtlas =
  paginationCoherenceIdempotent (atlasPagination valueAtlas)
