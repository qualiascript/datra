{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Derived Atlas observations corresponding to the remainder of the Lean
-- Atlas section.
module Atlas.Derived.Internal
  ( AtlasCellDominion
  , AtlasCellDominionHandler
  , AtlasTerritoryIndex
  , withAtlasCellDominion
  , withAtlasPageChain
  , atlasPageCell
  , atlasOriginCell
  , atlasExtent
  , atlasTerritoryChain
  , atlasTerritory
  , atlasRegion
  , atlasElementLT
  , atlasCoherenceIdempotent
  ) where

import Atlas.Internal
  ( Atlas
  , atlasDataAt
  , atlasFolio
  , atlasPageElements
  , atlasPagination
  , normalizeAtlasElement
  )
import Chain
  ( Chain
  , ChainIndex
  )
import Data.Kind (Type)
import DatraOrdinal
  ( Ordinal
  , ordinalLT
  )
import Dominion (Dominion)
import Folio
  ( lastChain
  , withPageAt
  )
import Numeric.Natural (Natural)
import PageElements
  ( PageElement
  , PageElementIndex
  , SomePageElement
  )
import PageElements.LiquidInternal
  ( PageElement (..)
  , SomePageElement (..)
  )
import qualified PageElements.Internal as Elements
import Pagination (paginationCoherenceIdempotent)

-- | A dependent Atlas dominion whose page-element identity is hidden. This
-- is the Haskell presentation of Lean values such as @extent A@ and
-- @territory A k@, whose carrier types depend on the selected cell.
type role AtlasCellDominion nominal nominal
data AtlasCellDominion
  (scope :: Type)
  (cellData :: Type -> Type) where
  AtlasCellDominion
    :: PageElement scope object
    -> Dominion (cellData object)
    -> AtlasCellDominion scope cellData

-- | A named continuation for consuming a dependent Atlas dominion.
type AtlasCellDominionHandler scope cellData result =
  forall object.
    PageElement scope object
    -> Dominion (cellData object)
    -> result

-- | Eliminate the hidden page-element identity of an extent or region.
withAtlasCellDominion
  :: AtlasCellDominion scope cellData
  -> AtlasCellDominionHandler scope cellData result
  -> result
withAtlasCellDominion
  (AtlasCellDominion occurrence valueDominion)
  useDominion = useDominion occurrence valueDominion

-- | A certified index into an Atlas's final genuine page. Lean uses the page
-- cell itself as the index; Haskell retains its chain certificate as well.
type AtlasTerritoryIndex final = ChainIndex final

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

-- | The Atlas extent: the dominion attached to its origin cell.
atlasExtent
  :: Atlas atlasScope scope cellData origin final
  -> AtlasCellDominion scope cellData
atlasExtent valueAtlas =
  case atlasOriginCell valueAtlas of
    SomePageElement origin ->
      AtlasCellDominion origin (atlasDataAt valueAtlas origin)

-- | The final genuine page whose certified indices select territory members.
-- Pair this chain with 'Chain.chainIndex' when starting from an unchecked
-- ordinal; 'atlasTerritory' itself only accepts the resulting witness.
atlasTerritoryChain
  :: Atlas atlasScope scope cellData origin final
  -> Chain final
atlasTerritoryChain = lastChain . atlasFolio

-- | The territory member selected by a certified final-page index.
atlasTerritory
  :: Atlas atlasScope scope cellData origin final
  -> AtlasTerritoryIndex final
  -> AtlasCellDominion scope cellData
atlasTerritory valueAtlas index =
  case Elements.lastPageElement (atlasPageElements valueAtlas) index of
    SomePageElement occurrence ->
      AtlasCellDominion occurrence (atlasDataAt valueAtlas occurrence)

-- | The @n@th region of an Atlas. As in Lean, this is definitionally the
-- corresponding territory member.
atlasRegion
  :: Atlas atlasScope scope cellData origin final
  -> AtlasTerritoryIndex final
  -> AtlasCellDominion scope cellData
atlasRegion = atlasTerritory

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
