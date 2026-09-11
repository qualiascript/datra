{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden representation of atlas objects.
--
-- This module intentionally contains no LiquidHaskell specifications yet.
-- The laws documented on 'atlas', 'atlasDataAt', and 'mapAtlasData' describe
-- the proof obligations that a later verified representation should enforce.
module Atlas.Internal
  ( Atlas
  , atlas
  , atlasPagination
  , atlasFolio
  , atlasPageElements
  , atlasCardinality
  , normalizeAtlasElement
  , normalizeAtlasArrow
  , atlasCoherence
  , atlasDataAt
  , mapAtlasData
  , atlasDataCoherence
  , normalizeAtlasDatum
  ) where

import Data.Kind (Type)
import DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  )
import Dominion (Dominion)
import Folio (Folio)
import Numeric.Natural (Natural)
import PageElements
  ( PageElement
  , PageElementArrow
  , PageElements
  , pageElementArrow
  )
import Pagination
  ( Pagination
  , PaginationMorphism
  , normalizePaginationArrow
  , normalizePaginationElement
  , paginationCardinality
  , paginationCoherence
  , paginationFolio
  , paginationPageElements
  )

-- | An atlas over one generatively scoped pagination.
--
-- @cellData object@ is the carrier of the dominion attached to the page
-- element identified by @object@.  Keeping this family as an explicit
-- parameter makes the dependent shape of the data assignment visible to
-- Haskell's type checker: the action on an arrow must connect exactly its
-- endpoint cell-data carriers.
--
-- The supplied actions are stored privately and are only called with
-- normalized page elements and arrows.  Consequently, all public observations
-- of a padded occurrence are defined by its last genuine representative.
type role Atlas nominal nominal nominal nominal
data Atlas
  (scope :: Type)
  (cellData :: Type -> Type)
  origin
  final = Atlas
  { storedPagination :: Pagination scope origin final
  , canonicalDataAt
      :: forall object.
         PageElement scope object
      -> Dominion (cellData object)
  , canonicalMapData
      :: forall source target.
         PageElementArrow scope source target
      -> DomanialInsertion (cellData source) (cellData target)
  }

-- | Construct an atlas object from a pagination and its canonical data
-- assignment.
--
-- This prototype deliberately does not check the following laws yet:
--
-- * Identity: the action on @identityPageElementArrow x@ is extensionally
--   'DomanialInsertion.identityInsertion'.
-- * Composition: the action on @g . f@ is extensionally the composite of the
--   actions on @g@ and @f@.
-- * Data coherence: the action from an occurrence to its normalized
--   representative is extensionally the identity insertion.  Public data
--   lookup is already defined to be unchanged on page numbers greater than or
--   equal to 'atlasCardinality'.
-- * Pagewise disjointness: for distinct cells on one genuine page, the images
--   of their cell-data carriers under the induced insertions to the origin's
--   cell-data carrier do not intersect.
--
-- The first two make the data assignment a functor to domanial insertions.
-- The third is the explicit tall-stability law.  The fourth is the Atlas
-- separation condition from the Lean definition.
atlas
  :: Pagination scope origin final
  -> (forall object.
        PageElement scope object -> Dominion (cellData object))
  -> (forall source target.
        PageElementArrow scope source target
        -> DomanialInsertion (cellData source) (cellData target))
  -> Atlas scope cellData origin final
atlas = Atlas

-- | Recover the pagination underlying an atlas.
atlasPagination
  :: Atlas scope cellData origin final
  -> Pagination scope origin final
atlasPagination = storedPagination

-- | Recover the finite folio underlying an atlas.
atlasFolio :: Atlas scope cellData origin final -> Folio origin final
atlasFolio = paginationFolio . atlasPagination

-- | Recover the category of page elements underlying an atlas.
atlasPageElements
  :: Atlas scope cellData origin final
  -> PageElements scope origin final
atlasPageElements = paginationPageElements . atlasPagination

-- | The number of genuine pages in the atlas's finite presentation.
atlasCardinality :: Atlas scope cellData origin final -> Natural
atlasCardinality = paginationCardinality . atlasPagination

-- | Collapse a tall occurrence to its last genuine representative.
--
-- Intended coherence law: normalizing twice equals normalizing once.
normalizeAtlasElement
  :: Atlas scope cellData origin final
  -> PageElement scope object
  -> PageElement scope object
normalizeAtlasElement value =
  normalizePaginationElement (atlasPagination value)

-- | Normalize both endpoints of a tall page-element arrow.
--
-- Intended coherence laws: this operation preserves identities and
-- composition, and normalizing an arrow twice equals normalizing it once.
normalizeAtlasArrow
  :: Atlas scope cellData origin final
  -> PageElementArrow scope source target
  -> PageElementArrow scope source target
normalizeAtlasArrow value =
  normalizePaginationArrow (atlasPagination value)

-- | The idempotent pagination endomorphism selecting the finite
-- representatives used by this atlas.
--
-- Intended coherence law: composing this morphism with itself gives this
-- morphism again.  That law is already verified by the Pagination layer; it
-- is repeated here because it will become the object idempotent in the
-- Karoubi-style presentation of atlas morphisms.
atlasCoherence
  :: Atlas scope cellData origin final
  -> PaginationMorphism scope scope
atlasCoherence = paginationCoherence . atlasPagination

-- | Retrieve the dominion carried by a page element.
--
-- The occurrence is normalized before the supplied action is evaluated.
-- Therefore the intended tall-stability equation
--
-- @
-- atlasDataAt value x
--   = atlasDataAt value (normalizeAtlasElement value x)
-- @
--
-- holds by construction, up to extensional equality of 'Dominion' values.
atlasDataAt
  :: Atlas scope cellData origin final
  -> PageElement scope object
  -> Dominion (cellData object)
atlasDataAt value occurrence =
  canonicalDataAt value (normalizeAtlasElement value occurrence)

-- | Apply the atlas data assignment to a page-element arrow.
--
-- The arrow is normalized before the supplied action is evaluated.  The
-- supplied canonical action ought to preserve identities and composition.
-- Together with normalization preserving those operations, that makes this
-- full tall-spine action functorial and constant on the padded tail.
mapAtlasData
  :: Atlas scope cellData origin final
  -> PageElementArrow scope source target
  -> DomanialInsertion (cellData source) (cellData target)
mapAtlasData value pageArrow =
  canonicalMapData value (normalizeAtlasArrow value pageArrow)

-- | The data-layer action from an occurrence to its normalized
-- representative.
--
-- Intended coherence law: this is extensionally the identity insertion.  It
-- is the data component of the Atlas's normalization idempotent.
atlasDataCoherence
  :: Atlas scope cellData origin final
  -> PageElement scope object
  -> DomanialInsertion (cellData object) (cellData object)
atlasDataCoherence value occurrence =
  mapAtlasData value
    (pageElementArrow
      occurrence
      (normalizeAtlasElement value occurrence))

-- | Normalize a datum by applying the data component of Atlas coherence.
--
-- Intended coherence law: @normalizeAtlasDatum value x = id@ pointwise.  It
-- follows from the identity law for the canonical arrow action because public
-- arrow observation first collapses both endpoints to the same representative.
normalizeAtlasDatum
  :: Atlas scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> cellData object
normalizeAtlasDatum value occurrence =
  applyInsertion (atlasDataCoherence value occurrence)
