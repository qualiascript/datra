{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--higherorder" @-}

-- | Hidden representation of atlas objects.
--
-- The law-bearing data assignment lives in "Atlas.LiquidInternal".
module Atlas.Internal
  ( Atlas
  , AtlasDataAction
  , atlasDataAction
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

import Atlas.LiquidInternal
  ( AtlasAction
  , AtlasData
  , atlasAction
  , atlasActionData
  , atlasActionDataAt
  , atlasActionMap
  , atlasData
  )
import Data.Kind (Type)
import DomanialInsertion.LiquidInternal
import Dominion (Dominion)
import Folio (Folio)
import Numeric.Natural (Natural)
import PageElements (PageElements)
import PageElements.LiquidInternal
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

-- | A law-bearing atlas with its own generative identity, built over one
-- generatively scoped pagination.
--
-- @atlasScope@ identifies this particular Atlas object, independently of the
-- pagination's @scope@.  That distinction lets future Atlas morphisms name
-- their exact source and target even when two atlases share one pagination.
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
type role Atlas nominal nominal nominal nominal nominal
data Atlas
  (atlasScope :: Type)
  (scope :: Type)
  (cellData :: Type -> Type)
  origin
  final = Atlas
  { storedPagination :: Pagination scope origin final
  , storedAtlasData :: AtlasData scope cellData
  }

-- | The object and arrow actions of an Atlas data assignment.
type AtlasDataAction = AtlasAction

-- | Package the dependent cell-data assignment and its arrow action before
-- supplying the laws checked by 'atlas'.
atlasDataAction
  :: (forall object.
        PageElement scope object -> Dominion (cellData object))
  -> (forall source target.
        PageElementArrow scope source target
        -> DomanialInsertion (cellData source) (cellData target))
  -> AtlasDataAction scope cellData
atlasDataAction = atlasAction

-- | Construct an atlas object from a pagination and its canonical data
-- assignment.
--
-- LiquidHaskell checks the following supplied laws pointwise:
--
-- * Identity: the action on @identityPageElementArrow x@ is extensionally
--   'DomanialInsertion.identityInsertion'.
-- * Composition: the action on @g . f@ is extensionally the composite of the
--   actions on @g@ and @f@.
-- * Tall data coherence: the action from an occurrence to its normalized
--   representative is extensionally the identity insertion.  Public data
--   lookup is already defined to be unchanged on page numbers greater than or
--   equal to 'atlasCardinality'.
-- * Pagewise disjointness: for distinct cells on one genuine page, the images
--   of their cell-data carriers under the induced insertions to the origin's
--   cell-data carrier do not intersect.
--
-- The first two make the data assignment a functor to domanial insertions.
-- The third is the explicit tall-stability law.  The fourth is the Atlas
-- separation condition from the Lean definition.  The continuation introduces
-- a fresh @atlasScope@, so that identity cannot escape or be confused with the
-- identity of another Atlas.  Unit arguments on three of the witnesses carry
-- refinement preconditions and have no runtime content.
{-@
atlas
  :: paginationValue:Pagination scope origin final
  -> action:AtlasDataAction scope cellData
  -> identityLaw:(forall object.
       occurrence:PageElement scope object
       -> datum:cellData object
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  (atlasFinalPageLogic paginationValue)
                  (atlasTraceLimitLogic paginationValue)
                  (identityPageElementArrow occurrence)))
              datum
            == datum })
  -> compositionLaw:(forall source middle target.
       second:PageElementArrow scope middle target
       -> first:PageElementArrow scope source middle
       -> alignment:{() | arrowTarget first == arrowSource second}
       -> datum:cellData source
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  (atlasFinalPageLogic paginationValue)
                  (atlasTraceLimitLogic paginationValue)
                  (composePageElementArrows second first)))
              datum
            == applyInsertion
                 (atlasActionMap action
                   (normalizePageElementArrowAt
                     (atlasFinalPageLogic paginationValue)
                     (atlasTraceLimitLogic paginationValue) second))
                 (applyInsertion
                   (atlasActionMap action
                     (normalizePageElementArrowAt
                       (atlasFinalPageLogic paginationValue)
                       (atlasTraceLimitLogic paginationValue) first))
                   datum) })
  -> coherenceLaw:(forall object.
       occurrence:PageElement scope object
       -> coherenceArrow:PageElementArrow scope object object
       -> conditions:{() |
            arrowSource coherenceArrow == occurrence
            && arrowTarget coherenceArrow == normalizePageElementAt
                 (atlasFinalPageLogic paginationValue)
                 (atlasTraceLimitLogic paginationValue) occurrence}
       -> datum:cellData object
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  (atlasFinalPageLogic paginationValue)
                  (atlasTraceLimitLogic paginationValue) coherenceArrow))
              datum
            == datum })
  -> disjointLaw:(forall leftObject rightObject originObject.
       left:PageElement scope leftObject
       -> right:PageElement scope rightObject
       -> leftToOrigin:PageElementArrow scope leftObject originObject
       -> rightToOrigin:PageElementArrow scope rightObject originObject
       -> conditions:{() |
            pageElementPage right == pageElementPage left
            && pageElementPosition right /= pageElementPosition left
            && pageElementPage left <= atlasFinalPageLogic paginationValue
            && arrowSource leftToOrigin == left
            && pageElementPage (arrowTarget leftToOrigin) == 0
            && arrowSource rightToOrigin == right
            && arrowTarget rightToOrigin == arrowTarget leftToOrigin}
       -> leftDatum:cellData leftObject
       -> rightDatum:cellData rightObject
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  (atlasFinalPageLogic paginationValue)
                  (atlasTraceLimitLogic paginationValue) leftToOrigin))
              leftDatum
            /= applyInsertion
                 (atlasActionMap action
                   (normalizePageElementArrowAt
                     (atlasFinalPageLogic paginationValue)
                     (atlasTraceLimitLogic paginationValue) rightToOrigin))
                 rightDatum })
  -> useAtlas:(forall atlasScope.
       Atlas atlasScope scope cellData origin final -> result)
  -> result
@-}
atlas
  :: Pagination scope origin final
  -> AtlasDataAction scope cellData
  -> (forall object.
        PageElement scope object -> cellData object -> ())
  -> (forall source middle target.
        PageElementArrow scope middle target
        -> PageElementArrow scope source middle
        -> ()
        -> cellData source
        -> ())
  -> (forall object.
        PageElement scope object
        -> PageElementArrow scope object object
        -> ()
        -> cellData object
        -> ())
  -> (forall leftObject rightObject originObject.
        PageElement scope leftObject
        -> PageElement scope rightObject
        -> PageElementArrow scope leftObject originObject
        -> PageElementArrow scope rightObject originObject
        -> ()
        -> cellData leftObject
        -> cellData rightObject
        -> ())
  -> (forall atlasScope.
        Atlas atlasScope scope cellData origin final -> result)
  -> result
atlas paginationValue action identityLaw compositionLaw coherenceLaw disjointLaw
    useAtlas =
  useAtlas
    (Atlas
      paginationValue
      (atlasData
        (atlasFinalPage paginationValue)
        (atlasTraceLimit paginationValue)
        action
        identityLaw
        compositionLaw
        coherenceLaw
        disjointLaw))

-- | Final genuine page used by Atlas normalization.
{-@ measure atlasFinalPageLogic :: Pagination scope origin final -> Natural @-}
{-@
assume atlasFinalPage
  :: value:Pagination scope origin final
  -> { finalPage:Natural | finalPage == atlasFinalPageLogic value }
@-}
atlasFinalPage :: Pagination scope origin final -> Natural
atlasFinalPage paginationValue = paginationCardinality paginationValue - 1

-- | Maximum transport-trace length used by Atlas normalization.
{-@ measure atlasTraceLimitLogic :: Pagination scope origin final -> Int @-}
{-@
assume atlasTraceLimit
  :: value:Pagination scope origin final
  -> { traceLimit:Int | traceLimit == atlasTraceLimitLogic value }
@-}
atlasTraceLimit :: Pagination scope origin final -> Int
atlasTraceLimit paginationValue =
  fromIntegral (paginationCardinality paginationValue)

-- | Recover the pagination underlying an atlas.
atlasPagination
  :: Atlas atlasScope scope cellData origin final
  -> Pagination scope origin final
atlasPagination = storedPagination

-- | Recover the finite folio underlying an atlas.
atlasFolio
  :: Atlas atlasScope scope cellData origin final
  -> Folio origin final
atlasFolio = paginationFolio . atlasPagination

-- | Recover the category of page elements underlying an atlas.
atlasPageElements
  :: Atlas atlasScope scope cellData origin final
  -> PageElements scope origin final
atlasPageElements = paginationPageElements . atlasPagination

-- | The number of genuine pages in the atlas's finite presentation.
atlasCardinality
  :: Atlas atlasScope scope cellData origin final
  -> Natural
atlasCardinality = paginationCardinality . atlasPagination

-- | Collapse a tall occurrence to its last genuine representative.
normalizeAtlasElement
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> PageElement scope object
{-@ reflect normalizeAtlasElement @-}
normalizeAtlasElement value =
  normalizePaginationElement (atlasPagination value)

-- | Normalize both endpoints of a tall page-element arrow.
normalizeAtlasArrow
  :: Atlas atlasScope scope cellData origin final
  -> PageElementArrow scope source target
  -> PageElementArrow scope source target
normalizeAtlasArrow value =
  normalizePaginationArrow (atlasPagination value)

-- | The idempotent pagination endomorphism selecting the finite
-- representatives used by this atlas.
--
-- This will become the object idempotent in the Karoubi-style presentation of
-- atlas morphisms.
atlasCoherence
  :: Atlas atlasScope scope cellData origin final
  -> PaginationMorphism scope scope
atlasCoherence = paginationCoherence . atlasPagination

-- | Retrieve the dominion carried by a page element.
--
-- The occurrence is normalized before the supplied action is evaluated, so
-- the tall-stability equation
--
-- @
-- atlasDataAt value x
--   = atlasDataAt value (normalizeAtlasElement value x)
-- @
--
-- holds by construction, up to extensional equality of 'Dominion' values.
atlasDataAt
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> Dominion (cellData object)
atlasDataAt value occurrence =
  atlasActionDataAt
    (atlasActionData (storedAtlasData value))
    (normalizeAtlasElement value occurrence)

-- | Apply the atlas data assignment to a page-element arrow.
--
-- The arrow is normalized before the supplied action is evaluated.  The
-- checked canonical action preserves identities and composition.  Together
-- with normalization preserving those operations, that makes this full
-- tall-spine action functorial and constant on the padded tail.
mapAtlasData
  :: Atlas atlasScope scope cellData origin final
  -> PageElementArrow scope source target
  -> DomanialInsertion (cellData source) (cellData target)
{-@ reflect mapAtlasData @-}
mapAtlasData value pageArrow =
  atlasActionMap
    (atlasActionData (storedAtlasData value))
    (normalizeAtlasArrow value pageArrow)

-- | The data-layer action from an occurrence to its normalized
-- representative.
--
-- The checked tall-coherence law makes this extensionally the identity
-- insertion.  It is the data component of the Atlas's normalization
-- idempotent.
atlasDataCoherence
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> DomanialInsertion (cellData object) (cellData object)
atlasDataCoherence value occurrence =
  case normalizePageElementReachableAt
    (atlasFinalPage (atlasPagination value))
    (atlasTraceLimit (atlasPagination value))
    occurrence of
      () -> mapAtlasData value
        (pageElementArrow
          occurrence
          (normalizePageElementAt
            (atlasFinalPage (atlasPagination value))
            (atlasTraceLimit (atlasPagination value))
            occurrence))

-- | Normalize a datum by applying the data component of Atlas coherence.
--
-- The checked tall-coherence law makes this operation pointwise equal to the
-- identity.
normalizeAtlasDatum
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> cellData object
normalizeAtlasDatum value occurrence =
  applyInsertion (atlasDataCoherence value occurrence)
