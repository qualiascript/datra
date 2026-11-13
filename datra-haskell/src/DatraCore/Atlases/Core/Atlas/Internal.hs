{-# LANGUAGE CPP #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
#include "../../../LiquidPlugin.h"
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
  , AtlasMembership
  , atlasMembership
  , atlasMembershipAccepts
  , atlasRestrictedDataAction
  , atlas
  , atlasWithScope
  , atlasPagination
  , atlasFolio
  , atlasPageElements
  , atlasCardinality
  , normalizeAtlasElement
  , normalizeAtlasArrow
  , normalizeAtlasElementTraceValid
  , normalizeAtlasArrowTraceValid
  , atlasCoherence
  , atlasDataAt
  , atlasAcceptsDatum
  , atlasAcceptsDatumNormalized
  , mapAtlasData
  , atlasDataCoherence
  , atlasDataCoherenceAgrees
  , normalizeAtlasDatum
  , atlasIdentityWitness
  , atlasCompositionWitness
  , atlasCoherenceWitness
  , atlasDisjointWitness
  , withAtlasPageChain
  , atlasPageCell
  , atlasOriginCell
  , atlasElementLT
  , atlasCoherenceIdempotent
  ) where

import Atlas.LiquidInternal
  ( AtlasAction
  , AtlasMembership
  , atlasMembership
  , atlasMembershipAccepts
  , AtlasData
  , atlasAction
  , atlasActionData
  , atlasDataFinalPage
  , atlasDataTraceLimit
  , atlasActionDataAt
  , atlasActionAccepts
  , atlasActionMap
  , atlasData
  , atlasDataIdentityLaw
  , atlasDataCompositionLaw
  , atlasDataCoherenceLaw
  , atlasDataDisjointLaw
  )
import qualified Atlas.LiquidInternal as Action
import Chain (Chain)
import Data.Kind (Type)
import DatraOrdinal (Ordinal, ordinalLT)
import DomanialInsertion.Core
  ( DomanialInsertion (..)
  , identityInsertion
  , identityInsertionApply
  )
import Dominion (Dominion)
import Folio (Folio, withPageAt)
import Numeric.Natural (Natural)
import PageElements (PageElementIndex, PageElements)
import qualified PageElements.Internal as Elements
import PageElements.Structure
  ( PageElementCell (..)
  , PageElement (..)
  , SomePageElement (..)
  , PageElementArrow (..)
  , SomePageElementArrow (..)
  , somePageElementPage
  , somePageElementPosition
  , somePageElementTrace
  , somePageElementPrecedes
  , somePageElementTransported
  , identityPageElementArrow
  , composePageElementArrows
  , normalizePageElementAt
  , normalizePageElementArrowAt
  , normalizePageElementIdempotentAt
  , traceStartsWith
  , positionAtPage
  )
import Pagination.Internal
  ( Pagination
  , PaginationMorphism
  , paginationCardinality
  , paginationCoherence
  , paginationCoherenceIdempotent
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
{-@ data Atlas atlasScope scope cellData origin final = Atlas
      { storedPagination :: Pagination scope origin final
      , storedAtlasData :: {stored:AtlasData scope cellData |
           atlasDataFinalPage stored == atlasFinalPage storedPagination
           && atlasDataTraceLimit stored == atlasTraceLimit storedPagination
           && Action.atlasActionDomain (atlasActionData stored)
                == Elements.pageElementDomain (paginationPageElements storedPagination)}
      } @-}
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
{-@ atlasDataAction :: category:PageElements scope origin final
      -> dataAt:(forall object. occurrence:{PageElement scope object | Elements.pageElementTraceValid category occurrence}
           -> Dominion (cellData object))
      -> mapData:(forall source target. arrow:{PageElementArrow scope source target |
           Elements.pageElementTraceValid category (arrowSource arrow)
           && Elements.pageElementTraceValid category (arrowTarget arrow)}
           -> DomanialInsertion (cellData source) (cellData target))
      -> {action:AtlasDataAction scope cellData |
           Action.atlasActionDomain action == Elements.pageElementDomain category} @-}
atlasDataAction
  :: PageElements scope origin final
  -> (forall object.
        PageElement scope object -> Dominion (cellData object))
  -> (forall source target.
        PageElementArrow scope source target
        -> DomanialInsertion (cellData source) (cellData target))
  -> AtlasDataAction scope cellData
atlasDataAction category = atlasAction (Elements.pageElementDomain category)

-- | Retain a value-dependent cell carrier through Atlas construction.
{-@ atlasRestrictedDataAction
      :: category:PageElements scope origin final
      -> membership:AtlasMembership scope cellData
      -> dataAt:(forall object. occurrence:{PageElement scope object | Elements.pageElementTraceValid category occurrence}
           -> Dominion ({datum:cellData object | atlasMembershipAccepts membership occurrence datum}))
      -> mapData:(forall source target. arrow:{PageElementArrow scope source target |
           Elements.pageElementTraceValid category (arrowSource arrow)
           && Elements.pageElementTraceValid category (arrowTarget arrow)}
           -> DomanialInsertion
                ({datum:cellData source | atlasMembershipAccepts membership (arrowSource arrow) datum})
                ({datum:cellData target | atlasMembershipAccepts membership (arrowTarget arrow) datum}))
      -> {action:AtlasDataAction scope cellData | Action.atlasActionMembership action == membership
           && Action.atlasActionDomain action == Elements.pageElementDomain category} @-}
atlasRestrictedDataAction
  :: PageElements scope origin final
  -> AtlasMembership scope cellData
  -> (forall object. PageElement scope object -> Dominion (cellData object))
  -> (forall source target. PageElementArrow scope source target
        -> DomanialInsertion (cellData source) (cellData target))
  -> AtlasDataAction scope cellData
atlasRestrictedDataAction category = Action.atlasRestrictedAction (Elements.pageElementDomain category)

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
  -> action:{AtlasDataAction scope cellData |
       Action.atlasActionDomain action == Elements.pageElementDomain (paginationPageElements paginationValue)}
  -> identityLaw:(forall object.
       occurrence:{PageElement scope object | Action.atlasActionElementValid action occurrence}
       -> datum:{cellData object | atlasActionAccepts action
            (normalizePageElementAt (atlasFinalPage paginationValue)
              (atlasTraceLimit paginationValue) occurrence) datum}
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  (atlasFinalPage paginationValue)
                  (atlasTraceLimit paginationValue)
                  (identityPageElementArrow occurrence)))
              datum
            == datum })
  -> compositionLaw:(forall source middle target.
       second:{PageElementArrow scope middle target | Action.atlasActionArrowValid action second}
       -> first:{PageElementArrow scope source middle | Action.atlasActionArrowValid action first}
       -> alignment:{() | arrowTarget first == arrowSource second}
       -> datum:{cellData source | atlasActionAccepts action
            (normalizePageElementAt (atlasFinalPage paginationValue)
              (atlasTraceLimit paginationValue) (arrowSource first)) datum}
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  (atlasFinalPage paginationValue)
                  (atlasTraceLimit paginationValue)
                  (composePageElementArrows second first)))
              datum
            == applyInsertion
                 (atlasActionMap action
                   (normalizePageElementArrowAt
                     (atlasFinalPage paginationValue)
                     (atlasTraceLimit paginationValue) second))
                 (applyInsertion
                   (atlasActionMap action
                     (normalizePageElementArrowAt
                       (atlasFinalPage paginationValue)
                       (atlasTraceLimit paginationValue) first))
                   datum) })
  -> coherenceLaw:(forall object.
       occurrence:{PageElement scope object | Action.atlasActionElementValid action occurrence}
       -> coherenceArrow:{PageElementArrow scope object object | Action.atlasActionArrowValid action coherenceArrow}
       -> conditions:{() |
            arrowSource coherenceArrow == occurrence
            && arrowTarget coherenceArrow == normalizePageElementAt
                 (atlasFinalPage paginationValue)
                 (atlasTraceLimit paginationValue) occurrence}
       -> datum:{cellData object | atlasActionAccepts action
            (normalizePageElementAt (atlasFinalPage paginationValue)
              (atlasTraceLimit paginationValue) occurrence) datum}
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  (atlasFinalPage paginationValue)
                  (atlasTraceLimit paginationValue) coherenceArrow))
              datum
            == datum })
  -> disjointLaw:(forall leftObject rightObject originObject.
       left:{PageElement scope leftObject | Action.atlasActionElementValid action left}
       -> right:{PageElement scope rightObject | Action.atlasActionElementValid action right}
       -> leftToOrigin:{PageElementArrow scope leftObject originObject | Action.atlasActionArrowValid action leftToOrigin}
       -> rightToOrigin:{PageElementArrow scope rightObject originObject | Action.atlasActionArrowValid action rightToOrigin}
       -> conditions:{() |
            pageElementPage right == pageElementPage left
            && pageElementPosition right /= pageElementPosition left
            && pageElementPage left <= atlasFinalPage paginationValue
            && arrowSource leftToOrigin == left
            && pageElementPage (arrowTarget leftToOrigin) == 0
            && arrowSource rightToOrigin == right
            && arrowTarget rightToOrigin == arrowTarget leftToOrigin}
       -> leftDatum:{cellData leftObject | atlasActionAccepts action
            (normalizePageElementAt (atlasFinalPage paginationValue)
              (atlasTraceLimit paginationValue) left) leftDatum}
       -> rightDatum:{cellData rightObject | atlasActionAccepts action
            (normalizePageElementAt (atlasFinalPage paginationValue)
              (atlasTraceLimit paginationValue) right) rightDatum}
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  (atlasFinalPage paginationValue)
                  (atlasTraceLimit paginationValue) leftToOrigin))
              leftDatum
            /= applyInsertion
                 (atlasActionMap action
                   (normalizePageElementArrowAt
                     (atlasFinalPage paginationValue)
                     (atlasTraceLimit paginationValue) rightToOrigin))
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
    (atlasWithScope
      paginationValue
      action
      identityLaw
      compositionLaw
      coherenceLaw
      disjointLaw)

-- | Internal, deterministically named variant of 'atlas'. Derived functors
-- use an input object's type-level name as the output scope, so repeated
-- object and arrow actions agree on exactly the same category object.
-- Public callers continue to use the generative continuation in 'atlas'.
-- ALIGN: ATLAS-MEMBERSHIP-ATLAS-INTERPRETATION.
-- ALIGN: ATLAS-MEMBERSHIP-FUNCTOR-ISOMORPHISM.
{-@
atlasWithScope
  :: paginationValue:Pagination scope origin final
  -> action:{AtlasDataAction scope cellData |
       Action.atlasActionDomain action == Elements.pageElementDomain (paginationPageElements paginationValue)}
  -> identityLaw:(forall object.
       occurrence:{PageElement scope object | Action.atlasActionElementValid action occurrence}
       -> datum:{cellData object | atlasActionAccepts action
            (normalizePageElementAt (atlasFinalPage paginationValue)
              (atlasTraceLimit paginationValue) occurrence) datum}
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  (atlasFinalPage paginationValue)
                  (atlasTraceLimit paginationValue)
                  (identityPageElementArrow occurrence)))
              datum
            == datum })
  -> compositionLaw:(forall source middle target.
       second:{PageElementArrow scope middle target | Action.atlasActionArrowValid action second}
       -> first:{PageElementArrow scope source middle | Action.atlasActionArrowValid action first}
       -> alignment:{() | arrowTarget first == arrowSource second}
       -> datum:{cellData source | atlasActionAccepts action
            (normalizePageElementAt (atlasFinalPage paginationValue)
              (atlasTraceLimit paginationValue) (arrowSource first)) datum}
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  (atlasFinalPage paginationValue)
                  (atlasTraceLimit paginationValue)
                  (composePageElementArrows second first)))
              datum
            == applyInsertion
                 (atlasActionMap action
                   (normalizePageElementArrowAt
                     (atlasFinalPage paginationValue)
                     (atlasTraceLimit paginationValue) second))
                 (applyInsertion
                   (atlasActionMap action
                     (normalizePageElementArrowAt
                       (atlasFinalPage paginationValue)
                       (atlasTraceLimit paginationValue) first))
                   datum) })
  -> coherenceLaw:(forall object.
       occurrence:{PageElement scope object | Action.atlasActionElementValid action occurrence}
       -> coherenceArrow:{PageElementArrow scope object object | Action.atlasActionArrowValid action coherenceArrow}
       -> conditions:{() |
            arrowSource coherenceArrow == occurrence
            && arrowTarget coherenceArrow == normalizePageElementAt
                 (atlasFinalPage paginationValue)
                 (atlasTraceLimit paginationValue) occurrence}
       -> datum:{cellData object | atlasActionAccepts action
            (normalizePageElementAt (atlasFinalPage paginationValue)
              (atlasTraceLimit paginationValue) occurrence) datum}
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  (atlasFinalPage paginationValue)
                  (atlasTraceLimit paginationValue) coherenceArrow))
              datum
            == datum })
  -> disjointLaw:(forall leftObject rightObject originObject.
       left:{PageElement scope leftObject | Action.atlasActionElementValid action left}
       -> right:{PageElement scope rightObject | Action.atlasActionElementValid action right}
       -> leftToOrigin:{PageElementArrow scope leftObject originObject | Action.atlasActionArrowValid action leftToOrigin}
       -> rightToOrigin:{PageElementArrow scope rightObject originObject | Action.atlasActionArrowValid action rightToOrigin}
       -> conditions:{() |
            pageElementPage right == pageElementPage left
            && pageElementPosition right /= pageElementPosition left
            && pageElementPage left <= atlasFinalPage paginationValue
            && arrowSource leftToOrigin == left
            && pageElementPage (arrowTarget leftToOrigin) == 0
            && arrowSource rightToOrigin == right
            && arrowTarget rightToOrigin == arrowTarget leftToOrigin}
       -> leftDatum:{cellData leftObject | atlasActionAccepts action
            (normalizePageElementAt (atlasFinalPage paginationValue)
              (atlasTraceLimit paginationValue) left) leftDatum}
       -> rightDatum:{cellData rightObject | atlasActionAccepts action
            (normalizePageElementAt (atlasFinalPage paginationValue)
              (atlasTraceLimit paginationValue) right) rightDatum}
       -> { proof:() |
            applyInsertion
              (atlasActionMap action
                (normalizePageElementArrowAt
                  (atlasFinalPage paginationValue)
                  (atlasTraceLimit paginationValue) leftToOrigin))
              leftDatum
            /= applyInsertion
                 (atlasActionMap action
                   (normalizePageElementArrowAt
                     (atlasFinalPage paginationValue)
                     (atlasTraceLimit paginationValue) rightToOrigin))
                 rightDatum })
  -> Atlas atlasScope scope cellData origin final
@-}
atlasWithScope
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
  -> Atlas atlasScope scope cellData origin final
atlasWithScope
  paginationValue
  action
  identityLaw
  compositionLaw
  coherenceLaw
  disjointLaw =
    Atlas
      paginationValue
      (atlasData
        (atlasFinalPage paginationValue)
        (atlasTraceLimit paginationValue)
        action
        identityLaw
        compositionLaw
        coherenceLaw
        disjointLaw)

-- | Final genuine page used by Atlas normalization.
{-@ reflect atlasFinalPage @-}
atlasFinalPage :: Pagination scope origin final -> Natural
atlasFinalPage paginationValue = paginationCardinality paginationValue - 1

-- | Maximum transport-trace length used by Atlas normalization.
{-@ reflect atlasTraceLimit @-}
atlasTraceLimit :: Pagination scope origin final -> Int
atlasTraceLimit paginationValue =
  fromIntegral (paginationCardinality paginationValue)

-- | Recover the pagination underlying an atlas.
{-@ reflect atlasPagination @-}
atlasPagination
  :: Atlas atlasScope scope cellData origin final
  -> Pagination scope origin final
atlasPagination = storedPagination

-- | Recover the finite folio underlying an atlas.
{-@ reflect atlasFolio @-}
atlasFolio
  :: Atlas atlasScope scope cellData origin final
  -> Folio origin final
atlasFolio value = Elements.pageElementsFolio (atlasPageElements value)

-- | Recover the category of page elements underlying an atlas.
{-@ reflect atlasPageElements @-}
atlasPageElements
  :: Atlas atlasScope scope cellData origin final
  -> PageElements scope origin final
atlasPageElements valueAtlas = paginationPageElements (storedPagination valueAtlas)

-- | The number of genuine pages in the atlas's finite presentation.
{-@ reflect atlasCardinality @-}
atlasCardinality
  :: Atlas atlasScope scope cellData origin final
  -> Natural
atlasCardinality value = paginationCardinality (atlasPagination value)

-- | Collapse a tall occurrence to its last genuine representative.
normalizeAtlasElement
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> PageElement scope object
{-@ reflect normalizeAtlasElement @-}
normalizeAtlasElement value =
  normalizePageElementAt
    (atlasDataFinalPage (storedAtlasData value))
    (atlasDataTraceLimit (storedAtlasData value))

-- | Normalize both endpoints of a tall page-element arrow.
{-@ reflect normalizeAtlasArrow @-}
normalizeAtlasArrow
  :: Atlas atlasScope scope cellData origin final
  -> PageElementArrow scope source target
  -> PageElementArrow scope source target
normalizeAtlasArrow value =
  normalizePageElementArrowAt
    (atlasDataFinalPage (storedAtlasData value))
    (atlasDataTraceLimit (storedAtlasData value))

-- | Retain the owning folio's certificate when entering the stored data
-- action, whose inputs are normalized using this Atlas's pagination bounds.
-- ALIGN: ATLAS-TRACE-VALID-NORMALIZATION.
{-@ normalizeAtlasElementTraceValid :: owner:Atlas atlasScope scope cellData origin final
      -> occurrence:{PageElement scope object |
           Elements.pageElementTraceValid (atlasPageElements owner) occurrence}
      -> {Elements.pageElementTraceValid (atlasPageElements owner) (normalizeAtlasElement owner occurrence)} @-}
normalizeAtlasElementTraceValid
  :: Atlas atlasScope scope cellData origin final -> PageElement scope object -> ()
normalizeAtlasElementTraceValid owner occurrence =
  storedAtlasData owner `seq` paginationCardinality (storedPagination owner) `seq`
    Elements.pageElementTraceValidNormalize (atlasPageElements owner) occurrence

-- ALIGN: ATLAS-ARROW-TRACE-VALID-NORMALIZATION.
{-@ normalizeAtlasArrowTraceValid :: owner:Atlas atlasScope scope cellData origin final
      -> arrow:{PageElementArrow scope source target |
           Elements.pageElementTraceValid (atlasPageElements owner) (arrowSource arrow)
           && Elements.pageElementTraceValid (atlasPageElements owner) (arrowTarget arrow)}
      -> {Elements.pageElementTraceValid (atlasPageElements owner) (arrowSource (normalizeAtlasArrow owner arrow))
           && Elements.pageElementTraceValid (atlasPageElements owner) (arrowTarget (normalizeAtlasArrow owner arrow))} @-}
normalizeAtlasArrowTraceValid
  :: Atlas atlasScope scope cellData origin final -> PageElementArrow scope source target -> ()
normalizeAtlasArrowTraceValid owner arrow =
  normalizeAtlasElementTraceValid owner (arrowSource arrow) `seq`
    normalizeAtlasElementTraceValid owner (arrowTarget arrow)

-- | The idempotent pagination endomorphism selecting the finite
-- representatives used by this atlas.
--
-- This will become the object idempotent in the Karoubi-style presentation of
-- atlas morphisms.
atlasCoherence
  :: Atlas atlasScope scope cellData origin final
  -> PaginationMorphism scope scope
atlasCoherence = paginationCoherence . atlasPagination

{-@ predicate AtlasValidCell A X = Elements.pageElementTraceValid (atlasPageElements A) X @-}
{-@ predicate AtlasValidArrow A H = AtlasValidCell A (arrowSource H) && AtlasValidCell A (arrowTarget H) @-}

-- | Membership in the normalized cell carrier.
{-@ reflect atlasAcceptsDatum @-}
-- ALIGN: ATLAS-DATUM-MEMBERSHIP.
atlasAcceptsDatum
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object -> cellData object -> Bool
atlasAcceptsDatum value occurrence datum =
  atlasActionAccepts (atlasActionData (storedAtlasData value))
    (normalizeAtlasElement value occurrence) datum

-- ALIGN: ATLAS-DATUM-MEMBERSHIP-NORMALIZATION.
{-@ atlasAcceptsDatumNormalized :: value:Atlas atlasScope scope cellData origin final
      -> occurrence:PageElement scope object -> datum:cellData object
      -> {atlasAcceptsDatum value (normalizeAtlasElement value occurrence) datum
           == atlasAcceptsDatum value occurrence datum} @-}
atlasAcceptsDatumNormalized
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object -> cellData object -> ()
atlasAcceptsDatumNormalized value occurrence _ =
  normalizePageElementIdempotentAt (atlasDataFinalPage (storedAtlasData value))
    (atlasDataTraceLimit (storedAtlasData value)) occurrence

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
{-@ atlasDataAt :: value:Atlas atlasScope scope cellData origin final
      -> occurrence:{PageElement scope object | AtlasValidCell value occurrence}
      -> Dominion ({datum:cellData object | atlasAcceptsDatum value occurrence datum}) @-}
-- ALIGN: ATLAS-MEMBERSHIP-RANK-INTERPRETATION.
-- ALIGN: ATLAS-MEMBERSHIP-UNRANK-INTERPRETATION.
atlasDataAt
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> Dominion (cellData object)
atlasDataAt value occurrence =
  normalizeAtlasElementTraceValid value occurrence `seq` atlasActionDataAt
    (atlasActionData (storedAtlasData value))
    (normalizeAtlasElement value occurrence)

-- | Apply the atlas data assignment to a page-element arrow.
--
-- The arrow is normalized before the supplied action is evaluated.  The
-- checked canonical action preserves identities and composition.  Together
-- with normalization preserving those operations, that makes this full
-- tall-spine action functorial and constant on the padded tail.
{-@ mapAtlasData :: value:Atlas atlasScope scope cellData origin final
      -> arrow:{PageElementArrow scope source target | AtlasValidArrow value arrow}
      -> DomanialInsertion
           ({datum:cellData source | atlasAcceptsDatum value (arrowSource arrow) datum})
           ({datum:cellData target | atlasAcceptsDatum value (arrowTarget arrow) datum}) @-}
-- ALIGN: ATLAS-MEMBERSHIP-MAP-INTERPRETATION.
-- ALIGN: ATLAS-MEMBERSHIP-PREIMAGE-INTERPRETATION.
mapAtlasData
  :: Atlas atlasScope scope cellData origin final
  -> PageElementArrow scope source target
  -> DomanialInsertion (cellData source) (cellData target)
{-@ reflect mapAtlasData @-}
mapAtlasData value pageArrow =
  normalizeAtlasArrowTraceValid value pageArrow `seq` atlasActionMap
    (atlasActionData (storedAtlasData value))
    (normalizeAtlasArrow value pageArrow)

-- | The data-layer action from an occurrence to its normalized
-- representative.
--
-- The checked tall-coherence law makes this extensionally the identity
-- insertion.  It is the data component of the Atlas's normalization
-- idempotent. Constructing the identity directly retains the same membership
-- predicate on both ends; 'atlasDataCoherenceAgrees' checks its forward action
-- against the stored normalization arrow.
{-@ atlasDataCoherence :: value:Atlas atlasScope scope cellData origin final
      -> occurrence:PageElement scope object
      -> DomanialInsertion
           ({datum:cellData object | atlasAcceptsDatum value occurrence datum})
           ({datum:cellData object | atlasAcceptsDatum value occurrence datum}) @-}
atlasDataCoherence
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> DomanialInsertion (cellData object) (cellData object)
{-@ reflect atlasDataCoherence @-}
-- ALIGN: ATLAS-DATA-COHERENCE-INSERTION.
atlasDataCoherence _ _ = identityInsertion

-- ALIGN: ATLAS-DATA-COHERENCE-AGREEMENT.
{-@ atlasDataCoherenceAgrees :: value:Atlas atlasScope scope cellData origin final
      -> occurrence:{PageElement scope object | AtlasValidCell value occurrence}
      -> arrow:{PageElementArrow scope object object | AtlasValidArrow value arrow && arrowSource arrow == occurrence && arrowTarget arrow == normalizeAtlasElement value occurrence}
      -> datum:{cellData object | atlasAcceptsDatum value occurrence datum}
      -> {applyInsertion (atlasDataCoherence value occurrence) datum
           == applyInsertion (mapAtlasData value arrow) datum} @-}
atlasDataCoherenceAgrees
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object -> PageElementArrow scope object object
  -> cellData object -> ()
atlasDataCoherenceAgrees value occurrence arrow datum =
  identityInsertionApply datum `seq` atlasCoherenceWitness value occurrence arrow datum

-- | Normalize a datum by applying the data component of Atlas coherence.
--
-- The checked tall-coherence law makes this operation pointwise equal to the
-- identity.
{-@ normalizeAtlasDatum :: value:Atlas atlasScope scope cellData origin final
      -> occurrence:PageElement scope object
      -> {datum:cellData object | atlasAcceptsDatum value occurrence datum}
      -> {datum:cellData object | atlasAcceptsDatum value occurrence datum} @-}
normalizeAtlasDatum
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> cellData object
normalizeAtlasDatum value occurrence =
  applyInsertion (atlasDataCoherence value occurrence)

-- | Reuse the checked laws retained by an Atlas. These eliminators keep
-- derived constructions proof-bearing instead of asking them to resupply
-- opaque unit callbacks.
-- ALIGN: ATLAS-IDENTITY-WITNESS.
{-@ atlasIdentityWitness
      :: value:Atlas atlasScope scope cellData origin final
      -> occurrence:{PageElement scope object | AtlasValidCell value occurrence} -> datum:{cellData object | atlasAcceptsDatum value occurrence datum}
      -> {applyInsertion (mapAtlasData value (identityPageElementArrow occurrence)) datum == datum} @-}
atlasIdentityWitness
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> cellData object
  -> ()
atlasIdentityWitness value occurrence datum =
  atlasDataIdentityLaw (storedAtlasData value) occurrence datum

-- ALIGN: ATLAS-COMPOSITION-WITNESS.
{-@ atlasCompositionWitness
      :: value:Atlas atlasScope scope cellData origin final
      -> second:{PageElementArrow scope middle target | AtlasValidArrow value second}
      -> first:{PageElementArrow scope source middle | AtlasValidArrow value first && arrowTarget first == arrowSource second}
      -> datum:{cellData source | atlasAcceptsDatum value (arrowSource first) datum}
      -> {applyInsertion (mapAtlasData value (composePageElementArrows second first)) datum
           == applyInsertion (mapAtlasData value second)
                (applyInsertion (mapAtlasData value first) datum)} @-}
atlasCompositionWitness
  :: Atlas atlasScope scope cellData origin final
  -> PageElementArrow scope middle target
  -> PageElementArrow scope source middle
  -> cellData source
  -> ()
atlasCompositionWitness value second first datum =
  atlasDataCompositionLaw (storedAtlasData value) second first datum

-- ALIGN: ATLAS-COHERENCE-WITNESS.
{-@ atlasCoherenceWitness
      :: value:Atlas atlasScope scope cellData origin final
      -> occurrence:{PageElement scope object | AtlasValidCell value occurrence}
      -> coherenceArrow:{PageElementArrow scope object object | AtlasValidArrow value coherenceArrow && arrowSource coherenceArrow == occurrence
           && arrowTarget coherenceArrow == normalizeAtlasElement value occurrence}
      -> datum:{cellData object | atlasAcceptsDatum value occurrence datum}
      -> {applyInsertion (mapAtlasData value coherenceArrow) datum == datum} @-}
atlasCoherenceWitness
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> PageElementArrow scope object object
  -> cellData object
  -> ()
atlasCoherenceWitness value occurrence coherenceArrow datum =
  atlasDataCoherenceLaw (storedAtlasData value) occurrence coherenceArrow datum

-- ALIGN: ATLAS-DISJOINT-WITNESS.
{-@ atlasDisjointWitness
      :: value:Atlas atlasScope scope cellData origin final
      -> left:{PageElement scope leftObject | AtlasValidCell value left} -> right:{PageElement scope rightObject | AtlasValidCell value right}
      -> leftToOrigin:{PageElementArrow scope leftObject originObject | AtlasValidArrow value leftToOrigin}
      -> rightToOrigin:{PageElementArrow scope rightObject originObject | AtlasValidArrow value rightToOrigin && pageElementPage right == pageElementPage left
           && pageElementPosition right /= pageElementPosition left
           && pageElementPage left <= atlasFinalPage (atlasPagination value)
           && arrowSource leftToOrigin == left
           && pageElementPage (arrowTarget leftToOrigin) == 0
           && arrowSource rightToOrigin == right
           && arrowTarget rightToOrigin == arrowTarget leftToOrigin}
      -> leftDatum:{cellData leftObject | atlasAcceptsDatum value left leftDatum} -> rightDatum:{cellData rightObject | atlasAcceptsDatum value right rightDatum}
      -> {applyInsertion (mapAtlasData value leftToOrigin) leftDatum
           /= applyInsertion (mapAtlasData value rightToOrigin) rightDatum} @-}
atlasDisjointWitness
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope leftObject
  -> PageElement scope rightObject
  -> PageElementArrow scope leftObject originObject
  -> PageElementArrow scope rightObject originObject
  -> cellData leftObject
  -> cellData rightObject
  -> ()
atlasDisjointWitness value left right leftToOrigin rightToOrigin leftDatum rightDatum =
  atlasDataDisjointLaw (storedAtlasData value) left right leftToOrigin rightToOrigin leftDatum rightDatum

-- | Eliminate the carrier of the @n@th page chain. Pages at or above the
-- Atlas cardinality are the padded copies of the final genuine chain.
withAtlasPageChain
  :: Atlas atlasScope scope cellData origin final
  -> Natural
  -> (forall page. Chain page -> result)
  -> result
withAtlasPageChain valueAtlas = withPageAt (atlasFolio valueAtlas)

-- | Construct a page cell from an index already certified against this
-- pagination's page-element spine.
{-@ atlasPageCell
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> index:{PageElementIndex scope |
           Elements.pageElementIndexOrigin index
             == Elements.originPageElement (atlasPageElements valueAtlas)
           && Elements.folioTraceLookup (Elements.pageElementsFolio (atlasPageElements valueAtlas))
                (Elements.pageElementIndexPage index) (Elements.pageElementIndexPosition index)
                == Just (Elements.pageElementIndexTrace index)}
      -> {element:SomePageElement scope |
           somePageElementPrecedes element
             (Elements.originPageElement (atlasPageElements valueAtlas))
           && somePageElementTransported element
             (Elements.originPageElement (atlasPageElements valueAtlas))
           && somePageElementPage element == Elements.pageElementIndexPage index
           && somePageElementPosition element == Elements.pageElementIndexPosition index
           && len (somePageElementTrace element) == Elements.pageElementIndexPage index + 1
           && traceStartsWith (Elements.pageElementIndexPosition index) (somePageElementTrace element)
           && Elements.somePageElementTraceValid (atlasPageElements valueAtlas) element} @-}
atlasPageCell
  :: Atlas atlasScope scope cellData origin final
  -> PageElementIndex scope
  -> SomePageElement scope
atlasPageCell _ = Elements.pageElement

-- | The unique origin cell of an Atlas.
{-@ atlasOriginCell
      :: valueAtlas:Atlas atlasScope scope cellData origin final
      -> {element:SomePageElement scope |
           element == Elements.originPageElement (atlasPageElements valueAtlas)} @-}
atlasOriginCell
  :: Atlas atlasScope scope cellData origin final
  -> SomePageElement scope
atlasOriginCell valueAtlas = Elements.originPageElement (atlasPageElements valueAtlas)

-- | Compare two cells after transporting them to their common earliest page.
-- Inputs on the padded tail are normalized before comparison.
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

-- | Pointwise idempotence of the Atlas coherence map.
atlasCoherenceIdempotent
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> ()
atlasCoherenceIdempotent valueAtlas =
  paginationCoherenceIdempotent (atlasPagination valueAtlas)
