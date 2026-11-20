{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- | A flattened, ordered merge of a nonempty sequence of Atlases.
module AtlasSequence
  ( AtlasSequenceMember
  , atlasSequenceMember
  , withAtlasSequenceMember
  , AtlasSequenceDatum
  , AtlasSequencePageCell
  , atlasSequenceDatumMember
  , atlasSequenceDatumRank
  , atlasSequenceLength
  , atlasSequence
  , atlasSequenceMemberOrderedTransposal
  ) where

import Atlas
  ( Atlas
  , AtlasMappedObject
  , AtlasObject
  , AtlasObjectMap
  , atlas
  , atlasRestrictedDataAction
  , atlasMembership
  , atlasFolio
  , atlasHom
  , atlasMorphism
  , atlasMorphismAction
  , atlasObjectMap
  , atlasPageElements
  , atlasWitness
  )
import AtlasExtent (atlasCellOriginRankInsertion)
import AtlasSequence.Page (AtlasSequencePageCell)
import AtlasSequence.Assembly (atlasSequenceLength, atlasSequenceFolio)
import AtlasSequence.Member (memberPageOrder)
import AtlasSequence.Resolution
  ( AtlasSequenceMember
  , atlasSequenceMember
  , withAtlasSequenceMember
  , sequenceCellContains
  )
import AtlasTransposal
  ( AtlasTransposalElement
  , atlasTransposal
  , atlasTransposalElement
  , withAtlasTransposalElement
  )
import Chain (chainOrderType)
import Data.List.NonEmpty (NonEmpty (..), toList)
import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  , ordinalLT
  , subtractOrdinal
  )
import DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , insertionLeftInverse
  , domanialInsertion
  , preimage
  )
import Dominion (Dominion)
import AtlasSequence.Data
import Folio (withPageAt)
import Numeric.Natural (Natural)
import OrderedAtlasTransposal
  ( OrderedAtlasTransposal
  , orderedAtlasTransposal
  )
import PageElements
  ( PageElement
  , PageElementArrow
  , arrowSource
  , arrowTarget
  , pageElement
  , pageElementIndex
  , withPageElement
  )
import PageElements.Structure (PageElement (..))
import qualified Pagination

memberCount :: NonEmpty AtlasSequenceMember -> Natural
memberCount = fromIntegral . length

-- ALIGN: SEQUENCE-PAGE-PREFIX-ORDER.
prefixPageOrder
  :: [AtlasSequenceMember]
  -> Natural
  -> Natural
  -> Ordinal
prefixPageOrder members memberIndex pageNumber =
  go members memberIndex (finiteOrdinal 0)
  where
    go _ 0 accumulated = accumulated
    go [] _ accumulated = accumulated
    go (member : rest) remaining accumulated =
      go
        rest
        (remaining - 1)
        (addOrdinals accumulated (memberPageOrder member pageNumber))

-- ALIGN: SEQUENCE-DOMINION-ROUNDTRIP.
-- ALIGN: SEQUENCE-DOMINION-INTERPRETATION.
-- ALIGN: SEQUENCE-DOMINION-RANK.
-- ALIGN: SEQUENCE-INDEXED-DOMINION.
-- ALIGN: SEQUENCE-INDEXED-INTERPRETATION.
-- ALIGN: SEQUENCE-ATLAS-RANK-INTERPRETATION.
-- ALIGN: SEQUENCE-FINITE-DATA-DECODE.
-- ALIGN: SEQUENCE-FINITE-DATA-EQUIVALENCE.
-- ALIGN: SEQUENCE-FINITE-DATA-RANK.
sequenceDominionAt
  :: NonEmpty AtlasSequenceMember
  -> PageElement mergeScope object
  -> Dominion (AtlasSequenceDatum object)
sequenceDominionAt members occurrence =
  sequenceDatumDominion (memberCount members) (sequenceCellContains members occurrence)

-- ALIGN: SEQUENCE-DATA-INSERTION.
-- ALIGN: SEQUENCE-DATA-INTERPRETATION.
-- ALIGN: SEQUENCE-RESOLVED-ARROW.
-- ALIGN: SEQUENCE-ATLAS-DATA-INTERPRETATION.
-- ALIGN: SEQUENCE-FINITE-DATA-NATURALITY.
sequenceDataMap
  :: NonEmpty AtlasSequenceMember
  -> PageElementArrow mergeScope source target
  -> DomanialInsertion
       (AtlasSequenceDatum source)
       (AtlasSequenceDatum target)
sequenceDataMap members pageArrow =
  sequenceDatumInsertion
    (sequenceCellContains members (arrowSource pageArrow))
    (sequenceCellContains members (arrowTarget pageArrow))
    (const ())

-- | Merge every member under one fresh extent. Result page @n + 1@ is the
-- ordered concatenation of page @n@ from every member, so page 1 has exactly
-- one cell per member.
-- ALIGN: SEQUENCE-DATA-IDENTITY.
-- ALIGN: SEQUENCE-DATA-COMPOSITION.
-- ALIGN: SEQUENCE-ATLAS-IDENTITY.
-- ALIGN: SEQUENCE-ATLAS-COMPOSITION.
-- ALIGN: SEQUENCE-ATLAS-COHERENCE.
-- ALIGN: SEQUENCE-ATLAS-DISJOINT.
-- ALIGN: SEQUENCE-ATLAS-CONSTRUCTION.
-- ALIGN: SEQUENCE-FINITE-ELEMENTS-EQUIVALENCE.
-- ALIGN: SEQUENCE-ATLAS-ISOMORPHISM.
atlasSequence
  :: NonEmpty AtlasSequenceMember
  -> (forall mergeAtlasScope mergeScope.
       Atlas
         mergeAtlasScope
         mergeScope
         AtlasSequenceDatum
         ()
         AtlasSequencePageCell
       -> result)
  -> result
atlasSequence members useSequence =
  let pages = atlasSequenceFolio members
  in Pagination.pagination pages $ \sequencePagination ->
      atlas
        sequencePagination
        (atlasRestrictedDataAction (Pagination.paginationPageElements sequencePagination)
          (atlasMembership (sequenceCellContains members))
          (sequenceDominionAt members)
          (sequenceDataMap members))
        (\_ _ -> ())
        (\_ _ _ _ -> ())
        (\_ _ _ _ -> ())
        (\_ _ _ _ _ _ _ -> ())
        useSequence

data AtlasSequenceObjectMap

type instance
  AtlasMappedObject AtlasSequenceObjectMap sourceObject =
    AtlasSequencePageCell

retypePageElement
  :: PageElement scope sourceObject
  -> PageElement scope targetObject
retypePageElement (PageElement page position trace cell) =
  PageElement page position trace cell

sequencePageElementAt
  :: Atlas
       mergeAtlasScope
       mergeScope
       AtlasSequenceDatum
       ()
       AtlasSequencePageCell
  -> Natural
  -> Ordinal
  -> PageElement mergeScope AtlasSequencePageCell
sequencePageElementAt sequenceAtlas pageNumber position =
  case pageElementIndex
    (atlasPageElements sequenceAtlas) pageNumber position of
      Just index -> withPageElement (pageElement index) retypePageElement
      Nothing -> error "Atlas sequence inclusion produced an invalid cell"

-- ALIGN: SEQUENCE-MEMBER-OBJECT.
-- ALIGN: SEQUENCE-MEMBER-RESOLVED.
-- ALIGN: SEQUENCE-MEMBER-PAGE.
-- ALIGN: SEQUENCE-MEMBER-POSITION.
-- ALIGN: SEQUENCE-MEMBER-CHECKED-LOOKUP.
-- ALIGN: SEQUENCE-MEMBER-OBJECT-INTERPRETATION.
sequenceMemberElement
  :: [AtlasSequenceMember]
  -> Natural
  -> Atlas
       mergeAtlasScope
       mergeScope
       AtlasSequenceDatum
       ()
       AtlasSequencePageCell
  -> PageElement sourceScope sourceObject
  -> PageElement mergeScope AtlasSequencePageCell
sequenceMemberElement members memberIndex sequenceAtlas source =
  sequencePageElementAt
    sequenceAtlas
    (pageElementPage source + 1)
    (addOrdinals
      (prefixPageOrder members memberIndex (pageElementPage source))
      (pageElementPosition source))

-- ALIGN: SEQUENCE-MEMBER-COMPONENT.
-- ALIGN: SEQUENCE-MEMBER-NATURALITY.
-- ALIGN: SEQUENCE-MEMBER-INDEXED-MEMBERSHIP.
-- ALIGN: SEQUENCE-MEMBER-INDEXED-COMPONENT.
sequenceMemberComponent
  :: Natural
  -> Atlas sourceAtlasScope sourceScope sourceData sourceOrigin sourceFinal
  -> PageElement sourceScope sourceObject
  -> DomanialInsertion
       (sourceData sourceObject)
       (AtlasSequenceDatum AtlasSequencePageCell)
sequenceMemberComponent memberIndex sourceAtlas source =
  domanialInsertion
    (AtlasSequenceDatum memberIndex . applyInsertion sourceInsertion)
    sourcePreimage
    (insertionLeftInverse sourceInsertion)
  where
    sourceInsertion = atlasCellOriginRankInsertion sourceAtlas source

    sourcePreimage (AtlasSequenceDatum targetMember valueRank)
      | targetMember == memberIndex = preimage sourceInsertion valueRank
      | otherwise = Nothing

-- ALIGN: SEQUENCE-MEMBER-OBJECT-ROUNDTRIP.
-- ALIGN: SEQUENCE-MEMBER-OBJECT-INVERSE-SOUND.
-- ALIGN: SEQUENCE-MEMBER-OBJECT-OPPOSITE-REJECT.
-- ALIGN: SEQUENCE-MEMBER-NORMALIZED-OBJECT-ROUNDTRIP.
sequenceMemberObjectPreimage
  :: [AtlasSequenceMember]
  -> Natural
  -> Atlas sourceAtlasScope sourceScope sourceData sourceOrigin sourceFinal
  -> AtlasTransposalElement
       (AtlasObject mergeAtlasScope mergeScope AtlasSequenceDatum)
  -> Maybe
       (AtlasTransposalElement
         (AtlasObject sourceAtlasScope sourceScope sourceData))
sequenceMemberObjectPreimage members memberIndex sourceAtlas target =
  withAtlasTransposalElement target $ \targetElement ->
    if pageElementPage targetElement == 0
      then Nothing
      else
        let sourcePage = pageElementPage targetElement - 1
            prefix = prefixPageOrder members memberIndex sourcePage
        in do
          sourcePosition <- subtractOrdinal
            prefix
            (pageElementPosition targetElement)
          withPageAt (atlasFolio sourceAtlas) sourcePage $ \sourcePageChain ->
            if ordinalLT sourcePosition (chainOrderType sourcePageChain)
              then do
                index <- pageElementIndex
                  (atlasPageElements sourceAtlas)
                  sourcePage
                  sourcePosition
                pure $ withPageElement (pageElement index) $
                  atlasTransposalElement (atlasWitness sourceAtlas)
              else Nothing

-- | The order-preserving inclusion of one member into a sequence merge.
-- Its extent lands at the cell whose page-1 position is its member index.
-- ALIGN: SEQUENCE-MEMBER-OBJECT-INSERTION.
-- ALIGN: SEQUENCE-MEMBER-ARROW.
-- ALIGN: SEQUENCE-MEMBER-MORPHISM.
-- ALIGN: SEQUENCE-MEMBER-TRANSPOSAL.
-- ALIGN: SEQUENCE-MEMBER-ORDER.
-- ALIGN: SEQUENCE-MEMBER-ORDERED-TRANSPOSAL.
-- ALIGN: SEQUENCE-MEMBER-MORPHISM-RANK.
-- ALIGN: SEQUENCE-MEMBER-MORPHISM-INTERPRETATION.
-- ALIGN: SEQUENCE-MEMBER-ORDERED-INTERPRETATION.
atlasSequenceMemberOrderedTransposal
  :: forall sourceAtlasScope sourceScope sourceData sourceOrigin sourceFinal
      mergeAtlasScope mergeScope.
     NonEmpty AtlasSequenceMember
  -> Natural
  -> Atlas sourceAtlasScope sourceScope sourceData sourceOrigin sourceFinal
  -> Atlas
       mergeAtlasScope
       mergeScope
       AtlasSequenceDatum
       ()
       AtlasSequencePageCell
  -> OrderedAtlasTransposal
       (AtlasObject sourceAtlasScope sourceScope sourceData)
       (AtlasObject mergeAtlasScope mergeScope AtlasSequenceDatum)
atlasSequenceMemberOrderedTransposal
    members memberIndex sourceAtlas sequenceAtlas =
  orderedAtlasTransposal transposal (\_ _ -> ())
  where
    memberList = toList members

    hom =
      atlasHom
        (atlasMorphism
          (atlasMorphismAction
            (atlasObjectMap :: AtlasObjectMap AtlasSequenceObjectMap)
            sourceAtlas
            sequenceAtlas
            (sequenceMemberElement memberList memberIndex sequenceAtlas)
            (sequenceMemberComponent memberIndex sourceAtlas)
            (\_ _ -> ())
            (\_ _ -> ())))

    transposal =
      atlasTransposal
        (atlasWitness sourceAtlas)
        hom
        (sequenceMemberObjectPreimage
          memberList memberIndex sourceAtlas)
        (const ())
