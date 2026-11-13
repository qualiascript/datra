{-# LANGUAGE GADTs #-}
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
  , atlasCardinality
  , atlasDataAction
  , atlasFolio
  , atlasHom
  , atlasMorphism
  , atlasMorphismAction
  , atlasObjectMap
  , atlasPageElements
  , atlasWitness
  )
import AtlasExtent.Internal (atlasCellOriginRankInsertion, extentContainsRank, cellContainsRank)
import AtlasTransposal
  ( AtlasTransposalElement
  , atlasTransposal
  , atlasTransposalElement
  , withAtlasTransposalElement
  )
import Chain
  ( Chain
  , chain
  , chainIndex
  , chainObjectAt
  , chainOrderType
  , chainPosition
  )
import Consolidation
  ( Coconsolidation
  , consolidation
  , consolidationPreimage
  , op
  , unop
  )
import Data.List.NonEmpty (NonEmpty (..))
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
import AtlasSequence.LiquidInternal
import Folio
  ( Folio
  , appendPage
  , originChain
  , originValue
  , pageOrder
  , singletonFolio
  , withFolioMap
  , withPageAt
  )
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
import PageElements.LiquidInternal (PageElement (..))
import qualified Pagination

-- | An existential Atlas retained as one member of a flattened sequence.
data AtlasSequenceMember where
  AtlasSequenceMember
    :: Atlas atlasScope paginationScope cellData origin final
    -> AtlasSequenceMember

atlasSequenceMember
  :: Atlas atlasScope paginationScope cellData origin final
  -> AtlasSequenceMember
atlasSequenceMember = AtlasSequenceMember

withAtlasSequenceMember
  :: AtlasSequenceMember
  -> (forall atlasScope paginationScope cellData origin final.
       Atlas atlasScope paginationScope cellData origin final
       -> result)
  -> result
withAtlasSequenceMember (AtlasSequenceMember valueAtlas) useAtlas =
  useAtlas valueAtlas

-- | A non-origin cell tagged by its member and source-cell transport trace.
data AtlasSequencePageCell = AtlasSequencePageCell Natural [Ordinal]
  deriving (Eq, Show)

memberCount :: NonEmpty AtlasSequenceMember -> Natural
memberCount = fromIntegral . length

memberCardinality :: AtlasSequenceMember -> Natural
memberCardinality member =
  withAtlasSequenceMember member atlasCardinality

-- | A sequence has a fresh extent followed by all member pages in parallel.
-- ALIGN: SEQUENCE-FOLIO-LENGTH.
-- ALIGN: SEQUENCE-FOLIO-LENGTH-INTERPRETATION.
atlasSequenceLength :: NonEmpty AtlasSequenceMember -> Natural
atlasSequenceLength members =
  maximum (fmap memberCardinality members) + 1

unitChain :: Chain ()
unitChain =
  chain
    (finiteOrdinal 1)
    (const (finiteOrdinal 0))
    (\position ->
      if position == finiteOrdinal 0 then Just () else Nothing)
    (const ())
    (\_ _ -> ())
    (const ())

cellTrace :: PageElement scope object -> [Ordinal]
cellTrace (PageElement _ _ trace _) = trace

componentTraceAt
  :: Atlas atlasScope scope cellData origin final
  -> Natural
  -> Ordinal
  -> Maybe [Ordinal]
componentTraceAt valueAtlas pageNumber position = do
  index <- pageElementIndex
    (atlasPageElements valueAtlas) pageNumber position
  pure (withPageElement (pageElement index) cellTrace)

memberPageOrder :: AtlasSequenceMember -> Natural -> Ordinal
memberPageOrder member pageNumber =
  withAtlasSequenceMember member $ \valueAtlas ->
    withPageAt (atlasFolio valueAtlas) pageNumber chainOrderType

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

withMemberAt
  :: [AtlasSequenceMember]
  -> Natural
  -> (forall atlasScope paginationScope cellData origin final.
       Atlas atlasScope paginationScope cellData origin final
       -> result)
  -> Maybe result
withMemberAt [] _ _ = Nothing
withMemberAt (member : _) 0 useAtlas =
  Just (withAtlasSequenceMember member useAtlas)
withMemberAt (_ : members) memberIndex useAtlas =
  withMemberAt members (memberIndex - 1) useAtlas

-- ALIGN: SEQUENCE-MEMBER-POSITION-RESOLVER.
-- ALIGN: SEQUENCE-MEMBER-POSITION-ROUNDTRIP.
-- ALIGN: SEQUENCE-MEMBER-POSITION-SOUND.
-- ALIGN: SEQUENCE-COMPONENT-DECODER.
withMemberAtPosition
  :: forall result.
     [AtlasSequenceMember]
  -> Natural
  -> Ordinal
  -> (forall atlasScope paginationScope cellData origin final.
       Natural
       -> Atlas atlasScope paginationScope cellData origin final
       -> Ordinal
       -> Maybe result)
  -> Maybe result
withMemberAtPosition = go 0
  where
    go
      :: Natural
      -> [AtlasSequenceMember]
      -> Natural
      -> Ordinal
      -> (forall atlasScope paginationScope cellData origin final.
           Natural
           -> Atlas atlasScope paginationScope cellData origin final
           -> Ordinal
           -> Maybe result)
      -> Maybe result
    go _ [] _ _ _ = Nothing
    go memberIndex (member : members) pageNumber position usePosition =
      withAtlasSequenceMember member $ \valueAtlas ->
        withPageAt (atlasFolio valueAtlas) pageNumber $ \sourcePage ->
          let sourceOrder = chainOrderType sourcePage
          in if ordinalLT position sourceOrder
              then usePosition memberIndex valueAtlas position
              else do
                remaining <- subtractOrdinal sourceOrder position
                go
                  (memberIndex + 1)
                  members
                  pageNumber
                  remaining
                  usePosition

-- ALIGN: SEQUENCE-PAGE-CELL-POSITION.
-- ALIGN: SEQUENCE-PAGE-TRACE-ENCODING.
sequenceCellPosition
  :: [AtlasSequenceMember]
  -> Natural
  -> AtlasSequencePageCell
  -> Ordinal
sequenceCellPosition members pageNumber
    (AtlasSequencePageCell memberIndex (position : _)) =
  addOrdinals
    (prefixPageOrder members memberIndex pageNumber)
    position
sequenceCellPosition _ _ _ = finiteOrdinal 0

-- ALIGN: SEQUENCE-PAGE-TOTAL-ORDER.
-- ALIGN: SEQUENCE-PAGE-CHAIN.
-- ALIGN: SEQUENCE-PAGE-LOOKUP.
-- ALIGN: SEQUENCE-PAGE-LOOKUP-BOUNDS.
-- ALIGN: SEQUENCE-PAGE-ORDER-INTERPRETATION.
-- ALIGN: SEQUENCE-FINITE-PAGE-EQUIVALENCE.
atlasSequencePageChain
  :: NonEmpty AtlasSequenceMember
  -> Natural
  -> Chain AtlasSequencePageCell
atlasSequencePageChain members pageNumber =
  let memberList = toList members
      pageOrderType =
        foldl
          addOrdinals
          (finiteOrdinal 0)
          (fmap (`memberPageOrder` pageNumber) memberList)

      cellAt position =
        withMemberAtPosition memberList pageNumber position $
          \memberIndex valueAtlas sourcePosition -> do
            trace <- componentTraceAt
              valueAtlas pageNumber sourcePosition
            pure (AtlasSequencePageCell memberIndex trace)
  in chain
      pageOrderType
      (sequenceCellPosition memberList pageNumber)
      cellAt
      (const ())
      (\_ _ -> ())
      (const ())

firstSequenceCell :: NonEmpty AtlasSequenceMember -> AtlasSequencePageCell
firstSequenceCell (member :| _) =
  withAtlasSequenceMember member $ \valueAtlas ->
    let pages = atlasFolio valueAtlas
        position = chainPosition (originChain pages) (originValue pages)
    in case componentTraceAt valueAtlas 0 position of
        Just trace -> AtlasSequencePageCell 0 trace
        Nothing -> AtlasSequencePageCell 0 [position]

-- ALIGN: SEQUENCE-COLLAPSE-ORIGIN.
collapseToOrigin
  :: NonEmpty AtlasSequenceMember
  -> Coconsolidation () AtlasSequencePageCell
collapseToOrigin members =
  op (consolidation
    (const ())
    (const (firstSequenceCell members))
    (\_ _ _ -> ())
    (const ()))

-- ALIGN: SEQUENCE-PAGE-PREVIOUS.
previousSequenceCell :: AtlasSequencePageCell -> AtlasSequencePageCell
previousSequenceCell
    (AtlasSequencePageCell memberIndex (_ : rest@(_ : _))) =
  AtlasSequencePageCell memberIndex rest
previousSequenceCell cell = cell

componentPreimagePosition
  :: Atlas atlasScope scope cellData origin final
  -> Natural
  -> Ordinal
  -> Maybe Ordinal
componentPreimagePosition valueAtlas targetPage sourcePosition = do
  interval <- pageOrder (targetPage - 1) targetPage
  withFolioMap (atlasFolio valueAtlas) interval $
    \sourcePage targetPageChain transition -> do
      sourceIndex <- chainIndex sourcePage sourcePosition
      let sourceCell = chainObjectAt sourceIndex
          targetCell = consolidationPreimage (unop transition) sourceCell
      pure (chainPosition targetPageChain targetCell)

-- ALIGN: SEQUENCE-PAGE-NEXT.
nextSequenceCell
  :: [AtlasSequenceMember]
  -> Natural
  -> AtlasSequencePageCell
  -> AtlasSequencePageCell
nextSequenceCell members targetPage previous =
  case previous of
    AtlasSequencePageCell memberIndex (sourcePosition : _) ->
      case withMemberAt members memberIndex $ \valueAtlas ->
        componentPreimagePosition valueAtlas targetPage sourcePosition
          >>= componentTraceAt valueAtlas targetPage of
        Just (Just trace) -> AtlasSequencePageCell memberIndex trace
        _ -> previous
    _ -> previous

-- ALIGN: SEQUENCE-PAGE-TRANSITION.
-- ALIGN: SEQUENCE-PAGE-TRANSITION-INTERPRETATION.
sequencePageTransition
  :: NonEmpty AtlasSequenceMember
  -> Natural
  -> Coconsolidation AtlasSequencePageCell AtlasSequencePageCell
sequencePageTransition members targetPage =
  op (consolidation
    previousSequenceCell
    (nextSequenceCell (toList members) targetPage)
    (\_ _ rightCell -> previousSequenceCell rightCell)
    (const ()))

-- ALIGN: SEQUENCE-FOLIO-PREFIX.
appendRemainingPages
  :: NonEmpty AtlasSequenceMember
  -> Natural
  -> Natural
  -> Folio () AtlasSequencePageCell
  -> Folio () AtlasSequencePageCell
appendRemainingPages members pageNumber depth pages
  | pageNumber >= depth = pages
  | otherwise =
      appendRemainingPages members (pageNumber + 1) depth
        (appendPage
          pages
          (atlasSequencePageChain members pageNumber)
          (sequencePageTransition members pageNumber))

-- ALIGN: SEQUENCE-FOLIO.
-- ALIGN: SEQUENCE-PADDED-PAGE-RESOLUTION.
-- ALIGN: SEQUENCE-FINITE-INDEX-INTERPRETATION.
-- ALIGN: SEQUENCE-FINITE-INTERVAL-INTERPRETATION.
atlasSequenceFolio
  :: NonEmpty AtlasSequenceMember
  -> Folio () AtlasSequencePageCell
atlasSequenceFolio members =
  let depth = maximum (fmap memberCardinality members)
      origin = singletonFolio unitChain
      firstPage = appendPage
        origin
        (atlasSequencePageChain members 0)
        (collapseToOrigin members)
  in appendRemainingPages members 1 depth firstPage

data SequenceSourceCell where
  SequenceOriginCell :: SequenceSourceCell
  SequenceMemberSourceCell
    :: Natural
    -> Atlas atlasScope scope cellData origin final
    -> PageElement scope object
    -> SequenceSourceCell

-- ALIGN: SEQUENCE-SOURCE-RESOLUTION.
-- ALIGN: SEQUENCE-SOURCE-RESOLUTION-EQUIV.
-- ALIGN: SEQUENCE-NORMALIZED-RESOLUTION.
sequenceSourceCell
  :: NonEmpty AtlasSequenceMember
  -> PageElement mergeScope object
  -> Maybe SequenceSourceCell
sequenceSourceCell members occurrence
  | pageElementPage occurrence == 0 = Just SequenceOriginCell
  | otherwise =
      let sourcePage = pageElementPage occurrence - 1
          position = pageElementPosition occurrence
      in withMemberAtPosition (toList members) sourcePage position $
          \memberIndex valueAtlas sourcePosition -> do
            index <- pageElementIndex
              (atlasPageElements valueAtlas) sourcePage sourcePosition
            pure $ withPageElement (pageElement index) $
              SequenceMemberSourceCell memberIndex valueAtlas

-- ALIGN: SEQUENCE-CELL-MEMBERSHIP.
-- ALIGN: SEQUENCE-CELL-ROOT-IMAGE.
-- ALIGN: SEQUENCE-RESOLVED-CELL.
-- ALIGN: SEQUENCE-FINITE-MEMBERSHIP.
sequenceCellContains
  :: NonEmpty AtlasSequenceMember
  -> PageElement mergeScope object
  -> AtlasSequenceDatum datumObject
  -> Bool
sequenceCellContains members occurrence
    (AtlasSequenceDatum datumMember valueRank) =
  case sequenceSourceCell members occurrence of
    Nothing -> False
    Just SequenceOriginCell ->
      maybe False id $
        withMemberAt (toList members) datumMember $ \valueAtlas ->
          extentContainsRank valueAtlas valueRank
    Just (SequenceMemberSourceCell sourceMember valueAtlas source) ->
      sourceMember == datumMember
        && cellContainsRank valueAtlas source valueRank

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
        (atlasDataAction
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

toList :: NonEmpty value -> [value]
toList (value :| values) = value : values
