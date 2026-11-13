{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

-- | Hidden implementation of the object-level Atlas merge.
module AtlasMerge.Internal
  ( AtlasMergeDatum
  , AtlasMergeSide (..)
  , AtlasMergePageCell
  , atlasMergeDatumSide
  , atlasMergeDatumRank
  , atlasMergeLength
  , atlasMergeFolio
  , atlasMerge
  , atlasMergeLeftOrderedTransposal
  , atlasMergeRightOrderedTransposal
  ) where

import Atlas
  ( Atlas
  , AtlasMappedObject
  , AtlasObject
  , AtlasObjectMap
  , atlas
  , atlasCardinality
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
import AtlasMerge.LiquidInternal
  ( AtlasMergeSide (..)
  , AtlasMergeDatum (..)
  , atlasMergeDatumSide
  , atlasMergeDatumRank
  , mergeDatumDominion
  , mergeDatumInsertion
  )
import AtlasExtent.Internal (atlasCellOriginRankInsertion)
import AtlasMerge.Page (AtlasMergePageCell (..), atlasMergePageChain)
import AtlasMerge.Resolution (mergeCellContains)
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
import DatraOrdinal
  ( Ordinal
  , addOrdinals
  , finiteOrdinal
  )
import DatraOrdinal.Internal (subtractOrdinal)
import DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , insertionLeftInverse
  , domanialInsertion
  , preimage
  )
import Dominion (Dominion)
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
import PageElements
  ( PageElement
  , PageElementArrow
  , arrowSource
  , arrowTarget
  , pageElement
  , pageElementIndex
  , withPageElement
  )
import PageElements.Internal (folioTraceLookup)
import PageElements.LiquidInternal
  ( PageElement (..)
  )
import qualified Pagination
import OrderedAtlasTransposal
  ( OrderedAtlasTransposal
  , orderedAtlasTransposal
  )

-- | The merge has a fresh singleton origin followed by the componentwise
-- pages of both input atlases.
-- ALIGN: MERGE-FOLIO-LENGTH.
-- ALIGN: MERGE-FOLIO-LENGTH-INTERPRETATION.
atlasMergeLength
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> Natural
atlasMergeLength left right =
  max (atlasCardinality left) (atlasCardinality right) + 1

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

componentTraceAt
  :: Atlas atlasScope scope cellData origin final
  -> Natural
  -> Ordinal
  -> Maybe [Ordinal]
componentTraceAt valueAtlas pageNumber position =
  folioTraceLookup (atlasFolio valueAtlas) pageNumber position

firstMergeCell
  :: Atlas atlasScope scope cellData origin final
  -> AtlasMergePageCell
firstMergeCell valueAtlas =
  let pages = atlasFolio valueAtlas
      firstPosition = chainPosition (originChain pages) (originValue pages)
  in case componentTraceAt valueAtlas 0 firstPosition of
      Just trace -> AtlasMergeLeftCell trace
      Nothing -> AtlasMergeLeftCell [firstPosition]

-- ALIGN: MERGE-COLLAPSE-ORIGIN.
collapseToOrigin
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Coconsolidation () AtlasMergePageCell
collapseToOrigin left =
  op (consolidation
    (const ())
    (const (firstMergeCell left))
    (\_ _ _ -> ())
    (const ()))

-- ALIGN: MERGE-PAGE-PREVIOUS.
previousMergeCell :: AtlasMergePageCell -> AtlasMergePageCell
previousMergeCell (AtlasMergeLeftCell (_ : rest@(_ : _))) =
  AtlasMergeLeftCell rest
previousMergeCell (AtlasMergeRightCell (_ : rest@(_ : _))) =
  AtlasMergeRightCell rest
previousMergeCell cell = cell

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

-- ALIGN: MERGE-PAGE-NEXT.
nextMergeCell
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> Natural
  -> AtlasMergePageCell
  -> AtlasMergePageCell
nextMergeCell left right targetPage previous =
  case previous of
    AtlasMergeLeftCell (sourcePosition : _) ->
      maybe
      previous AtlasMergeLeftCell
      (componentPreimagePosition left targetPage sourcePosition
         >>= componentTraceAt left targetPage)
    AtlasMergeRightCell (sourcePosition : _) ->
      maybe
      previous AtlasMergeRightCell
      (componentPreimagePosition right targetPage sourcePosition
         >>= componentTraceAt right targetPage)
    _ -> previous

-- ALIGN: MERGE-PAGE-TRANSITION.
-- ALIGN: MERGE-PAGE-TRANSITION-INTERPRETATION.
-- ALIGN: MERGE-PAGE-PREIMAGE.
mergePageTransition
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> Natural
  -> Coconsolidation AtlasMergePageCell AtlasMergePageCell
mergePageTransition left right targetPage =
  op (consolidation
    previousMergeCell
    (nextMergeCell left right targetPage)
    (\_ _ rightCell -> previousMergeCell rightCell)
    (const ()))

-- ALIGN: MERGE-FOLIO-PREFIX.
appendRemainingPages
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> Natural
  -> Natural
  -> Folio () AtlasMergePageCell
  -> Folio () AtlasMergePageCell
appendRemainingPages left right pageNumber depth pages
  | pageNumber >= depth = pages
  | otherwise =
      appendRemainingPages left right (pageNumber + 1) depth
        (appendPage
          pages
          (atlasMergePageChain left right pageNumber)
          (mergePageTransition left right pageNumber))

-- | The finite bouquet folio underlying an Atlas merge.
-- ALIGN: MERGE-FOLIO.
-- ALIGN: MERGE-COMPONENT-PAGE-INDEX.
-- ALIGN: MERGE-FINITE-INDEX-INTERPRETATION.
-- ALIGN: MERGE-FINITE-INTERVAL-INTERPRETATION.
atlasMergeFolio
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> Folio () AtlasMergePageCell
atlasMergeFolio left right =
  let depth = max (atlasCardinality left) (atlasCardinality right)
      origin = singletonFolio unitChain
      firstPage = appendPage
        origin
        (atlasMergePageChain left right 0)
        (collapseToOrigin left)
  in appendRemainingPages left right 1 depth firstPage

-- ALIGN: MERGE-UNRANK-SOUND.
-- ALIGN: MERGE-BOUQUET-DATA-DECODE.
-- ALIGN: MERGE-DOMINION-ROUNDTRIP.
-- ALIGN: MERGE-DOMINION-INTERPRETATION.
-- ALIGN: MERGE-DOMINION-RANK.
-- ALIGN: MERGE-INDEXED-DOMINION.
-- ALIGN: MERGE-INDEXED-INTERPRETATION.
-- ALIGN: MERGE-ATLAS-RANK-INTERPRETATION.
-- ALIGN: MERGE-BOUQUET-DATA-EQUIVALENCE.
-- ALIGN: MERGE-BOUQUET-DATA-RANK.
mergeDominionAt
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> PageElement mergeScope object
  -> Dominion (AtlasMergeDatum object)
mergeDominionAt left right occurrence =
  mergeDatumDominion (mergeCellContains left right occurrence)

-- ALIGN: MERGE-DATA-INSERTION.
-- ALIGN: MERGE-DATA-INTERPRETATION.
-- ALIGN: MERGE-DATA-IDENTITY.
-- ALIGN: MERGE-DATA-COMPOSITION.
-- ALIGN: MERGE-RESOLVED-ARROW.
-- ALIGN: MERGE-ATLAS-DATA-INTERPRETATION.
-- ALIGN: MERGE-BOUQUET-DATA-NATURALITY.
mergeDataMap
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> PageElementArrow mergeScope source target
  -> DomanialInsertion (AtlasMergeDatum source) (AtlasMergeDatum target)
mergeDataMap left right pageArrow =
  mergeDatumInsertion
    (mergeCellContains left right (arrowSource pageArrow))
    (mergeCellContains left right (arrowTarget pageArrow))
    (const ())

-- | Merge two atlases.  The result has a fresh singleton origin whose
-- dominion is the disjoint union of the input extents; result page @n + 1@
-- combines the full-spine page @n@ of each input componentwise.
--
-- The continuation keeps the freshly generated pagination and Atlas scopes
-- from escaping, following the construction style of 'Atlas.atlas'.
-- ALIGN: MERGE-ATLAS-IDENTITY.
-- ALIGN: MERGE-ATLAS-COMPOSITION.
-- ALIGN: MERGE-ATLAS-COHERENCE.
-- ALIGN: MERGE-ATLAS-DISJOINT.
-- ALIGN: MERGE-ATLAS-CONSTRUCTION.
-- ALIGN: MERGE-FINITE-ELEMENTS-EQUIVALENCE.
-- ALIGN: MERGE-BOUQUET-ATLAS-ISOMORPHISM.
atlasMerge
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> (forall mergeAtlasScope mergeScope.
       Atlas
         mergeAtlasScope
         mergeScope
         AtlasMergeDatum
         ()
         AtlasMergePageCell
       -> result)
  -> result
atlasMerge left right useMerge =
  let pages = atlasMergeFolio left right
  in Pagination.pagination pages $ \mergePagination ->
      atlas
        mergePagination
        (atlasRestrictedDataAction (Pagination.paginationPageElements mergePagination)
          (atlasMembership (mergeCellContains left right))
          (mergeDominionAt left right)
          (mergeDataMap left right))
        (\_ _ -> ())
        (\_ _ _ _ -> ())
        (\_ _ _ _ -> ())
        (\_ _ _ _ _ _ _ -> ())
        useMerge

-- | Type-level object actions for the two canonical inclusions into an Atlas
-- merge. Every input cell lands on the corresponding non-origin merge cell.
data LeftAtlasMergeObjectMap
data RightAtlasMergeObjectMap

type instance
  AtlasMappedObject LeftAtlasMergeObjectMap sourceObject =
    AtlasMergePageCell

type instance
  AtlasMappedObject RightAtlasMergeObjectMap sourceObject =
    AtlasMergePageCell

retypePageElement
  :: PageElement scope sourceObject
  -> PageElement scope targetObject
retypePageElement (PageElement page position trace cell) =
  PageElement page position trace cell

mergePageElementAt
  :: Atlas mergeAtlasScope mergeScope AtlasMergeDatum () AtlasMergePageCell
  -> Natural
  -> Ordinal
  -> PageElement mergeScope AtlasMergePageCell
mergePageElementAt mergedAtlas pageNumber position =
  case pageElementIndex
    (atlasPageElements mergedAtlas) pageNumber position of
      Just index ->
        withPageElement (pageElement index) retypePageElement
      Nothing -> error "Atlas merge inclusion produced an invalid cell"

-- ALIGN: MERGE-LEFT-OBJECT.
-- ALIGN: MERGE-LEFT-PAGE.
-- ALIGN: MERGE-LEFT-POSITION.
-- ALIGN: MERGE-LEFT-RESOLVED.
-- ALIGN: MERGE-LEFT-CHECKED-LOOKUP.
-- ALIGN: MERGE-LEFT-OBJECT-INTERPRETATION.
leftMergeElement
  :: Atlas mergeAtlasScope mergeScope AtlasMergeDatum () AtlasMergePageCell
  -> PageElement leftScope sourceObject
  -> PageElement mergeScope AtlasMergePageCell
leftMergeElement mergedAtlas source =
  mergePageElementAt
    mergedAtlas
    (pageElementPage source + 1)
    (pageElementPosition source)

-- ALIGN: MERGE-RIGHT-OBJECT.
-- ALIGN: MERGE-RIGHT-PAGE.
-- ALIGN: MERGE-RIGHT-POSITION.
-- ALIGN: MERGE-RIGHT-RESOLVED.
-- ALIGN: MERGE-RIGHT-CHECKED-LOOKUP.
-- ALIGN: MERGE-RIGHT-OBJECT-INTERPRETATION.
rightMergeElement
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas mergeAtlasScope mergeScope AtlasMergeDatum () AtlasMergePageCell
  -> PageElement rightScope sourceObject
  -> PageElement mergeScope AtlasMergePageCell
rightMergeElement leftAtlas mergedAtlas source =
  withPageAt (atlasFolio leftAtlas) (pageElementPage source) $ \leftPage ->
    mergePageElementAt
      mergedAtlas
      (pageElementPage source + 1)
      (addOrdinals
        (chainOrderType leftPage)
        (pageElementPosition source))

-- ALIGN: MERGE-LEFT-COMPONENT.
-- ALIGN: MERGE-LEFT-NATURALITY.
-- ALIGN: MERGE-LEFT-INDEXED-MEMBERSHIP.
-- ALIGN: MERGE-LEFT-INDEXED-COMPONENT.
leftMergeComponent
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> PageElement leftScope sourceObject
  -> DomanialInsertion
       (leftData sourceObject)
       (AtlasMergeDatum AtlasMergePageCell)
leftMergeComponent leftAtlas source =
  domanialInsertion
    (AtlasMergeLeftDatum . applyInsertion sourceInsertion)
    leftPreimage
    (insertionLeftInverse sourceInsertion)
  where
    sourceInsertion = atlasCellOriginRankInsertion leftAtlas source

    leftPreimage (AtlasMergeLeftDatum valueRank) =
      preimage sourceInsertion valueRank
    leftPreimage (AtlasMergeRightDatum _) = Nothing

-- ALIGN: MERGE-RIGHT-COMPONENT.
-- ALIGN: MERGE-RIGHT-NATURALITY.
-- ALIGN: MERGE-RIGHT-INDEXED-MEMBERSHIP.
-- ALIGN: MERGE-RIGHT-INDEXED-COMPONENT.
rightMergeComponent
  :: Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> PageElement rightScope sourceObject
  -> DomanialInsertion
       (rightData sourceObject)
       (AtlasMergeDatum AtlasMergePageCell)
rightMergeComponent rightAtlas source =
  domanialInsertion
    (AtlasMergeRightDatum . applyInsertion sourceInsertion)
    rightPreimage
    (insertionLeftInverse sourceInsertion)
  where
    sourceInsertion = atlasCellOriginRankInsertion rightAtlas source

    rightPreimage (AtlasMergeLeftDatum _) = Nothing
    rightPreimage (AtlasMergeRightDatum valueRank) =
      preimage sourceInsertion valueRank

-- ALIGN: MERGE-LEFT-OBJECT-ROUNDTRIP.
-- ALIGN: MERGE-LEFT-OBJECT-INVERSE-SOUND.
-- ALIGN: MERGE-LEFT-OBJECT-OPPOSITE-REJECT.
-- ALIGN: MERGE-LEFT-NORMALIZED-OBJECT-ROUNDTRIP.
leftMergeObjectPreimage
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> AtlasTransposalElement
       (AtlasObject mergeAtlasScope mergeScope AtlasMergeDatum)
  -> Maybe
       (AtlasTransposalElement
         (AtlasObject leftAtlasScope leftScope leftData))
leftMergeObjectPreimage leftAtlas target =
  withAtlasTransposalElement target $ \targetElement ->
    if pageElementPage targetElement == 0
      then Nothing
      else do
        index <- pageElementIndex
          (atlasPageElements leftAtlas)
          (pageElementPage targetElement - 1)
          (pageElementPosition targetElement)
        pure $ withPageElement (pageElement index) $
          atlasTransposalElement (atlasWitness leftAtlas)

-- ALIGN: MERGE-RIGHT-OBJECT-ROUNDTRIP.
-- ALIGN: MERGE-RIGHT-OBJECT-INVERSE-SOUND.
-- ALIGN: MERGE-RIGHT-OBJECT-OPPOSITE-REJECT.
-- ALIGN: MERGE-RIGHT-NORMALIZED-OBJECT-ROUNDTRIP.
rightMergeObjectPreimage
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> AtlasTransposalElement
       (AtlasObject mergeAtlasScope mergeScope AtlasMergeDatum)
  -> Maybe
       (AtlasTransposalElement
         (AtlasObject rightAtlasScope rightScope rightData))
rightMergeObjectPreimage leftAtlas rightAtlas target =
  withAtlasTransposalElement target $ \targetElement ->
    if pageElementPage targetElement == 0
      then Nothing
      else
        let sourcePage = pageElementPage targetElement - 1
        in withPageAt (atlasFolio leftAtlas) sourcePage $ \leftPage -> do
          sourcePosition <- subtractOrdinal
            (chainOrderType leftPage)
            (pageElementPosition targetElement)
          index <- pageElementIndex
            (atlasPageElements rightAtlas)
            sourcePage
            sourcePosition
          pure $ withPageElement (pageElement index) $
            atlasTransposalElement (atlasWitness rightAtlas)

-- | The canonical order-preserving inclusion of the left Atlas into its
-- merge. Its extent is sent to element 0 of merge page 1.
-- ALIGN: MERGE-LEFT-OBJECT-INSERTION.
-- ALIGN: MERGE-LEFT-ARROW.
-- ALIGN: MERGE-LEFT-MORPHISM.
-- ALIGN: MERGE-LEFT-TRANSPOSAL.
-- ALIGN: MERGE-LEFT-ORDER.
-- ALIGN: MERGE-LEFT-ORDERED-TRANSPOSAL.
-- ALIGN: MERGE-LEFT-MORPHISM-RANK.
-- ALIGN: MERGE-LEFT-MORPHISM-INTERPRETATION.
-- ALIGN: MERGE-LEFT-ORDERED-INTERPRETATION.
atlasMergeLeftOrderedTransposal
  :: forall leftAtlasScope leftScope leftData leftOrigin leftFinal
      rightAtlasScope rightScope rightData rightOrigin rightFinal
      mergeAtlasScope mergeScope.
     Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> Atlas mergeAtlasScope mergeScope AtlasMergeDatum () AtlasMergePageCell
  -> OrderedAtlasTransposal
       (AtlasObject leftAtlasScope leftScope leftData)
       (AtlasObject mergeAtlasScope mergeScope AtlasMergeDatum)
atlasMergeLeftOrderedTransposal leftAtlas _ mergedAtlas =
  orderedAtlasTransposal transposal (\_ _ -> ())
  where
    hom =
      atlasHom
        (atlasMorphism
          (atlasMorphismAction
            (atlasObjectMap :: AtlasObjectMap LeftAtlasMergeObjectMap)
            leftAtlas
            mergedAtlas
            (leftMergeElement mergedAtlas)
            (leftMergeComponent leftAtlas)
            (\_ _ -> ())
            (\_ _ -> ())))

    transposal =
      atlasTransposal
        (atlasWitness leftAtlas)
        hom
        (leftMergeObjectPreimage leftAtlas)
        (const ())

-- | The canonical order-preserving inclusion of the right Atlas into its
-- merge. Its extent is sent to element 1 of merge page 1, after the left
-- extent.
-- ALIGN: MERGE-RIGHT-OBJECT-INSERTION.
-- ALIGN: MERGE-RIGHT-ARROW.
-- ALIGN: MERGE-RIGHT-MORPHISM.
-- ALIGN: MERGE-RIGHT-TRANSPOSAL.
-- ALIGN: MERGE-RIGHT-ORDER.
-- ALIGN: MERGE-RIGHT-ORDERED-TRANSPOSAL.
-- ALIGN: MERGE-RIGHT-MORPHISM-RANK.
-- ALIGN: MERGE-RIGHT-MORPHISM-INTERPRETATION.
-- ALIGN: MERGE-RIGHT-ORDERED-INTERPRETATION.
atlasMergeRightOrderedTransposal
  :: forall leftAtlasScope leftScope leftData leftOrigin leftFinal
      rightAtlasScope rightScope rightData rightOrigin rightFinal
      mergeAtlasScope mergeScope.
     Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> Atlas mergeAtlasScope mergeScope AtlasMergeDatum () AtlasMergePageCell
  -> OrderedAtlasTransposal
       (AtlasObject rightAtlasScope rightScope rightData)
       (AtlasObject mergeAtlasScope mergeScope AtlasMergeDatum)
atlasMergeRightOrderedTransposal leftAtlas rightAtlas mergedAtlas =
  orderedAtlasTransposal transposal (\_ _ -> ())
  where
    hom =
      atlasHom
        (atlasMorphism
          (atlasMorphismAction
            (atlasObjectMap :: AtlasObjectMap RightAtlasMergeObjectMap)
            rightAtlas
            mergedAtlas
            (rightMergeElement leftAtlas mergedAtlas)
            (rightMergeComponent rightAtlas)
            (\_ _ -> ())
            (\_ _ -> ())))

    transposal =
      atlasTransposal
        (atlasWitness rightAtlas)
        hom
        (rightMergeObjectPreimage leftAtlas rightAtlas)
        (const ())
