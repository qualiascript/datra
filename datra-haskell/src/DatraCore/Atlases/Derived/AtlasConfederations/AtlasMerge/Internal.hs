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
  , atlasFolio
  , atlasHom
  , atlasMorphism
  , atlasMorphismAction
  , atlasObjectMap
  , atlasPageElements
  , atlasWitness
  )
import AtlasMerge.Data
  ( AtlasMergeSide (..)
  , AtlasMergeDatum (..)
  , atlasMergeDatumSide
  , atlasMergeDatumRank
  )
import AtlasExtent (atlasCellOriginRankInsertion)
import AtlasMerge.Page (AtlasMergePageCell (..))
import AtlasMerge.Assembly (atlasMergeLength, atlasMergeFolio)
import AtlasMerge.Action (atlasMerge)
import AtlasTransposal
  ( AtlasTransposalElement
  , atlasTransposal
  , atlasTransposalElement
  , withAtlasTransposalElement
  )
import Chain (chainOrderType)
import DatraOrdinal
  ( Ordinal
  , addOrdinals
  )
import DatraOrdinal (subtractOrdinal)
import DomanialInsertion
  ( DomanialInsertion
  , applyInsertion
  , insertionLeftInverse
  , domanialInsertion
  , preimage
  )
import Folio (withPageAt)
import Numeric.Natural (Natural)
import PageElements
  ( PageElement
  , pageElement
  , pageElementIndex
  , withPageElement
  )
import PageElements.Structure
  ( PageElement (..)
  )
import OrderedAtlasTransposal
  ( OrderedAtlasTransposal
  , orderedAtlasTransposal
  )

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
