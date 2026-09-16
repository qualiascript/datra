{-# LANGUAGE GADTs #-}
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
  , atlasDataAction
  , atlasDataAt
  , atlasFolio
  , atlasHom
  , atlasMorphism
  , atlasMorphismAction
  , atlasObjectMap
  , atlasOriginCell
  , atlasPageElements
  , atlasWitness
  , mapAtlasData
  )
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
  , ordinalLT
  )
import DatraOrdinal.Internal (subtractOrdinal)
import DomanialInsertion
  ( DomanialInsertion
  , domanialInsertion
  , preimage
  )
import Dominion (Dominion, dominion, rank, unrank)
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
  , pageElement
  , pageElementArrow
  , pageElementIndex
  , withPageElement
  )
import PageElements.LiquidInternal
  ( PageElement (..)
  )
import qualified Pagination
import OrderedAtlasTransposal
  ( OrderedAtlasTransposal
  , orderedAtlasTransposal
  )

-- | Which input Atlas supplied a cell or datum in a merge.
data AtlasMergeSide = AtlasMergeLeft | AtlasMergeRight
  deriving (Eq, Show)

-- | A cell in a non-origin page of the merged folio.
--
-- The stored list is the component cell's transport trace, beginning at the
-- represented component page and ending at that component's origin.  Keeping
-- the trace makes adjacent bouquet consolidations total without erasing any
-- of the source folios' dependent page carriers.
data AtlasMergePageCell
  = AtlasMergeLeftCell [Ordinal]
  | AtlasMergeRightCell [Ordinal]
  deriving (Eq, Show)

-- | Data in every merge cell is represented by its tagged rank in the
-- corresponding input extent.  A dominion is isomorphic to its image under
-- its rank embedding, so this is the executable counterpart of Lean's
-- @imageDom@ construction.  The phantom parameter retains the dependent
-- Atlas cell identity expected by 'Atlas'.
data AtlasMergeDatum object
  = AtlasMergeLeftDatum Natural
  | AtlasMergeRightDatum Natural
  deriving (Eq, Show)

atlasMergeDatumSide :: AtlasMergeDatum object -> AtlasMergeSide
atlasMergeDatumSide (AtlasMergeLeftDatum _) = AtlasMergeLeft
atlasMergeDatumSide (AtlasMergeRightDatum _) = AtlasMergeRight

-- | Rank in the merged extent.  Even ranks belong to the left extent and odd
-- ranks belong to the right extent, exactly as in Lean's @domSum@.
atlasMergeDatumRank :: AtlasMergeDatum object -> Natural
atlasMergeDatumRank (AtlasMergeLeftDatum valueRank) = 2 * valueRank
atlasMergeDatumRank (AtlasMergeRightDatum valueRank) = 2 * valueRank + 1

retagMergeDatum :: AtlasMergeDatum source -> AtlasMergeDatum target
retagMergeDatum (AtlasMergeLeftDatum valueRank) =
  AtlasMergeLeftDatum valueRank
retagMergeDatum (AtlasMergeRightDatum valueRank) =
  AtlasMergeRightDatum valueRank

-- | The merge has a fresh singleton origin followed by the componentwise
-- pages of both input atlases.
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
  let element = pageElement index
  pure (withPageElement element cellTrace)

mergeCellPosition :: AtlasMergePageCell -> Ordinal
mergeCellPosition (AtlasMergeLeftCell (position : _)) = position
mergeCellPosition (AtlasMergeRightCell (position : _)) = position
-- The constructors are hidden and all constructed cells have nonempty traces.
-- This total fallback also keeps malformed internal values harmless.
mergeCellPosition _ = finiteOrdinal 0

-- | The tagged componentwise page at source-spine index @n@.  Its ordinal is
-- the ordinal sum of the two component page ordinals.
atlasMergePageChain
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> Natural
  -> Chain AtlasMergePageCell
atlasMergePageChain left right pageNumber =
  withPageAt (atlasFolio left) pageNumber $ \leftPage ->
    withPageAt (atlasFolio right) pageNumber $ \rightPage ->
      let leftOrder = chainOrderType leftPage
          rightOrder = chainOrderType rightPage

          positionInPage (AtlasMergeLeftCell trace) =
            mergeCellPosition (AtlasMergeLeftCell trace)
          positionInPage (AtlasMergeRightCell trace) =
            addOrdinals leftOrder
              (mergeCellPosition (AtlasMergeRightCell trace))

          cellAt position
            | ordinalLT position leftOrder = do
                trace <- componentTraceAt left pageNumber position
                pure (AtlasMergeLeftCell trace)
            | otherwise = do
                rightPosition <- subtractOrdinal leftOrder position
                trace <- componentTraceAt right pageNumber rightPosition
                pure (AtlasMergeRightCell trace)
      in chain
          (addOrdinals leftOrder rightOrder)
          positionInPage
          cellAt
          (const ())
          (\_ _ -> ())
          (const ())

firstMergeCell
  :: Atlas atlasScope scope cellData origin final
  -> AtlasMergePageCell
firstMergeCell valueAtlas =
  let pages = atlasFolio valueAtlas
      firstPosition = chainPosition (originChain pages) (originValue pages)
  in case componentTraceAt valueAtlas 0 firstPosition of
      Just trace -> AtlasMergeLeftCell trace
      Nothing -> AtlasMergeLeftCell [firstPosition]

collapseToOrigin
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Coconsolidation () AtlasMergePageCell
collapseToOrigin left =
  op (consolidation
    (const ())
    (const (firstMergeCell left))
    (\_ _ _ -> ())
    (const ()))

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

data MergeSourceCell leftScope rightScope where
  MergeOriginCell :: MergeSourceCell leftScope rightScope
  MergeLeftSourceCell
    :: PageElement leftScope object
    -> MergeSourceCell leftScope rightScope
  MergeRightSourceCell
    :: PageElement rightScope object
    -> MergeSourceCell leftScope rightScope

mergeSourceCell
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> PageElement mergeScope object
  -> Maybe (MergeSourceCell leftScope rightScope)
mergeSourceCell left right occurrence
  | pageElementPage occurrence == 0 = Just MergeOriginCell
  | otherwise =
      let componentPage = pageElementPage occurrence - 1
          position = pageElementPosition occurrence
      in withPageAt (atlasFolio left) componentPage $ \leftPage ->
          let leftOrder = chainOrderType leftPage
          in if ordinalLT position leftOrder
              then do
                index <- pageElementIndex
                  (atlasPageElements left) componentPage position
                pure (withPageElement (pageElement index) MergeLeftSourceCell)
              else do
                rightPosition <- subtractOrdinal leftOrder position
                index <- pageElementIndex
                  (atlasPageElements right) componentPage rightPosition
                pure (withPageElement (pageElement index) MergeRightSourceCell)

extentContainsRank
  :: Atlas atlasScope scope cellData origin final
  -> Natural
  -> Bool
extentContainsRank valueAtlas valueRank =
  withPageElement (atlasOriginCell valueAtlas) $ \origin ->
    case unrank (atlasDataAt valueAtlas origin) valueRank of
      Just _ -> True
      Nothing -> False

cellContainsRank
  :: Atlas atlasScope scope cellData origin final
  -> PageElement scope object
  -> Natural
  -> Bool
cellContainsRank valueAtlas source valueRank =
  withPageElement (atlasOriginCell valueAtlas) $ \origin ->
    case unrank (atlasDataAt valueAtlas origin) valueRank of
      Nothing -> False
      Just rootDatum ->
        case preimage
          (mapAtlasData valueAtlas (pageElementArrow source origin))
          rootDatum of
          Just _ -> True
          Nothing -> False

mergeCellContains
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> PageElement mergeScope object
  -> AtlasMergeDatum datumObject
  -> Bool
mergeCellContains left right occurrence datum =
  case mergeSourceCell left right occurrence of
    Nothing -> False
    Just MergeOriginCell -> case datum of
      AtlasMergeLeftDatum valueRank -> extentContainsRank left valueRank
      AtlasMergeRightDatum valueRank -> extentContainsRank right valueRank
    Just (MergeLeftSourceCell source) -> case datum of
      AtlasMergeLeftDatum valueRank -> cellContainsRank left source valueRank
      AtlasMergeRightDatum _ -> False
    Just (MergeRightSourceCell source) -> case datum of
      AtlasMergeLeftDatum _ -> False
      AtlasMergeRightDatum valueRank -> cellContainsRank right source valueRank

mergeDatumAt
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> PageElement mergeScope object
  -> Natural
  -> Maybe (AtlasMergeDatum object)
mergeDatumAt left right occurrence combinedRank =
  let candidate
        | even combinedRank = AtlasMergeLeftDatum (combinedRank `div` 2)
        | otherwise = AtlasMergeRightDatum (combinedRank `div` 2)
  in if mergeCellContains left right occurrence candidate
      then Just candidate
      else Nothing

mergeDominionAt
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> PageElement mergeScope object
  -> Dominion (AtlasMergeDatum object)
mergeDominionAt left right occurrence =
  dominion
    atlasMergeDatumRank
    (mergeDatumAt left right occurrence)
    (const ())

mergeDataMap
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> PageElementArrow mergeScope source target
  -> DomanialInsertion (AtlasMergeDatum source) (AtlasMergeDatum target)
mergeDataMap left right pageArrow =
  domanialInsertion
    retagMergeDatum
    (\datum ->
      if mergeCellContains left right (arrowSource pageArrow) datum
        then Just (retagMergeDatum datum)
        else Nothing)
    (const ())

-- | Merge two atlases.  The result has a fresh singleton origin whose
-- dominion is the disjoint union of the input extents; result page @n + 1@
-- combines the full-spine page @n@ of each input componentwise.
--
-- The continuation keeps the freshly generated pagination and Atlas scopes
-- from escaping, following the construction style of 'Atlas.atlas'.
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
        (atlasDataAction
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

leftMergeElement
  :: Atlas mergeAtlasScope mergeScope AtlasMergeDatum () AtlasMergePageCell
  -> PageElement leftScope sourceObject
  -> PageElement mergeScope AtlasMergePageCell
leftMergeElement mergedAtlas source =
  mergePageElementAt
    mergedAtlas
    (pageElementPage source + 1)
    (pageElementPosition source)

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

leftMergeComponent
  :: Atlas leftAtlasScope leftScope leftData leftOrigin leftFinal
  -> PageElement leftScope sourceObject
  -> DomanialInsertion
       (leftData sourceObject)
       (AtlasMergeDatum AtlasMergePageCell)
leftMergeComponent leftAtlas source =
  domanialInsertion
    (AtlasMergeLeftDatum . rank sourceDominion)
    leftPreimage
    (const ())
  where
    sourceDominion = atlasDataAt leftAtlas source

    leftPreimage (AtlasMergeLeftDatum valueRank) =
      unrank sourceDominion valueRank
    leftPreimage (AtlasMergeRightDatum _) = Nothing

rightMergeComponent
  :: Atlas rightAtlasScope rightScope rightData rightOrigin rightFinal
  -> PageElement rightScope sourceObject
  -> DomanialInsertion
       (rightData sourceObject)
       (AtlasMergeDatum AtlasMergePageCell)
rightMergeComponent rightAtlas source =
  domanialInsertion
    (AtlasMergeRightDatum . rank sourceDominion)
    rightPreimage
    (const ())
  where
    sourceDominion = atlasDataAt rightAtlas source

    rightPreimage (AtlasMergeLeftDatum _) = Nothing
    rightPreimage (AtlasMergeRightDatum valueRank) =
      unrank sourceDominion valueRank

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
