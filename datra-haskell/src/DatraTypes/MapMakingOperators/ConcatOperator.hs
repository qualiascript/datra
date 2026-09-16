{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Two-page concatenation of stable-confederal data.
--
-- Concatenation first forms the flattened 'SequentialOperator' presentation,
-- then retains only its extent and final genuine page.  The canonical ordered
-- transposal returned by 'withConcatOrderedTransposal' includes those two
-- surviving pages back into the full sequential presentation.
module MapMakingOperators.ConcatOperator
  ( ConcatOperatorValues
  , ConcatOperatorValue
  , concatValue
  , concatOperator
  , concatToSequential
  , withConcatOrderedTransposal
  , (<.>)
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
  , atlasPageElements
  , atlasWitness
  , mapAtlasData
  )
import AtlasConfederation
  ( AtlasConfederation
  , AtlasConfederationObject
  , MergedAtlasConfederationScope
  )
import AtlasSequence (AtlasSequenceDatum, AtlasSequencePageCell)
import AtlasTransposal
  ( AtlasTransposalElement
  , atlasTransposal
  , atlasTransposalElement
  , withAtlasTransposalElement
  )
import Data.Kind (Type)
import Consolidation (Coconsolidation)
import DomanialInsertion (DomanialInsertion, identityInsertion)
import Folio
  ( Folio
  , appendPage
  , folio
  , lastChain
  , originChain
  , originUnique
  , originValue
  )
import Folio.LiquidInternal
  ( FolioData (..)
  , composeFolioMaps
  , identityFolioMap
  )
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
  , pageElementArrow
  , pageElementIndex
  , withPageElement
  )
import PageElements.LiquidInternal (PageElement (..))
import qualified Pagination
import MapMakingOperators.SequentialOperator
  ( SequentialOperand
  , SequentialOperatorValue
  , SequentialOperatorValues
  , sequentialOperator
  , sequentialValue
  , withSequentialOperandAtlas
  , withSequentialAtlasTraversals
  )
import StableConfederalData
  ( StableConfederalData
  , StableConfederalDataHom
  , StableConfederalDataValue
  , mapStableConfederalData
  , stableConfederalData
  , stableConfederalDataComposition
  , stableConfederalDataHom
  , stableConfederalDataIdentity
  )

-- | Defunctionalized carrier for a sequential value whose Atlas presentation
-- is collapsed to its extent and final genuine page.
data ConcatOperatorValues (left :: Type) (right :: Type)

type role ConcatOperatorValue nominal nominal nominal
newtype ConcatOperatorValue left right object =
  ConcatOperatorValue (SequentialOperatorValue left right object)

type instance
  StableConfederalDataValue (ConcatOperatorValues left right) object =
    ConcatOperatorValue left right object

-- | Introduce a concatenation value using the same Day-convolution carrier as
-- the sequential operator.
concatValue
  :: (SequentialOperand left, SequentialOperand right)
  => AtlasConfederation leftScope leftIndex
  -> AtlasConfederation rightScope rightIndex
  -> StableConfederalDataValue
       left (AtlasConfederationObject leftScope leftIndex)
  -> StableConfederalDataValue
       right (AtlasConfederationObject rightScope rightIndex)
  -> ConcatOperatorValue
       left
       right
       (AtlasConfederationObject
         (MergedAtlasConfederationScope leftScope rightScope)
         (Either leftIndex rightIndex))
concatValue left right leftValue rightValue =
  ConcatOperatorValue
    (sequentialValue left right leftValue rightValue)

-- | Form concatenated stable-confederal data.  Its presheaf action is exactly
-- the sequential action; only the representing Atlas presentation differs.
concatOperator
  :: (SequentialOperand left, SequentialOperand right)
  => StableConfederalData left
  -> StableConfederalData right
  -> StableConfederalData (ConcatOperatorValues left right)
concatOperator left right =
  stableConfederalData
    (\arrow (ConcatOperatorValue value) ->
      ConcatOperatorValue
        (mapStableConfederalData sequenced arrow value))
    (\(ConcatOperatorValue value) ->
      stableConfederalDataIdentity sequenced value)
    (\second first (ConcatOperatorValue value) ->
      stableConfederalDataComposition sequenced second first value)
  where
    sequenced = sequentialOperator left right

-- | Forget the two-page presentation and retain the underlying sequential
-- value.
concatToSequential
  :: (SequentialOperand left, SequentialOperand right)
  => StableConfederalData left
  -> StableConfederalData right
  -> StableConfederalDataHom
       (ConcatOperatorValues left right)
       (SequentialOperatorValues left right)
concatToSequential left right =
  stableConfederalDataHom
    (concatOperator left right)
    (sequentialOperator left right)
    unwrap
    (\_ _ -> ())
  where
    unwrap (ConcatOperatorValue value) = value

-- The phantom identity of a page element is retained by the collapse.  Only
-- its pagination scope and trace change.
retypePageElement
  :: PageElement sourceScope sourceObject
  -> PageElement targetScope targetObject
retypePageElement (PageElement page position trace cell) =
  PageElement page position trace cell

sequenceElement
  :: Atlas
       sequenceAtlasScope
       sequenceScope
       AtlasSequenceDatum
       ()
       AtlasSequencePageCell
  -> PageElement concatScope object
  -> PageElement sequenceScope object
sequenceElement sequenceAtlas source =
  let sequencePage =
        if pageElementPage source == 0
          then 0
          else atlasCardinality sequenceAtlas - 1
  in case pageElementIndex
      (atlasPageElements sequenceAtlas)
      sequencePage
      (pageElementPosition source) of
        Just index -> withPageElement (pageElement index) retypePageElement
        Nothing -> error "Concat collapse produced an invalid sequence cell"

concatDataMap
  :: Atlas
       sequenceAtlasScope
       sequenceScope
       AtlasSequenceDatum
       ()
       AtlasSequencePageCell
  -> PageElementArrow concatScope source target
  -> DomanialInsertion
       (AtlasSequenceDatum source)
       (AtlasSequenceDatum target)
concatDataMap sequenceAtlas sourceArrow =
  mapAtlasData sequenceAtlas
    (pageElementArrow
      (sequenceElement sequenceAtlas (arrowSource sourceArrow))
      (sequenceElement sequenceAtlas (arrowTarget sourceArrow)))

originToFinal
  :: Folio origin final
  -> Coconsolidation origin final
originToFinal (OriginFolio {}) = identityFolioMap
originToFinal (SnocPage _ previous _ transition) =
  composeFolioMaps transition (originToFinal previous)

withCollapsedSequenceAtlas
  :: Atlas
       sequenceAtlasScope
       sequenceScope
       AtlasSequenceDatum
       ()
       AtlasSequencePageCell
  -> (forall concatAtlasScope concatScope.
       Atlas
         concatAtlasScope
         concatScope
         AtlasSequenceDatum
         ()
         AtlasSequencePageCell
       -> result)
  -> result
withCollapsedSequenceAtlas sequenceAtlas useConcat =
  let pages = atlasFolio sequenceAtlas
      collapsedPages =
        appendPage
          (folio
            (originChain pages)
            (originValue pages)
            (originUnique pages))
          (lastChain pages)
          (originToFinal pages)
  in Pagination.pagination collapsedPages $ \collapsedPagination ->
      atlas
        collapsedPagination
        (atlasDataAction
          (atlasDataAt sequenceAtlas . sequenceElement sequenceAtlas)
          (concatDataMap sequenceAtlas))
        (\_ _ -> ())
        (\_ _ _ _ -> ())
        (\_ _ _ _ -> ())
        (\_ _ _ _ _ _ _ -> ())
        useConcat

data ConcatSequenceObjectMap

type instance
  AtlasMappedObject ConcatSequenceObjectMap sourceObject = sourceObject

concatObjectPreimage
  :: Atlas
       concatAtlasScope
       concatScope
       AtlasSequenceDatum
       ()
       AtlasSequencePageCell
  -> Atlas
       sequenceAtlasScope
       sequenceScope
       AtlasSequenceDatum
       ()
       AtlasSequencePageCell
  -> AtlasTransposalElement
       (AtlasObject
         sequenceAtlasScope sequenceScope AtlasSequenceDatum)
  -> Maybe
       (AtlasTransposalElement
         (AtlasObject concatAtlasScope concatScope AtlasSequenceDatum))
concatObjectPreimage concatAtlas sequenceAtlas target =
  withAtlasTransposalElement target $ \targetElement ->
    let targetPage = pageElementPage targetElement
        finalPage = atlasCardinality sequenceAtlas - 1
        concatPage
          | targetPage == 0 = Just 0
          | targetPage == finalPage = Just 1
          | otherwise = Nothing
    in do
      sourcePage <- concatPage
      index <- pageElementIndex
        (atlasPageElements concatAtlas)
        sourcePage
        (pageElementPosition targetElement)
      pure $ withPageElement (pageElement index) $
        atlasTransposalElement (atlasWitness concatAtlas)

concatOrderedTransposal
  :: Atlas
       concatAtlasScope
       concatScope
       AtlasSequenceDatum
       ()
       AtlasSequencePageCell
  -> Atlas
       sequenceAtlasScope
       sequenceScope
       AtlasSequenceDatum
       ()
       AtlasSequencePageCell
  -> OrderedAtlasTransposal
       (AtlasObject concatAtlasScope concatScope AtlasSequenceDatum)
       (AtlasObject sequenceAtlasScope sequenceScope AtlasSequenceDatum)
concatOrderedTransposal concatAtlas sequenceAtlas =
  orderedAtlasTransposal transposal (\_ _ -> ())
  where
    hom =
      atlasHom
        (atlasMorphism
          (atlasMorphismAction
            (atlasObjectMap :: AtlasObjectMap ConcatSequenceObjectMap)
            concatAtlas
            sequenceAtlas
            (sequenceElement sequenceAtlas)
            (const identityInsertion)
            (\_ _ -> ())
            (\_ _ -> ())))

    transposal =
      atlasTransposal
        (atlasWitness concatAtlas)
        hom
        (concatObjectPreimage concatAtlas sequenceAtlas)
        (const ())

-- | Evaluate concatenation.  The first Atlas is the full sequential
-- presentation, the second is its two-page collapse, and the arrow includes
-- the collapse into the full presentation by mapping page 1 to the latter's
-- final genuine page.
withConcatOrderedTransposal
  :: (SequentialOperand left, SequentialOperand right)
  => ConcatOperatorValue left right object
  -> (forall sequenceAtlasScope sequenceScope
             concatAtlasScope concatScope.
       Atlas
         sequenceAtlasScope
         sequenceScope
         AtlasSequenceDatum
         ()
         AtlasSequencePageCell
       -> Atlas
            concatAtlasScope
            concatScope
            AtlasSequenceDatum
            ()
            AtlasSequencePageCell
       -> OrderedAtlasTransposal
            (AtlasObject concatAtlasScope concatScope AtlasSequenceDatum)
            (AtlasObject
              sequenceAtlasScope sequenceScope AtlasSequenceDatum)
       -> result)
  -> result
withConcatOrderedTransposal (ConcatOperatorValue value) useConcat =
  withSequentialAtlasTraversals value $ \sequenceAtlas _ ->
    withCollapsedSequenceAtlas sequenceAtlas $ \concatAtlas ->
      useConcat
        sequenceAtlas
        concatAtlas
        (concatOrderedTransposal concatAtlas sequenceAtlas)

-- Concatenation is opaque when used as one operand of another sequential
-- expression: its already-collapsed Atlas contributes as a single member.
instance {-# OVERLAPPING #-}
    (SequentialOperand left, SequentialOperand right) =>
    SequentialOperand (ConcatOperatorValues left right) where
  withSequentialOperandAtlas _ value useAtlas =
    withConcatOrderedTransposal value $ \_ concatAtlas _ ->
      useAtlas concatAtlas

-- | Legal Haskell spelling of the requested @<,>@ operation.  ASCII comma is
-- punctuation rather than an operator character in Haskell's lexer.
infixr 7 <.>

(<.>)
  :: (SequentialOperand left, SequentialOperand right)
  => StableConfederalData left
  -> StableConfederalData right
  -> StableConfederalData (ConcatOperatorValues left right)
(<.>) = concatOperator
