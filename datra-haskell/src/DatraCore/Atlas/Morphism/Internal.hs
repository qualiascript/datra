{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Hidden, currently unchecked representation of Atlas morphisms.
--
-- The laws documented on 'atlasMorphism' will be imposed with LiquidHaskell
-- once the executable shape of the API has settled.
module Atlas.Morphism.Internal
  ( AtlasMorphism
  , AtlasMorphismImage
  , atlasMorphismImage
  , withAtlasMorphismImage
  , atlasMorphism
  , atlasMorphismPagination
  , mapAtlasMorphismElement
  , mapAtlasMorphismArrow
  , mapAtlasMorphismData
  , identityAtlasMorphism
  , composeAtlasMorphisms
  ) where

import Atlas.Internal
  ( Atlas
  , normalizeAtlasElement
  )
import Data.Kind (Type)
import DomanialInsertion
  ( DomanialInsertion
  , composeInsertions
  , identityInsertion
  )
import PageElements
  ( PageElement
  , PageElementArrow
  , withPageElement
  )
import PageElements.Internal (SomePageElement (..))
import Pagination
  ( PaginationMorphism
  , SomePageElementArrow
  , mapPaginationArrow
  , paginationMorphism
  )

-- | The image of one source cell under an Atlas morphism.
--
-- The target page element and the data insertion are existentially packaged
-- together.  Consequently the insertion's codomain is necessarily the data
-- carrier belonging to that exact target cell.
type role AtlasMorphismImage nominal nominal nominal nominal
data AtlasMorphismImage
  (targetScope :: Type)
  (sourceCellData :: Type -> Type)
  (targetCellData :: Type -> Type)
  (sourceObject :: Type) where
  AtlasMorphismImage
    :: PageElement targetScope targetObject
    -> DomanialInsertion
         (sourceCellData sourceObject)
         (targetCellData targetObject)
    -> AtlasMorphismImage
         targetScope sourceCellData targetCellData sourceObject

-- | Package a target cell with the corresponding component of the data
-- transformation.
atlasMorphismImage
  :: PageElement targetScope targetObject
  -> DomanialInsertion
       (sourceCellData sourceObject)
       (targetCellData targetObject)
  -> AtlasMorphismImage
       targetScope sourceCellData targetCellData sourceObject
atlasMorphismImage = AtlasMorphismImage

-- | Eliminate the hidden target-cell identity of a mapped Atlas cell.
withAtlasMorphismImage
  :: AtlasMorphismImage
       targetScope sourceCellData targetCellData sourceObject
  -> (forall targetObject.
        PageElement targetScope targetObject
        -> DomanialInsertion
             (sourceCellData sourceObject)
             (targetCellData targetObject)
        -> result)
  -> result
withAtlasMorphismImage (AtlasMorphismImage target insertion) useImage =
  useImage target insertion

-- | A morphism between two particular Atlas objects.
--
-- The first two parameters are the generative identities of the source and
-- target Atlases.  The remaining parameters retain the pagination scopes and
-- dependent cell-data families needed by the executable action.  Origin and
-- final-page carrier types are existential implementation details because no
-- morphism operation exposes them.
type role AtlasMorphism nominal nominal nominal nominal nominal nominal
data AtlasMorphism
  (sourceAtlasScope :: Type)
  (targetAtlasScope :: Type)
  (sourceScope :: Type)
  (targetScope :: Type)
  (sourceCellData :: Type -> Type)
  (targetCellData :: Type -> Type) where
  AtlasMorphism
    :: Atlas
         sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
    -> Atlas
         targetAtlasScope targetScope targetCellData targetOrigin targetFinal
    -> AtlasMorphismAction
         sourceScope targetScope sourceCellData targetCellData
    -> AtlasMorphism
         sourceAtlasScope
         targetAtlasScope
         sourceScope
         targetScope
         sourceCellData
         targetCellData

-- IntelliJ's lightweight parser accepts rank-n arguments in ordinary data
-- constructors but not directly as fields of a GADT constructor.  Keeping the
-- canonical action behind this internal wrapper is type-equivalent and avoids
-- that parser-only ambiguity.
type role AtlasMorphismAction nominal nominal nominal nominal
newtype AtlasMorphismAction
  (sourceScope :: Type)
  (targetScope :: Type)
  (sourceCellData :: Type -> Type)
  (targetCellData :: Type -> Type) = AtlasMorphismAction
  (forall sourceObject.
    PageElement sourceScope sourceObject
    -> AtlasMorphismImage
         targetScope sourceCellData targetCellData sourceObject)

runAtlasMorphismAction
  :: AtlasMorphismAction
       sourceScope targetScope sourceCellData targetCellData
  -> PageElement sourceScope sourceObject
  -> AtlasMorphismImage
       targetScope sourceCellData targetCellData sourceObject
runAtlasMorphismAction (AtlasMorphismAction action) = action

-- | Construct an Atlas morphism from its canonical action.
--
-- The action is only observed on normalized source cells.  Its target cell is
-- normalized again before being exposed, so the induced full-spine action has
-- the Karoubi form
--
-- @
-- targetCoherence . canonicalAction . sourceCoherence
-- @
--
-- and is constant on the padded tails by construction.
--
-- The canonical action must eventually satisfy these laws:
--
-- * Page functoriality: its target-cell projection sends every source
--   page-element arrow to a target page-element arrow.  Equivalently it
--   preserves the thin category's precedence and exact-transport relations.
-- * Data naturality: for every source arrow @f : x -> y@, applying the source
--   Atlas data action to @f@ and then the component at @y@ agrees pointwise
--   with applying the component at @x@ and then the target Atlas data action
--   to the mapped arrow.
-- * Coherence compatibility: sandwiching either the page action or its data
--   components between the source and target Atlas coherences changes
--   nothing.  Operationally the wrapper below enforces this by normalization;
--   the future proof states its idempotent equation explicitly.
--
-- No proof witnesses are requested yet; this module intentionally exposes the
-- runtime shape before those obligations are encoded in LiquidHaskell.
atlasMorphism
  :: Atlas
       sourceAtlasScope sourceScope sourceCellData sourceOrigin sourceFinal
  -> Atlas
       targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> (forall sourceObject.
       PageElement sourceScope sourceObject
       -> AtlasMorphismImage
            targetScope sourceCellData targetCellData sourceObject)
  -> AtlasMorphism
       sourceAtlasScope
       targetAtlasScope
       sourceScope
       targetScope
       sourceCellData
       targetCellData
atlasMorphism sourceAtlas targetAtlas canonicalAction =
  AtlasMorphism
    sourceAtlas
    targetAtlas
    (AtlasMorphismAction canonicalAction)

-- | Apply an Atlas morphism to a cell and its attached data carrier.
--
-- Source and target normalization are performed here, so clients can use this
-- operation uniformly on genuine and padded page occurrences.
mapAtlasMorphismData
  :: AtlasMorphism
       sourceAtlasScope
       targetAtlasScope
       sourceScope
       targetScope
       sourceCellData
       targetCellData
  -> PageElement sourceScope sourceObject
  -> AtlasMorphismImage
       targetScope sourceCellData targetCellData sourceObject
mapAtlasMorphismData
  (AtlasMorphism sourceAtlas targetAtlas canonicalAction)
  source =
    normalizeImage targetAtlas
      (runAtlasMorphismAction
        canonicalAction
        (normalizeAtlasElement sourceAtlas source))

-- | Apply the page-element part of an Atlas morphism.
mapAtlasMorphismElement
  :: AtlasMorphism
       sourceAtlasScope
       targetAtlasScope
       sourceScope
       targetScope
       sourceCellData
       targetCellData
  -> PageElement sourceScope sourceObject
  -> SomePageElement targetScope
mapAtlasMorphismElement morphism source =
  withAtlasMorphismImage
    (mapAtlasMorphismData morphism source)
    (\target _ -> SomePageElement target)

-- | Recover the induced full-spine pagination morphism.
--
-- Arrow preservation is one of the currently documented, unchecked laws of
-- 'atlasMorphism'.  The placeholder witness here will be replaced by the
-- LiquidHaskell-checked law in the next pass.
atlasMorphismPagination
  :: AtlasMorphism
       sourceAtlasScope
       targetAtlasScope
       sourceScope
       targetScope
       sourceCellData
       targetCellData
  -> PaginationMorphism sourceScope targetScope
atlasMorphismPagination morphism =
  paginationMorphism
    (\source -> withPageElement source (mapAtlasMorphismElement morphism))
    (\_ _ -> ())

-- | Apply the page-element part of an Atlas morphism to an arrow.
mapAtlasMorphismArrow
  :: AtlasMorphism
       sourceAtlasScope
       targetAtlasScope
       sourceScope
       targetScope
       sourceCellData
       targetCellData
  -> PageElementArrow sourceScope sourceObject targetObject
  -> SomePageElementArrow targetScope
mapAtlasMorphismArrow morphism =
  mapPaginationArrow (atlasMorphismPagination morphism)

-- | The coherent identity of a particular Atlas.
--
-- On the full padded spine this maps every cell to its normalized
-- representative.  It is therefore the object's idempotent coherence map,
-- not 'Control.Category.id'.  Its canonical data component is the identity
-- insertion; the Atlas's checked tall-coherence law justifies that choice.
identityAtlasMorphism
  :: Atlas atlasScope scope cellData origin final
  -> AtlasMorphism atlasScope atlasScope scope scope cellData cellData
identityAtlasMorphism valueAtlas =
  AtlasMorphism valueAtlas valueAtlas
    (AtlasMorphismAction $ \source ->
      AtlasMorphismImage source identityInsertion)

-- | Compose Atlas morphisms in categorical order: the first argument is
-- applied after the second.
--
-- Composition uses the already coherent full-spine actions.  Thus the middle
-- Atlas coherence is present explicitly, matching composition in the Karoubi
-- envelope: @g . eMiddle . f@.  The component insertions compose in the same
-- order.
composeAtlasMorphisms
  :: AtlasMorphism
       middleAtlasScope
       targetAtlasScope
       middleScope
       targetScope
       middleCellData
       targetCellData
  -> AtlasMorphism
       sourceAtlasScope
       middleAtlasScope
       sourceScope
       middleScope
       sourceCellData
       middleCellData
  -> AtlasMorphism
       sourceAtlasScope
       targetAtlasScope
       sourceScope
       targetScope
       sourceCellData
       targetCellData
composeAtlasMorphisms
  second@(AtlasMorphism _ targetAtlas _)
  first@(AtlasMorphism sourceAtlas _ _) =
    AtlasMorphism sourceAtlas targetAtlas
      (AtlasMorphismAction $ \source ->
        withAtlasMorphismImage
          (mapAtlasMorphismData first source) $ \middle firstInsertion ->
            withAtlasMorphismImage
              (mapAtlasMorphismData second middle) $ \target secondInsertion ->
                AtlasMorphismImage target
                  (composeInsertions secondInsertion firstInsertion))

normalizeImage
  :: Atlas
       targetAtlasScope targetScope targetCellData targetOrigin targetFinal
  -> AtlasMorphismImage
       targetScope sourceCellData targetCellData sourceObject
  -> AtlasMorphismImage
       targetScope sourceCellData targetCellData sourceObject
normalizeImage targetAtlas (AtlasMorphismImage target insertion) =
  AtlasMorphismImage
    (normalizeAtlasElement targetAtlas target)
    insertion
