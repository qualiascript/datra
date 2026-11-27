{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE TypeFamilies #-}

-- | Private storage shared by native and owner-checked transposal operations.
module AtlasTransposal.Element.Internal
  ( AtlasTransposalElement, TransposalElementData (..) ) where

import Atlas (AtlasObjectAtlasScope, AtlasObjectPaginationScope, AtlasObjectCellData)
import Data.Kind (Type)
import PageElements (PageElement, pageElementPage, pageElementPosition)

type AtlasTransposalElement atlasObject =
  TransposalElementData (AtlasObjectAtlasScope atlasObject)
    (AtlasObjectPaginationScope atlasObject) (AtlasObjectCellData atlasObject)

type role TransposalElementData nominal nominal nominal
data TransposalElementData atlasScope scope (cellData :: Type -> Type) where
  AtlasTransposalElement :: PageElement scope object
    -> TransposalElementData atlasScope scope cellData

instance Eq (TransposalElementData a s d) where
  AtlasTransposalElement left == AtlasTransposalElement right =
    pageElementPage left == pageElementPage right
      && pageElementPosition left == pageElementPosition right

instance Show (TransposalElementData a s d) where
  showsPrec _ (AtlasTransposalElement element) =
    showString "AtlasTransposalElement "
      . shows (pageElementPage element, pageElementPosition element)
