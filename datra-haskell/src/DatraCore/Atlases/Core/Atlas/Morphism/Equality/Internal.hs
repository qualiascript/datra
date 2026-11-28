{-# LANGUAGE GADTs #-}
{-# LANGUAGE RoleAnnotations #-}

-- | Type-equality evidence shared by syntax and the checked presheaf laws.
-- The erasure used in refinements is justified by Presheaf.equalityUnique.
module Atlas.Morphism.Equality.Internal (AtlasEquality (..)) where

import Data.Kind (Type)
import Data.Type.Equality ((:~:))

type role AtlasEquality nominal nominal
data AtlasEquality (source :: Type) (target :: Type) = AtlasEquality (source :~: target)
