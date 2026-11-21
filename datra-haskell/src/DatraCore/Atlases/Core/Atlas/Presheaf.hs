{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
#include "../../../LiquidPlugin.h"
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
-- Equality witnesses erase to one sort; the checked uniqueness lemma below
-- justifies that erasure without exposing AtlasHom constructors to clients.
{-@ embed AtlasEquality * as TypeEquality @-}

-- | Symbolic Atlas composition and its laws for contravariant actions.
module Atlas.Presheaf
  ( AtlasHom
  , presheafIdentity
  , presheafCompose
  , presheafRightIdentity
  , presheafAssociativity
  ) where

import Atlas.Morphism.Internal (AtlasHom (..), AtlasEquality (..))
import Data.Type.Equality ((:~:) (Refl))

-- A polymorphic nullary value must be inlined into refinement expressions.
{-@ inline presheafIdentity @-}
presheafIdentity :: AtlasHom object object
presheafIdentity = IdentityAtlasHom (AtlasEquality Refl)

-- ALIGN: ATLASHOM-IDENTITY-WITNESS.
{-@ reflect presheafCompose @-}
presheafCompose
  :: AtlasHom middle target
  -> AtlasHom source middle
  -> AtlasHom source target
presheafCompose second (IdentityAtlasHom (AtlasEquality Refl)) = second
presheafCompose second (CompositeAtlasHom middle first) =
  CompositeAtlasHom (presheafCompose second middle) first
presheafCompose second first@(PrimitiveAtlasHom _ _ _) =
  CompositeAtlasHom second first

{-@
presheafRightIdentity
  :: arrow:AtlasHom source target
  -> { proof:() |
       presheafCompose arrow presheafIdentity == arrow }
@-}
-- ALIGN: ATLASHOM-RIGHT-IDENTITY.

presheafRightIdentity :: AtlasHom source target -> ()
presheafRightIdentity (IdentityAtlasHom (AtlasEquality Refl)) = ()
presheafRightIdentity (PrimitiveAtlasHom _ _ _) = ()
presheafRightIdentity (CompositeAtlasHom _ _) = ()

{-@
equalityUnique
  :: first:AtlasEquality a b
  -> second:AtlasEquality c d
  -> { first == second }
@-}
-- ALIGN: ATLAS-EQUALITY-ERASURE-INJECTIVE.
-- ALIGN: ATLAS-EQUALITY-UNIQUE.
equalityUnique :: AtlasEquality a b -> AtlasEquality c d -> ()
equalityUnique (AtlasEquality Refl) (AtlasEquality Refl) = ()

{-@
presheafAssociativity
  :: third:AtlasHom secondMiddle target
  -> second:AtlasHom firstMiddle secondMiddle
  -> first:AtlasHom source firstMiddle
  -> { proof:() |
       presheafCompose third (presheafCompose second first)
       == presheafCompose (presheafCompose third second) first }
@-}
-- ALIGN: ATLASHOM-ASSOC.

presheafAssociativity
  :: AtlasHom secondMiddle target
  -> AtlasHom firstMiddle secondMiddle
  -> AtlasHom source firstMiddle
  -> ()
presheafAssociativity third second (IdentityAtlasHom equality@(AtlasEquality Refl)) =
  equalityUnique equality (AtlasEquality Refl :: AtlasEquality () ()) `seq`
  presheafRightIdentity second `seq`
    presheafRightIdentity (presheafCompose third second)
presheafAssociativity _ _ (PrimitiveAtlasHom _ _ _) = ()
presheafAssociativity third second
  (CompositeAtlasHom middle first) =
    presheafAssociativity third second middle `seq` first `seq` ()

