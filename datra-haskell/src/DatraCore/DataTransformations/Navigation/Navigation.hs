-- | Monomorphisms from representable presheaves into DaTra sets.
--
-- A @Navigation atlas values@ is Lean's navigation @Yo(A) ⟶ D@. Its
-- pointwise partial left inverse is executable evidence that the natural
-- transformation is monic in the presheaf category.
module Navigation
  ( Navigation
  , navigation
  , navigationAtlas
  , navigationHom
  , mapNavigation
  , navigationPreimage
  , navigationLeftInverse
  ) where

import Navigation.Internal
  ( Navigation
  , mapNavigation
  , navigation
  , navigationAtlas
  , navigationHom
  , navigationLeftInverse
  , navigationPreimage
  )
