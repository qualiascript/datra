-- | Public folio API backed by the hidden implementation.
module Folio
  ( Folio
  , folio
  , singletonFolio
  , appendPage
  , folioLength
  , originChain
  , originValue
  , originUnique
  , lastChain
  , paddedIndex
  , withPageAt
  , withPaddedPage
  , withFolioMap
  , withPaddedFolioMap
  ) where

import Folio.Internal
  ( Folio
  , appendPage
  , folio
  , folioLength
  , lastChain
  , originChain
  , originUnique
  , originValue
  , paddedIndex
  , singletonFolio
  , withFolioMap
  , withPaddedFolioMap
  , withPaddedPage
  , withPageAt
  )
