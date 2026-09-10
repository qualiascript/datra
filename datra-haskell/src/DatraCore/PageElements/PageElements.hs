-- | The category of cell occurrences of a folio.
module PageElements
  ( PageElements
  , PageElement
  , PageElementArrow
  , pageElements
  , pageElement
  , pageElementPage
  , pageElementPosition
  , withPageElement
  , pageElementArrow
  , arrowSource
  , arrowTarget
  , identityPageElementArrow
  , composePageElementArrows
  , hasPageElementArrow
  ) where

import PageElements.Internal
  ( PageElement
  , PageElementArrow
  , PageElements
  , arrowSource
  , arrowTarget
  , pageElement
  , pageElementArrow
  , pageElements
  , composePageElementArrows
  , hasPageElementArrow
  , identityPageElementArrow
  , pageElementPage
  , pageElementPosition
  , withPageElement
  )
