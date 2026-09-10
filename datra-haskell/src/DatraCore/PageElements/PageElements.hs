-- | The category of cell occurrences of a folio.
module PageElements
  ( PageElements
  , PageElement
  , SomePageElement
  , PageElementArrow
  , pageElements
  , pageElement
  , pageElementPage
  , pageElementPosition
  , withPageElement
  , withPageElementValue
  , pageElementArrow
  , arrowSource
  , arrowTarget
  , identityPageElementArrow
  , composePageElementArrows
  ) where

import PageElements.Internal
  ( PageElement
  , PageElementArrow
  , PageElements
  , SomePageElement
  , arrowSource
  , arrowTarget
  , pageElement
  , pageElementArrow
  , pageElements
  , composePageElementArrows
  , identityPageElementArrow
  , pageElementPage
  , pageElementPosition
  , withPageElement
  , withPageElementValue
  )
