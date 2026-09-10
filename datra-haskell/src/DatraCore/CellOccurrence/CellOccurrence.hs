-- | The category of cell occurrences of a folio.
module CellOccurrence
  ( CellOccurrenceCategory
  , CellOccurrence
  , CellOccurrenceArrow
  , cellOccurrenceCategory
  , cellOccurrence
  , occurrencePage
  , occurrencePosition
  , withCellOccurrence
  , cellOccurrenceArrow
  , arrowSource
  , arrowTarget
  , identityCellOccurrenceArrow
  , composeCellOccurrenceArrows
  , hasCellOccurrenceArrow
  ) where

import CellOccurrence.Internal
  ( CellOccurrence
  , CellOccurrenceArrow
  , CellOccurrenceCategory
  , arrowSource
  , arrowTarget
  , cellOccurrence
  , cellOccurrenceArrow
  , cellOccurrenceCategory
  , composeCellOccurrenceArrows
  , hasCellOccurrenceArrow
  , identityCellOccurrenceArrow
  , occurrencePage
  , occurrencePosition
  , withCellOccurrence
  )
