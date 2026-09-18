-- | Locale selection and display of typed Datra diagnostics.
--
-- This is intentionally a presentation-layer module. Domain modules expose
-- typed error reasons without importing locales or human-language messages.
module Diagnostics.Localization
  ( Locale (..)
  , LocalizedDiagnostic (..)
  , renderDatraError
  ) where

import Diagnostics
  ( DatraError
  , LocalizedMessage
  , renderDatraErrorWith
  )
import Diagnostics.English qualified as English
import MapOperators.AccessOperator (AccessError)
import SuperEllipsisRange
  ( SuperEllipsisRangeConcatError
  , SuperEllipsisRangeError
  )

data Locale = English
  deriving (Eq, Ord, Show)

class LocalizedDiagnostic reason where
  localizeDiagnostic :: Locale -> reason -> LocalizedMessage

instance LocalizedDiagnostic AccessError where
  localizeDiagnostic English = English.localizeAccessError

instance LocalizedDiagnostic SuperEllipsisRangeError where
  localizeDiagnostic English = English.localizeSuperEllipsisRangeError

instance LocalizedDiagnostic SuperEllipsisRangeConcatError where
  localizeDiagnostic English =
    English.localizeSuperEllipsisRangeConcatError

renderDatraError
  :: LocalizedDiagnostic reason
  => Locale
  -> DatraError reason
  -> String
renderDatraError locale =
  renderDatraErrorWith (localizeDiagnostic locale)
