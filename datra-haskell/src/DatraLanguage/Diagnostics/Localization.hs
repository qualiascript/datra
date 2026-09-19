-- | Locale selection and display of typed Datra diagnostics.
--
-- This is intentionally a presentation-layer module. Domain modules expose
-- typed error reasons without importing locales or human-language messages.
module DatraLanguage.Diagnostics.Localization
  ( Locale (..)
  , LocalizedDiagnostic (..)
  , renderDatraError
  ) where

import DatraLanguage.Diagnostics
  ( DatraError
  , LocalizedMessage
  , renderDatraErrorWith
  )
import DatraLanguage.Diagnostics.Interpreter (InterpretingError)
import DatraLanguage.Diagnostics.Locales.English qualified as English
import DatraLanguage.Diagnostics.Locales.Română qualified as Română
import MapOperators.AccessOperator (AccessError)
import SuperEllipsisRange
  ( SuperEllipsisRangeConcatError
  , SuperEllipsisRangeError
  )

data Locale = English | Română
  deriving (Eq, Ord, Show)

class LocalizedDiagnostic reason where
  localizeDiagnostic :: Locale -> reason -> LocalizedMessage

instance LocalizedDiagnostic AccessError where
  localizeDiagnostic English = English.localizeAccessError
  localizeDiagnostic Română = Română.localizeAccessError

instance LocalizedDiagnostic InterpretingError where
  localizeDiagnostic English = English.localizeInterpretingError
  localizeDiagnostic Română = Română.localizeInterpretingError

instance LocalizedDiagnostic SuperEllipsisRangeError where
  localizeDiagnostic English = English.localizeSuperEllipsisRangeError
  localizeDiagnostic Română = Română.localizeSuperEllipsisRangeError

instance LocalizedDiagnostic SuperEllipsisRangeConcatError where
  localizeDiagnostic English =
    English.localizeSuperEllipsisRangeConcatError
  localizeDiagnostic Română =
    Română.localizeSuperEllipsisRangeConcatError

renderDatraError
  :: LocalizedDiagnostic reason
  => Locale
  -> DatraError reason
  -> String
renderDatraError locale =
  renderDatraErrorWith (localizeDiagnostic locale)
