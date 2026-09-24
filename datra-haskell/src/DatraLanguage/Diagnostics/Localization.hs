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
import DatraLanguage.Diagnostics.Application
  ( CommandLineOptionFailure
  , ModuleLoadFailure
  , ParseFailure
  , SyntaxExpansionFailure
  )
import Evaluation.Error (InterpretingError)
import DatraLanguage.Diagnostics.Locales.English qualified as English
import DatraLanguage.Diagnostics.Locales.Romanian qualified as Romanian
import MapOperators.AccessOperator (AccessError)
import SuperEllipsisRange
  ( SuperEllipsisRangeConcatError
  , SuperEllipsisRangeError
  )

data Locale = English | Romanian
  deriving (Eq, Ord, Show)

class LocalizedDiagnostic reason where
  localizeDiagnostic :: Locale -> reason -> LocalizedMessage

instance LocalizedDiagnostic AccessError where
  localizeDiagnostic English = English.localizeAccessError
  localizeDiagnostic Romanian = Romanian.localizeAccessError

instance LocalizedDiagnostic ParseFailure where
  localizeDiagnostic English = English.localizeParseFailure
  localizeDiagnostic Romanian = Romanian.localizeParseFailure

instance LocalizedDiagnostic ModuleLoadFailure where
  localizeDiagnostic English = English.localizeModuleLoadFailure
  localizeDiagnostic Romanian = Romanian.localizeModuleLoadFailure

instance LocalizedDiagnostic SyntaxExpansionFailure where
  localizeDiagnostic English = English.localizeSyntaxExpansionFailure
  localizeDiagnostic Romanian = Romanian.localizeSyntaxExpansionFailure

instance LocalizedDiagnostic CommandLineOptionFailure where
  localizeDiagnostic English = English.localizeCommandLineOptionFailure
  localizeDiagnostic Romanian = Romanian.localizeCommandLineOptionFailure

instance LocalizedDiagnostic InterpretingError where
  localizeDiagnostic English = English.localizeInterpretingError
  localizeDiagnostic Romanian = Romanian.localizeInterpretingError

instance LocalizedDiagnostic SuperEllipsisRangeError where
  localizeDiagnostic English = English.localizeSuperEllipsisRangeError
  localizeDiagnostic Romanian = Romanian.localizeSuperEllipsisRangeError

instance LocalizedDiagnostic SuperEllipsisRangeConcatError where
  localizeDiagnostic English =
    English.localizeSuperEllipsisRangeConcatError
  localizeDiagnostic Romanian =
    Romanian.localizeSuperEllipsisRangeConcatError

renderDatraError
  :: LocalizedDiagnostic reason
  => Locale
  -> DatraError reason
  -> String
renderDatraError locale =
  renderDatraErrorWith (localizeDiagnostic locale)
