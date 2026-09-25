-- | Typed failures at the parser, filesystem, syntax-expansion, and command-
-- line boundaries. Human-language rendering belongs to the locale modules.
module DatraLanguage.Diagnostics.Application
  ( ParseFailure (..)
  , ModuleLoadFailure (..)
  , SyntaxExpansionFailure (..)
  , CommandLineOptionFailure (..)
  ) where

data ParseFailure = ParseFailure
  { parseFailureMessage :: String }
  deriving (Eq, Show)

data ModuleLoadFailure
  = ImportScanFailed FilePath ParseFailure
  | ImportPathResolutionFailed String FilePath String
  | CyclicModuleImport FilePath
  | ModuleReadFailed String FilePath String
  | ImportedModuleParseFailed FilePath ParseFailure
  deriving (Eq, Show)

data SyntaxExpansionFailure
  = UnknownSyntaxControlAdapter String
  | InvalidSyntaxControlCaptures
      { syntaxControlAdapter :: String
      , expectedSyntaxCaptureCount :: Int
      , givenSyntaxCaptureCount :: Int
      }
  | InvalidDependentBinder String
  deriving (Eq, Show)

data CommandLineOptionFailure
  = UnsupportedDiagnosticLocale String
  | UnsupportedEvaluationMode String
  deriving (Eq, Show)
