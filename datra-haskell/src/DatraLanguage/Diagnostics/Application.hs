-- | Typed failures at the parser, filesystem, syntax-expansion, and command-
-- line boundaries. Human-language rendering belongs to the locale modules.
module DatraLanguage.Diagnostics.Application
  ( ParseFailure (..)
  , ModuleLoadFailure (..)
  , SyntaxTemplateAdmissibilityFailure (..)
  , CandidateRejectionReason (..)
  , CandidateRejectionReport (..)
  , SyntaxRewriteFailure (..)
  , CommandLineOptionFailure (..)
  ) where

import DatraLanguage.AST (Expression)
import DatraLanguage.Diagnostics (DatraError)

data ParseFailure
  = NeutralSourceParseFailure String
  | SyntaxEnvironmentParseFailure String
  | SyntaxRewriteParseFailure SyntaxRewriteFailure
  deriving (Eq, Show)

data ModuleLoadFailure
  = ImportScanFailed FilePath ParseFailure
  | ImportPathResolutionFailed String FilePath String
  | CyclicModuleImport FilePath
  | ModuleReadFailed String FilePath String
  | ImportedModuleParseFailed FilePath ParseFailure
  deriving (Eq, Show)

data SyntaxTemplateAdmissibilityFailure
  = NeutralSyntaxTemplateParseFailure
  | IncompleteCoreSyntaxOperator String
  | SyntaxTemplateProjectionLoss
  | UnstableSyntaxTemplateProjection
  deriving (Eq, Show)

data CandidateRejectionReason
  = TypedHoleMismatch
  | GenericBoundMismatch
  | CandidateReturnMismatch
  | RequiredChildExhausted
  deriving (Eq, Ord, Show)

data CandidateRejectionReport = CandidateRejectionReport
  { rejectedCandidateRule :: String
  , rejectedCandidateBranch :: Int
  , rejectedCandidateCapture :: Int
  , rejectedCandidateSource :: String
  , rejectedCandidateExpected :: Maybe String
  , rejectedCandidateActual :: Maybe String
  , rejectedCandidateInputs :: [(Int, String)]
  , rejectedCandidateReason :: CandidateRejectionReason
  }
  deriving (Eq, Show)

data SyntaxRewriteFailure
  = AmbiguousBareSkipApplication
  | OverlappingDependentDeclarations String String
  | NonInjectiveDependentDeclaration String
  | InvalidDeclarationModifiers [String] [String]
  | ExpectedDependentDeclaration Expression
  | InvalidRewriteSyntaxTemplate String SyntaxTemplateAdmissibilityFailure
  | RejectedSyntaxCandidates [DatraError CandidateRejectionReport]
  deriving (Eq, Show)

data CommandLineOptionFailure
  = UnsupportedDiagnosticLocale String
  deriving (Eq, Show)
