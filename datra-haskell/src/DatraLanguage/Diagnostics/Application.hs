-- | Typed failures at the parser, filesystem, syntax-expansion, and command-
-- line boundaries. Human-language rendering belongs to the locale modules.
module DatraLanguage.Diagnostics.Application
  ( ParseFailure (..)
  , LiteralTemplateParseFailure (..)
  , ModuleInputFailure (..)
  , CandidateRejectionReason (..)
  , CandidateRejectionReport (..)
  , SyntaxRewriteFailure (..)
  , CommandLineOptionFailure (..)
  ) where

import DatraLanguage.AST (Expression)
import DatraLanguage.Diagnostics (DatraError)
import Evaluation.Error (InterpretingError)

data ParseFailure
  = DatraSourceParseFailure String
  | DatraLiteralTemplateParseFailure LiteralTemplateParseFailure
  | SyntaxEnvironmentParseFailure String
  | SyntaxRewriteParseFailure SyntaxRewriteFailure
  deriving (Eq, Show)

data LiteralTemplateParseFailure
  = MixedTemplateLiteral
  | InvalidLiteralTemplateSpacing
  | NullableLiteralTemplate
  deriving (Eq, Ord, Show)

data ModuleInputFailure
  = ModulePathResolutionFailed FilePath FilePath String
  | ModuleReadFailed String FilePath String
  | ModuleParseFailed FilePath ParseFailure
  | ModulePreparationFailed FilePath InterpretingError
  deriving (Eq, Show)

data CandidateRejectionReason
  = TypedHoleMismatch
  | GenericBoundMismatch
  | RequiredChildExhausted
  deriving (Eq, Ord, Show)

data CandidateRejectionReport = CandidateRejectionReport
  { rejectedCandidateBranch :: Int
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
  | AmbiguousStrictSyntaxImport Expression
  | RewriteStackExhausted
  | OverlappingDependentDeclarations String String
  | InvalidDependentDeclarationModifiers [String] [String]
  | ExpectedDependentDeclaration Expression
  | RejectedSyntaxCandidates [DatraError CandidateRejectionReport]
  deriving (Eq, Show)

data CommandLineOptionFailure
  = UnsupportedDiagnosticLocale String
  deriving (Eq, Show)
