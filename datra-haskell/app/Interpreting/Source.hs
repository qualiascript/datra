module Interpreting.Source
  ( ModuleSource (..)
  , PreparedModules
  , emptyPreparedModules
  , preparedModuleContains
  , StandardLibraryVisibility (..)
  , ParsedDatraSource
  , parseDatraSourceSyntax
  , rewriteParsedDatraSourceWithModules
  , parseDatraSourceLocatedWithModulesAndStandardLibraryVisibility
  ) where

import Data.Bifunctor qualified as Bifunctor
import DatraLanguage.AST (Expression)
import DatraTypes.Module
import DatraTypes.Module.Source
import DatraTypes.Scope (Scope)
import DatraTypes.FunctionType (resolveGenericFunctionTypes)
import Evaluation.Expression
  ( installPreparedModules
  , parsedDefaultModule
  , standardLibraryParsingEnvironment
  , syntaxExpressionType
  )
import LibraryFiles (requiredBundledLibrarySource, standardLibraryFileName)
import Parsing (parseDatraRawLocatedWithSourceName)
import SyntaxRewriting (rewriteResourceSyntaxLocated)
import DatraLanguage.Diagnostics (Located (..))
import DatraLanguage.Diagnostics.Application (ParseFailure (..))
import System.FilePath (takeFileName)

-- | Production source parsing is deliberately split into two phases. The
-- the source parser first reads an unresolved AST without consulting declarations;
-- this pass then applies the syntax functions visible through Std, explicit
-- module inputs, and declarations introduced by the resource itself.
data ParsedDatraSource = ParsedDatraSource
  { parsedRawExpression :: Located Expression
  , parsedBaseScope :: Scope
  }

parseDatraSourceSyntax
  :: StandardLibraryVisibility
  -> FilePath
  -> String
  -> Either ParseFailure ParsedDatraSource
parseDatraSourceSyntax standardLibraryVisibility sourceName source = do
  locatedRaw@(Located _ raw) <-
    parseDatraRawLocatedWithSourceName sourceName source
  base <-
    Bifunctor.first (SyntaxEnvironmentParseFailure . show)
      (standardLibraryParsingEnvironment standardLibraryVisibility raw)
  pure ParsedDatraSource
    { parsedRawExpression = locatedRaw
    , parsedBaseScope = base
    }

parseDatraSourceLocatedWithModulesAndStandardLibraryVisibility
  :: StandardLibraryVisibility
  -> PreparedModules
  -> FilePath
  -> String
  -> Either ParseFailure (Located Expression)
parseDatraSourceLocatedWithModulesAndStandardLibraryVisibility
    standardLibraryVisibility prepared sourceName source = do
  if standardLibraryVisibility == NoStandardLibrary
      && preparedModulesEmpty prepared
      && takeFileName sourceName == standardLibraryFileName
      && source == requiredBundledLibrarySource standardLibraryFileName
    then do
      Located sourceSpan _ <-
        parseDatraRawLocatedWithSourceName sourceName source
      expressionValue <- Bifunctor.first
        (SyntaxEnvironmentParseFailure . show)
        parsedDefaultModule
      pure (Located sourceSpan expressionValue)
    else do
      parsed <- parseDatraSourceSyntax
        standardLibraryVisibility sourceName source
      rewritten <- rewriteParsedDatraSourceWithModules prepared parsed
      pure rewritten
  where
    preparedModulesEmpty (PreparedModules modules) = null modules

rewriteParsedDatraSourceWithModules
  :: PreparedModules
  -> ParsedDatraSource
  -> Either ParseFailure (Located Expression)
rewriteParsedDatraSourceWithModules prepared parsed = do
  scope <- Bifunctor.first (SyntaxEnvironmentParseFailure . show)
    (installPreparedModules prepared (parsedBaseScope parsed))
  let rewrite = rewriteResourceSyntaxLocated
        syntaxExpressionType scope (parsedRawExpression parsed)
  rewritten <- Bifunctor.first rewriteParseFailure rewrite
  pure (resolveGenericFunctionTypes <$> rewritten)
  where
    rewriteParseFailure = SyntaxRewriteParseFailure

