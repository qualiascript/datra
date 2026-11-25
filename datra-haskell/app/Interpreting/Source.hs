module Interpreting.Source
  ( ModuleSource (..)
  , PreparedModules
  , emptyPreparedModules
  , preparedModuleContains
  , preparedModuleNamespaceOrigins
  , preparedModuleSources
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
  ( parsedDefaultModule
  , standardLibraryParsingEnvironment
  , syntaxContext
  )
import LibraryFiles (requiredBundledLibrarySource, standardLibraryFileName)
import Parsing
  ( ResourceEnvelope (..)
  , parseDatraRawLocatedWithSourceName
  )
import SyntaxRewriting (rewriteResourceSyntaxLocated)
import StringInterpolation (SyntaxRule)
import DatraLanguage.Diagnostics (Located (..))
import DatraLanguage.Diagnostics.Application (ParseFailure (..))
import System.FilePath (takeFileName)

-- | Production source parsing is deliberately split into two phases. The
-- the source parser first reads an unresolved AST without consulting declarations;
-- this pass then applies the syntax functions visible through Std, explicit
-- module inputs, and declarations introduced by the resource itself.
data ParsedDatraSource = ParsedDatraSource
  { parsedEnvelope :: ResourceEnvelope
  , parsedRawExpression :: Located Expression
  , parsedBaseScope :: Scope
  , parsedStandardRules :: [SyntaxRule]
  , parsedBaseModuleRules :: [(String, String, [SyntaxRule])]
  }

parseDatraSourceSyntax
  :: StandardLibraryVisibility
  -> FilePath
  -> String
  -> Either ParseFailure ParsedDatraSource
parseDatraSourceSyntax standardLibraryVisibility sourceName source = do
  (envelope, locatedRaw@(Located _ raw)) <-
    parseDatraRawLocatedWithSourceName sourceName source
  (base, standardRules, baseModuleRules) <-
    Bifunctor.first (SyntaxEnvironmentParseFailure . show)
      (standardLibraryParsingEnvironment standardLibraryVisibility raw)
  pure ParsedDatraSource
    { parsedEnvelope = envelope
    , parsedRawExpression = locatedRaw
    , parsedBaseScope = base
    , parsedStandardRules = standardRules
    , parsedBaseModuleRules = baseModuleRules
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
      && null (preparedModuleSources prepared)
      && takeFileName sourceName == standardLibraryFileName
      && source == requiredBundledLibrarySource standardLibraryFileName
    then do
      (_, Located sourceSpan _) <-
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

rewriteParsedDatraSourceWithModules
  :: PreparedModules
  -> ParsedDatraSource
  -> Either ParseFailure (Located Expression)
rewriteParsedDatraSourceWithModules prepared parsed = do
  let dependencyRules =
        [ (identity, namespace, rules)
        | preparedModule <- preparedEntries
        , let identity = loadedModuleIdentity
                (preparedModuleResult preparedModule)
        , (namespace, rules) <- preparedModuleRuleSets preparedModule
        ]
      availableModuleRules = baseModuleRules <> dependencyRules
      initialRules = standardRules
      rewrite = rewriteResourceSyntaxLocated envelope
        (syntaxContext (parsedBaseScope parsed)
          (preparedModuleSources prepared)
          availableModuleRules initialRules [])
        (parsedRawExpression parsed)
  rewritten <- Bifunctor.first rewriteParseFailure rewrite
  pure (resolveGenericFunctionTypes <$> rewritten)
  where
    envelope = parsedEnvelope parsed
    standardRules = parsedStandardRules parsed
    baseModuleRules = parsedBaseModuleRules parsed
    PreparedModules preparedEntries = prepared
    rewriteParseFailure = SyntaxRewriteParseFailure

