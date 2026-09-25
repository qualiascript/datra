-- | Resolve imports relative to the importing file, detect cycles, and retain
-- each module's own dependency context. The standard library is embedded.
module ModuleLoading (loadImports, loadExpressionImports, importSyntax) where
import Control.Exception (IOException, try)
import Data.Bifunctor qualified as Bifunctor
import System.Directory (canonicalizePath)
import System.FilePath ((</>), takeDirectory, takeExtension)
import Interpreting (moduleExportNames, moduleName)
import RuntimeModules (ModuleSource (..))
import Parsing (sourceImports, parseDatraLocatedWithSyntaxImports)
import DatraLanguage.AST
import DatraLanguage.Identifier (public)
import DatraLanguage.Diagnostics (Located (locatedValue))
import DatraLanguage.Diagnostics.Application
  ( ModuleLoadFailure (..))
import SyntaxDefinitions
import StdLib (isStandardLibraryRequest)
import IntegersLib
  ( integersLibraryFileName
  , integersLibrarySource
  , isIntegersLibraryRequest
  )

loadImports
  :: FilePath
  -> String
  -> IO (Either ModuleLoadFailure [(String, ModuleSource)])
loadImports origin source = case sourceImports source of
  Left failure -> pure (Left (ImportScanFailed origin failure))
  Right paths -> loadPaths [] origin paths

-- Canonical AST imports must be read structurally: their string spelling may
-- be compact, and source text inside a string is not another import.
loadExpressionImports
  :: FilePath
  -> Expression
  -> IO (Either ModuleLoadFailure [(String, ModuleSource)])
loadExpressionImports origin = loadPaths [] origin . paths
  where
    paths (Import _ path) = [path]
    paths value = concatMap paths (expressionChildren value)

loadPaths
  :: [FilePath]
  -> FilePath
  -> [String]
  -> IO (Either ModuleLoadFailure [(String, ModuleSource)])
loadPaths ancestors origin = fmap sequence . traverse (load ancestors origin)
  where
    go visiting parent contents = case sourceImports contents of
      Left failure -> pure (Left (ImportScanFailed parent failure))
      Right paths -> loadPaths visiting parent paths
    load visiting parent requested
      | isStandardLibraryRequest requested =
          pure (Right (requested, StdLibModule))
      | isIntegersLibraryRequest requested =
          pure $ do
            expression <- Bifunctor.first
              (ImportedModuleParseFailed integersLibraryFileName)
              (locatedValue <$> parseDatraLocatedWithSyntaxImports
                [] integersLibraryFileName integersLibrarySource)
            Right
              ( requested
              , ModuleSource integersLibraryFileName expression []
              )
      | otherwise = do
          let filename = if null (takeExtension requested) then requested <> ".datra" else requested
              location = takeDirectory parent </> filename
          resolved <- try (canonicalizePath location) :: IO (Either IOException FilePath)
          case resolved of
            Left exception -> pure (Left
              (ImportPathResolutionFailed
                requested location (show exception)))
            Right path | path `elem` visiting ->
              pure (Left (CyclicModuleImport path))
            Right path -> do
              loaded <- try (readFile path >>= \text -> length text `seq` pure text) :: IO (Either IOException String)
              case loaded of
                Left exception -> pure (Left
                  (ModuleReadFailed requested path (show exception)))
                Right text -> do
                  dependencies <- go (path:visiting) path text
                  pure $ do
                    imports <- dependencies
                    expression <- Bifunctor.first
                      (ImportedModuleParseFailed path)
                      (locatedValue <$> parseDatraLocatedWithSyntaxImports
                        (importSyntax imports) path text)
                    pure (requested, ModuleSource path expression imports)


importSyntax
  :: [(String, ModuleSource)]
  -> [(String, String, [SyntaxRule])]
importSyntax = concatMap (\(path, source) ->
  [ (path, namespace,
  [rule { syntaxModule = Just path }
  | Right exported <- [moduleExportNames source]
  , declaration <- declarations source, rule <- declarationRules declaration
  , not (null (public [(syntaxName rule, ())]))
  , syntaxName rule `elem` exported])
  | Right namespace <- [moduleName source]
  ])
  where
    declarations (ModuleSource _ expression _) =
      outer expression <> inner expression
    declarations _ = []
    outer (Program entries _) = entries
    outer _ = []
    inner expression = case namedBeginBlock expression of
      Just (_, entries, _) -> entries
      Nothing -> []
