-- | Resolve imports relative to the importing file, detect cycles, and retain
-- each module's own dependency context. The standard library is embedded.
module ModuleLoading (loadImports, loadExpressionImports, importSyntax) where
import Control.Exception (IOException, try)
import Data.Bifunctor qualified as Bifunctor
import System.Directory (canonicalizePath)
import System.FilePath ((</>), takeDirectory, takeExtension, takeFileName)
import Interpreting (importInvocation, moduleName, moduleSyntaxRules)
import RuntimeModules (ModuleSource (..))
import Parsing
  ( sourceImports
  , parseDatraLocatedWithSyntaxImportsAndStandardLibrary
  )
import DatraLanguage.AST
import DatraLanguage.Diagnostics (Located (locatedValue))
import DatraLanguage.Diagnostics.Application
  ( ModuleLoadFailure (..))
import SyntaxDefinitions
import LibraryFiles (bundledLibrary)

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
    paths value = case importInvocation value of
      Just (_, path) -> [path]
      Nothing -> concatMap paths (expressionChildren value)

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
    load visiting parent requested = do
      shipped <- bundledLibrary requested
      case shipped of
        Just (path, text) ->
          parseModule visiting requested (takeFileName path) path text
        Nothing -> do
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
                Right text -> parseModule visiting requested path path text
    parseModule visiting requested identity path text
      | path `elem` visiting = pure (Left (CyclicModuleImport path))
      | otherwise = do
          dependencies <- go (path:visiting) path text
          pure $ do
            imports <- dependencies
            expression <- Bifunctor.first
              (ImportedModuleParseFailed path)
              (locatedValue <$>
                parseDatraLocatedWithSyntaxImportsAndStandardLibrary
                  False (importSyntax imports) path text)
            pure (requested, ModuleSource identity expression imports)


importSyntax
  :: [(String, ModuleSource)]
  -> [(String, String, [SyntaxRule])]
importSyntax = concatMap (\(path, source) ->
  [ (path, namespace, rules)
  | Right namespace <- [moduleName source]
  , Right rules <- [moduleSyntaxRules path source]
  ])
