-- | Resolve imports relative to the importing file, detect cycles, and retain
-- each module's own dependency context. The standard library is embedded.
module ModuleLoading
  ( loadSourceImports
  , loadExpressionImports
  ) where
import Control.Exception (IOException, try)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.State.Strict
  ( StateT, evalStateT, get, modify )
import Data.Bifunctor qualified as Bifunctor
import System.Directory (canonicalizePath)
import System.FilePath ((</>), takeDirectory, takeExtension, takeFileName)
import Interpreting
  ( StandardLibraryVisibility (..)
  , ParsedDatraSource
  , importInvocation
  , parseDatraSourceSyntax
  , parsedSourceImportInvocations
  , rewriteParsedDatraSourceWithImports
  )
import RuntimeModules (ModuleSource (..))
import DatraLanguage.AST
import DatraLanguage.Diagnostics (Located (locatedValue))
import DatraLanguage.Diagnostics.Application
  ( ModuleLoadFailure (..))
import LibraryFiles (bundledLibrary, standardLibraryFileName)

loadSourceImports
  :: FilePath
  -> String
  -> IO (Either ModuleLoadFailure
      ([(String, ModuleSource)], ParsedDatraSource))
loadSourceImports origin source =
  case parseDatraSourceSyntax AllStandardLibrary origin source of
    Left failure -> pure (Left (ImportScanFailed origin failure))
    Right parsed -> case parsedSourceImportInvocations parsed of
      Left failure -> pure (Left (ImportScanFailed origin failure))
      Right invocations -> fmap (fmap (, parsed))
        (loadPaths [] origin (map snd invocations))

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
loadPaths ancestors origin paths =
  evalStateT (loadPathsCached ancestors origin paths) []

type ModuleCache = [(FilePath, ModuleSource)]

loadPathsCached
  :: [FilePath]
  -> FilePath
  -> [String]
  -> StateT ModuleCache IO
      (Either ModuleLoadFailure [(String, ModuleSource)])
loadPathsCached ancestors origin =
  fmap sequence . traverse (load ancestors origin)
  where
    load visiting parent requested = do
      shipped <- liftIO (bundledLibrary requested)
      case shipped of
        Just (path, text) -> do
          let identity = takeFileName path
              standardLibraryVisibility =
                if identity == standardLibraryFileName
                  then NoStandardLibrary
                  else QualifiedStandardLibrary
          cachedModule standardLibraryVisibility
            visiting requested identity path text
        Nothing -> do
          let filename = if null (takeExtension requested) then requested <> ".datra" else requested
              location = takeDirectory parent </> filename
          resolved <- liftIO
            (try (canonicalizePath location) :: IO (Either IOException FilePath))
          case resolved of
            Left exception -> pure (Left
              (ImportPathResolutionFailed
                requested location (show exception)))
            Right path | path `elem` visiting ->
              pure (Left (CyclicModuleImport path))
            Right path -> do
              cache <- get
              case lookup path cache of
                Just source -> pure (Right (requested, source))
                Nothing -> do
                  loaded <- liftIO
                    (try (readFile path >>= \text ->
                      length text `seq` pure text)
                      :: IO (Either IOException String))
                  case loaded of
                    Left exception -> pure (Left
                      (ModuleReadFailed requested path (show exception)))
                    Right text -> cachedModule QualifiedStandardLibrary
                      visiting requested path path text
    cachedModule standardLibraryVisibility
        visiting requested identity path text
      | path `elem` visiting = pure (Left (CyclicModuleImport path))
      | otherwise = do
          cache <- get
          case lookup path cache of
            Just source -> pure (Right (requested, source))
            Nothing -> do
              parsed <- parseModule standardLibraryVisibility
                visiting requested identity path text
              case parsed of
                Right result@(_, source) ->
                  Right result <$ modify ((path, source) :)
                Left failure -> pure (Left failure)
    parseModule standardLibraryVisibility
        visiting requested identity path text
      | path `elem` visiting = pure (Left (CyclicModuleImport path))
      | otherwise = case
          parseDatraSourceSyntax standardLibraryVisibility path text of
          Left failure -> pure (Left (ImportScanFailed path failure))
          Right parsed -> case parsedSourceImportInvocations parsed of
            Left failure -> pure (Left (ImportScanFailed path failure))
            Right invocations -> do
              dependencies <- loadPathsCached (path:visiting) path
                (map snd invocations)
              case dependencies of
                Left failure -> pure (Left failure)
                Right imports -> do
                  standardImport <- if
                      standardLibraryVisibility == QualifiedStandardLibrary
                    then ensureStandardLibrary (path:visiting) path imports
                    else pure (Right (Nothing, imports))
                  pure $ do
                    (implicitStandard, allImports) <- standardImport
                    expression <- Bifunctor.first
                      (ImportedModuleParseFailed path)
                      (locatedValue <$>
                        rewriteParsedDatraSourceWithImports allImports parsed)
                    let importedExpression = case implicitStandard of
                          Just standard -> prependQualifiedImport standard expression
                          Nothing -> expression
                    pure (requested,
                      ModuleSource identity importedExpression allImports)
    ensureStandardLibrary visiting parent imports =
      case
          [ requested
          | (requested, ModuleSource identity _ _) <- imports
          , takeFileName identity == standardLibraryFileName
          ] of
        requested : _ -> pure (Right (Just requested, imports))
        [] -> fmap (fmap (\standard@(requested, _) ->
          (Just requested, standard : imports)))
          (load visiting parent standardLibraryFileName)
    prependQualifiedImport requested (Program entries result) =
      Program (Import False requested : entries) result
    prependQualifiedImport _ expression = expression
