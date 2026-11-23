-- | Resolve the explicit, ordered module inputs supplied by the CLI.
-- Source programs and canonical ASTs never carry filesystem paths.
module ModuleInputs
  ( loadRequestedModules
  ) where

import Control.Exception (IOException, try)
import Data.Bifunctor qualified as Bifunctor
import DatraLanguage.Diagnostics (Located (locatedValue))
import DatraLanguage.Diagnostics.Application
  ( ModuleInputFailure (..))
import Interpreting
  ( ModuleSource (..)
  , PreparedModules
  , StandardLibraryVisibility (QualifiedStandardLibrary)
  , emptyPreparedModules
  , parseDatraSourceSyntax
  , prepareModuleSource
  , preparedModuleContains
  , preparedModuleNamespaceOrigins
  , rewriteParsedDatraSourceWithModules
  , standardLibraryModuleSource
  )
import LibraryFiles (bundledLibrary, standardLibraryFileName)
import System.Directory (canonicalizePath)
import System.FilePath
  ( (</>)
  , takeDirectory
  , takeExtension
  , takeFileName
  )

data ModuleInput = ModuleInput
  { moduleInputIdentity :: FilePath
  , moduleInputSource :: String
  }

loadRequestedModules
  :: FilePath
  -> [FilePath]
  -> IO (Either ModuleInputFailure PreparedModules)
loadRequestedModules origin requested = do
  foldRequested (Right emptyPreparedModules) requested
  where
    foldRequested state [] = pure state
    foldRequested state (next : remaining) = do
      advanced <- case state of
        Left failure -> pure (Left failure)
        Right prepared -> loadRequestedModule origin prepared next
      foldRequested advanced remaining

loadRequestedModule
  :: FilePath
  -> PreparedModules
  -> FilePath
  -> IO (Either ModuleInputFailure PreparedModules)
loadRequestedModule origin prepared requested = do
  resolved <- resolveModuleInput origin requested
  pure $ do
    input <- resolved
    if preparedModuleContains
        (moduleInputIdentity input) prepared
      then Right prepared
      else prepareModuleInput prepared input

resolveModuleInput
  :: FilePath
  -> FilePath
  -> IO (Either ModuleInputFailure ModuleInput)
resolveModuleInput origin requested = do
  shipped <- bundledLibrary requested
  case shipped of
    Just (path, source) ->
      let identity = takeFileName path
      in pure (Right ModuleInput
        { moduleInputIdentity = identity
        , moduleInputSource = source
        })
    Nothing -> resolveFileModule origin requested

resolveFileModule
  :: FilePath
  -> FilePath
  -> IO (Either ModuleInputFailure ModuleInput)
resolveFileModule origin requested = do
  let filename
        | null (takeExtension requested) = requested <> ".datra"
        | otherwise = requested
      location = takeDirectory origin </> filename
  resolved <- try (canonicalizePath location)
    :: IO (Either IOException FilePath)
  case resolved of
    Left exception -> pure (Left (ModulePathResolutionFailed
      requested location (show exception)))
    Right path -> do
      loaded <- try (readFile path >>= forceText)
        :: IO (Either IOException String)
      pure $ case loaded of
        Left exception -> Left (ModuleReadFailed
          requested path (show exception))
        Right source -> Right ModuleInput
          { moduleInputIdentity = path
          , moduleInputSource = source
          }
  where
    forceText text = length text `seq` pure text

prepareModuleInput
  :: PreparedModules
  -> ModuleInput
  -> Either ModuleInputFailure PreparedModules
prepareModuleInput prepared input = do
  source <- if isStandardLibraryInput input
    then Bifunctor.first
      (ModulePreparationFailed (moduleInputIdentity input))
      standardLibraryModuleSource
    else do
      parsed <- Bifunctor.first
        (ModuleParseFailed (moduleInputIdentity input))
        (parseDatraSourceSyntax
          QualifiedStandardLibrary
          (moduleInputIdentity input)
          (moduleInputSource input))
      located <- Bifunctor.first
        (ModuleParseFailed (moduleInputIdentity input))
        (rewriteParsedDatraSourceWithModules
          prepared parsed)
      pure (ModuleSource
        (moduleInputIdentity input)
        (locatedValue located))
  updated <- Bifunctor.first
    (ModulePreparationFailed (moduleInputIdentity input))
    (prepareModuleSource prepared source)
  validateNamespaceOrigins (preparedModuleNamespaceOrigins updated)
  pure updated

isStandardLibraryInput :: ModuleInput -> Bool
isStandardLibraryInput =
  (== standardLibraryFileName) . takeFileName . moduleInputIdentity

validateNamespaceOrigins
  :: [(String, FilePath)]
  -> Either ModuleInputFailure ()
validateNamespaceOrigins origins =
  () <$ foldl add (Right []) origins
  where
    add result entry@(namespace, identity) = do
      previousOrigins <- result
      case lookup namespace previousOrigins of
        Just previous
          | previous /= identity -> Left (ModuleNamespaceCollision
              namespace previous identity)
        _ -> Right (previousOrigins <> [entry])
