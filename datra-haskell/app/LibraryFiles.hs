-- | Generic discovery for Datra modules distributed in @libs/@.
module LibraryFiles
  ( bundledLibrary
  , requiredBundledLibrarySource
  , standardLibraryFileName
  ) where

import Control.Exception (IOException, try)
import Paths_datra_haskell (getDataFileName)
import System.Directory (doesFileExist)
import System.FilePath (takeExtension, takeFileName, (</>))
import System.IO.Unsafe (unsafePerformIO)

standardLibraryFileName :: FilePath
standardLibraryFileName = "std.datra"

-- | Resolve any shipped library by its bare name, filename, or @libs/@ path.
-- The directory contents, rather than a Haskell registry, decide which
-- optional modules exist.
bundledLibrary :: FilePath -> IO (Maybe (FilePath, String))
bundledLibrary requested = do
  let filename = libraryFileName requested
  path <- getDataFileName ("libs" </> filename)
  exists <- doesFileExist path
  if not exists
    then pure Nothing
    else do
      loaded <- try (readFile path) :: IO (Either IOException String)
      pure ((path,) <$> either (const Nothing) Just loaded)
  where
    libraryFileName path =
      let filename = takeFileName path
      in if null (takeExtension filename)
          then filename <> ".datra"
          else filename

-- | The parser bootstrap is pure and cached for the process lifetime. Cabal's
-- data-file lookup keeps this independent of the current working directory.
requiredBundledLibrarySource :: FilePath -> String
requiredBundledLibrarySource requested = unsafePerformIO $ do
  loaded <- bundledLibrary requested
  case loaded of
    Just (_, source) -> pure source
    Nothing -> ioError (userError ("missing bundled Datra library: " <> requested))
{-# NOINLINE requiredBundledLibrarySource #-}
