{-# LANGUAGE TemplateHaskell #-}
-- | The singular identity and embedded source of Datra's standard library.
-- GHC tracks changes to the source file, while the executable remains
-- independent of its working directory.
module StdLib
  ( standardLibraryIdentity
  , standardLibraryFileName
  , standardLibrarySource
  , isStandardLibraryRequest
  ) where
import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)

standardLibraryIdentity :: String
standardLibraryIdentity = "std"

standardLibraryFileName :: FilePath
standardLibraryFileName = "std.datra"

isStandardLibraryRequest :: FilePath -> Bool
isStandardLibraryRequest requested =
  requested == standardLibraryIdentity
    || requested == standardLibraryFileName
    || requested == "lib/" <> standardLibraryFileName

standardLibrarySource :: String
standardLibrarySource = $(do
  addDependentFile "lib/std.datra"
  contents <- runIO (readFile "lib/std.datra")
  lift contents)
