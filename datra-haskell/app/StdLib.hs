{-# LANGUAGE TemplateHaskell #-}
-- | The singular identity and embedded source of Datra's standard library.
-- GHC tracks changes to the source file, while the executable remains
-- independent of its working directory.
module StdLib
  ( standardLibraryIdentity
  , standardLibraryFileName
  , standardLibraryNamespace
  , standardLibrarySource
  , isStandardLibraryRequest
  ) where
import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)

standardLibraryIdentity :: String
standardLibraryIdentity = "std_lib"

standardLibraryFileName :: FilePath
standardLibraryFileName = "std_lib.datra"

standardLibraryNamespace :: String
standardLibraryNamespace = "StdLib"

isStandardLibraryRequest :: FilePath -> Bool
isStandardLibraryRequest requested =
  requested == standardLibraryIdentity
    || requested == standardLibraryFileName

standardLibrarySource :: String
standardLibrarySource = $(do
  addDependentFile "std_lib.datra"
  contents <- runIO (readFile "std_lib.datra")
  lift contents)
