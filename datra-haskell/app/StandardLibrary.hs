{-# LANGUAGE TemplateHaskell #-}
-- | Embed the actual Datra library, so installed executables work independently
-- of their working directory. GHC tracks changes to the source file.
module StandardLibrary (standardLibrarySource) where
import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)
standardLibrarySource :: String
standardLibrarySource = $(do
  addDependentFile "standard_library.datra"
  contents <- runIO (readFile "standard_library.datra")
  lift contents)
