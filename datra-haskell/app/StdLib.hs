{-# LANGUAGE TemplateHaskell #-}
-- | Embed the actual Datra library, so installed executables work independently
-- of their working directory. GHC tracks changes to the source file.
module StdLib (standardLibrarySource) where
import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)
standardLibrarySource :: String
standardLibrarySource = $(do
  addDependentFile "std_lib.datra"
  contents <- runIO (readFile "std_lib.datra")
  lift contents)
