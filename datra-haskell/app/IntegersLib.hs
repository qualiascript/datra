{-# LANGUAGE TemplateHaskell #-}

-- | Embedded source for the optional integer helpers library.
module IntegersLib
  ( integersLibraryIdentity
  , integersLibraryFileName
  , integersLibrarySource
  , isIntegersLibraryRequest
  ) where

import Language.Haskell.TH.Syntax (addDependentFile, lift, runIO)

integersLibraryIdentity :: String
integersLibraryIdentity = "integers"

integersLibraryFileName :: FilePath
integersLibraryFileName = "integers.datra"

isIntegersLibraryRequest :: FilePath -> Bool
isIntegersLibraryRequest requested =
  requested == integersLibraryIdentity
    || requested == integersLibraryFileName
    || requested == "lib/" <> integersLibraryFileName

-- Keep this module as the sole packaging boundary; max/min and their recursive
-- helpers remain ordinary Datra source and never become runtime externals.
integersLibrarySource :: String
integersLibrarySource = $(do
  addDependentFile "lib/integers.datra"
  contents <- runIO (readFile "lib/integers.datra")
  lift contents)
