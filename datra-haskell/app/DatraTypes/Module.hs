module DatraTypes.Module
  ( PreparedModule (..)
  , PreparedModules (..)
  , emptyPreparedModules
  , preparedModuleSources
  , preparedModuleContains
  , preparedModuleNamespaceOrigins
  , StandardLibraryVisibility (..)
  , ModuleMemberPresentation (..)
  , ModuleExport (..)
  , LoadedModuleDeclaration (..)
  , LoadedModuleResult (..)
  , moduleExportName
  ) where

import DatraTypes (InterpretedValue)
import DatraTypes.Module.Source (ModuleSource)
import DatraTypes.Scope (Scope)
import StringInterpolation (SyntaxRule)

data PreparedModule = PreparedModule
  { preparedModuleSource :: ModuleSource
  , preparedModuleResult :: LoadedModuleResult
  -- OBSOLETE: syntax rules must be derived from the installed module's
  -- dependent declaration layers.  This parallel catalog remains only until
  -- SyntaxContext is replaced by Scope in the rewriting stack.
  , preparedModuleRuleSets :: [(String, [SyntaxRule])]
  }

newtype PreparedModules = PreparedModules [PreparedModule]

emptyPreparedModules :: PreparedModules
emptyPreparedModules = PreparedModules []

preparedModuleSources :: PreparedModules -> [(String, ModuleSource)]
preparedModuleSources (PreparedModules modules) =
  [ (loadedModuleIdentity (preparedModuleResult prepared),
      preparedModuleSource prepared)
  | prepared <- modules
  ]

preparedModuleContains :: FilePath -> PreparedModules -> Bool
preparedModuleContains identity (PreparedModules modules) = any
  ((== identity) . loadedModuleIdentity . preparedModuleResult)
  modules

preparedModuleNamespaceOrigins :: PreparedModules -> [(String, FilePath)]
preparedModuleNamespaceOrigins (PreparedModules modules) =
  [ (loadedModuleDeclarationName declaration,
      loadedModuleIdentity (preparedModuleResult prepared))
  | prepared <- modules
  , declaration <- loadedModuleDeclarations (preparedModuleResult prepared)
  ]

data StandardLibraryVisibility
  = NoStandardLibrary
  | QualifiedStandardLibrary
  | AllStandardLibrary
  deriving (Eq, Show)

data ModuleMemberPresentation
  = TransparentModuleMemberPresentation
  | CanonicalModuleMemberPresentation

data ModuleExport = ModuleExport
  String ModuleMemberPresentation Bool InterpretedValue

data LoadedModuleDeclaration = LoadedModuleDeclaration
  { loadedModuleDeclarationName :: String
  , loadedModuleDeclarationPresentation :: ModuleMemberPresentation
  , loadedModuleDeclarationIsDefinition :: Bool
  , loadedModuleDeclarationValue :: InterpretedValue
  , loadedModuleDeclarationScope :: Scope
  }

data LoadedModuleResult = LoadedModuleResult
  { loadedModuleIdentity :: FilePath
  , loadedModuleFederation :: InterpretedValue
  , loadedModuleDeclarations :: [LoadedModuleDeclaration]
  }

moduleExportName :: ModuleExport -> String
moduleExportName (ModuleExport name _ _ _) = name
