-- | Resolve imports relative to the importing file, detect cycles, and retain
-- each module's own dependency context. The standard library is embedded.
module ModuleLoading (loadImports, loadExpressionImports, importSyntax) where
import Control.Exception (IOException, try)
import System.Directory (canonicalizePath)
import System.FilePath ((</>), takeDirectory, takeExtension)
import Interpreting (ModuleSource (..), moduleExportNames)
import Parsing (sourceImports, parseDatraLocatedWithSyntaxImports)
import DatraLanguage.AST
import DatraLanguage.Diagnostics (Located (locatedValue))
import SyntaxDefinitions
import ModuleNames (isPrivateIdentifier)

loadImports :: FilePath -> String -> IO (Either String [(String, ModuleSource)])
loadImports origin source = case sourceImports source of
  Left message -> pure (Left message)
  Right paths -> loadPaths [] origin paths

-- Canonical AST imports must be read structurally: their string spelling may
-- be compact, and source text inside a string is not another import.
loadExpressionImports :: FilePath -> Expression -> IO (Either String [(String, ModuleSource)])
loadExpressionImports origin = loadPaths [] origin . paths
  where
    paths (Import _ path) = [path]
    paths value = concatMap paths (expressionChildren value)

loadPaths :: [FilePath] -> FilePath -> [String] -> IO (Either String [(String, ModuleSource)])
loadPaths ancestors origin = fmap sequence . traverse (load ancestors origin)
  where
    go visiting parent contents = case sourceImports contents of
      Left message -> pure (Left message)
      Right paths -> loadPaths visiting parent paths
    load visiting parent requested
      | requested `elem` ["std_lib", "std_lib.datra"] =
          pure (Right (requested, StdLibModule))
      | otherwise = do
          let filename = if null (takeExtension requested) then requested <> ".datra" else requested
              location = takeDirectory parent </> filename
          resolved <- try (canonicalizePath location) :: IO (Either IOException FilePath)
          case resolved of
            Left exception -> pure (Left (show exception))
            Right path | path `elem` visiting -> pure (Left ("cyclic import: " <> path))
            Right path -> do
              loaded <- try (readFile path >>= \text -> length text `seq` pure text) :: IO (Either IOException String)
              case loaded of
                Left exception -> pure (Left ("cannot import " <> requested <> ": " <> show exception))
                Right text -> do
                  dependencies <- go (path:visiting) path text
                  pure $ do
                    imports <- dependencies
                    expression <- locatedValue <$> parseDatraLocatedWithSyntaxImports (importSyntax imports) path text
                    pure (requested, ModuleSource path expression imports)


importSyntax :: [(String, ModuleSource)] -> [(String, [SyntaxRule])]
importSyntax = map (\(path, source) -> (path,
  [rule { syntaxModule = Just path }
  | Right exported <- [moduleExportNames source]
  , declaration <- declarations source, rule <- declarationRules declaration
  , not (isPrivateIdentifier (syntaxName rule)), syntaxName rule `elem` exported]))
  where
    declarations (ModuleSource _ (Program entries _) _) = entries
    declarations (ModuleSource _ (Begin entries _) _) = entries
    declarations _ = []
