module Main (main) where

import Data.Char (toLower)
import Data.Bifunctor qualified as Bifunctor
import DatraLanguage.Pretty (renderExpression)
import DatraLanguage.ConcreteSyntax (sourceLineFeed)
import DatraLanguage.Diagnostics
  ( Located (locatedValue)
  , withoutSourceSpan
  )
import DatraLanguage.Diagnostics.Application
  ( CommandLineOptionFailure (..))
import DatraLanguage.Diagnostics.Localization
  ( Locale (English, Romanian)
  , LocalizedDiagnostic
  , renderDatraError
  )
import Interpreting
  ( StandardLibraryVisibility (..)
  , interpretLocatedWithModulesAndStandardLibraryVisibility
  , parseDatraSourceSyntax
  , rewriteParsedDatraSourceWithModules
  )
import ModuleInputs (loadRequestedModules)
import Options.Applicative
import CanonicalParsing
  ( parseDatraAstLocatedWithSourceName )
import Rendering
  ( renderInterpretedValue
  )
import System.Exit (die)
import System.FilePath ((</>), takeDirectory)

data Command
  = Build Input [FilePath] FilePath FilePath Locale StandardLibraryVisibility
  | GenerateAst Input [FilePath] FilePath StandardLibraryVisibility
  | InterpretAst Input [FilePath] FilePath Locale StandardLibraryVisibility

data Input
  = InputFile FilePath
  | InlineInput String

defaultSourcePath :: FilePath
defaultSourcePath = "input.datra"

defaultAstPath :: FilePath
defaultAstPath = "output.datra.ast"

defaultOutputPath :: FilePath
defaultOutputPath = "output.datra"

defaultErrorFileName :: FilePath
defaultErrorFileName = "output.datra.error"

main :: IO ()
main = runCommand =<< customExecParser parserPreferences commandInfo

parserPreferences :: ParserPrefs
parserPreferences = prefs showHelpOnError

commandInfo :: ParserInfo Command
commandInfo =
  info
    (helper <*> commandParser)
    ( fullDesc
        <> header "datra-haskell - parse and interpret Datra"
        <> progDesc
          ( "With no subcommand, parse input.datra and write "
              <> "output.datra.ast and output.datra"
          )
    )

commandParser :: Parser Command
commandParser = commandSubparser <|> buildParser

commandSubparser :: Parser Command
commandSubparser =
  hsubparser
    ( command "ast"
        (info generateAstParser
          (progDesc "Parse Datra source and emit only its canonical AST"))
        <> command "interpret"
          (info interpretAstParser
            (progDesc "Interpret canonical Datra AST notation directly"))
        <> command "build"
          (info buildParser
            (progDesc "Generate the AST and interpret the Datra source"))
    )

buildParser :: Parser Command
buildParser =
  Build
    <$> sourceInputParser defaultSourcePath
    <*> moduleOptions
    <*> outputPathOption
      "ast-output"
      Nothing
      defaultAstPath
      "FILE"
      "Write the canonical AST to FILE; use - for stdout"
    <*> outputPathOption
      "output"
      (Just 'o')
      defaultOutputPath
      "FILE"
      "Write the interpreted value to FILE; use - for stdout"
    <*> localeOption
    <*> standardLibraryOption

generateAstParser :: Parser Command
generateAstParser =
  GenerateAst
    <$> sourceInputParser defaultSourcePath
    <*> moduleOptions
    <*> outputPathOption
      "output"
      (Just 'o')
      defaultAstPath
      "FILE"
      "Write the canonical AST to FILE; use - for stdout"
    <*> standardLibraryOption

interpretAstParser :: Parser Command
interpretAstParser =
  InterpretAst
    <$> astInputParser defaultAstPath
    <*> moduleOptions
    <*> outputPathOption
      "output"
      (Just 'o')
      defaultOutputPath
      "FILE"
      "Write the interpreted value to FILE; use - for stdout"
    <*> localeOption
    <*> standardLibraryOption

standardLibraryOption :: Parser StandardLibraryVisibility
standardLibraryOption =
  flag' NoStandardLibrary
    ( long "no-std"
        <> help "Do not provide Std to the root program"
    )
  <|> flag AllStandardLibrary QualifiedStandardLibrary
      ( long "qualified-std"
          <> help "Expose Std without opening its names or syntax"
      )

moduleOptions :: Parser [FilePath]
moduleOptions = many (strOption
  ( long "module"
      <> metavar "MODULE"
      <> help "Provide MODULE as a qualified module; may be repeated"
  ))

sourceInputParser :: FilePath -> Parser Input
sourceInputParser defaultPath =
  InlineInput
    <$> strOption
      ( long "source"
          <> metavar "DATRA"
          <> help "Read Datra source directly from this argument"
      )
    <|> fileInputParser defaultPath "Datra source"

astInputParser :: FilePath -> Parser Input
astInputParser defaultPath =
  InlineInput
    <$> strOption
      ( long "ast"
          <> metavar "AST"
          <> help "Read canonical Datra AST notation from this argument"
      )
    <|> fileInputParser defaultPath "canonical Datra AST"

fileInputParser :: FilePath -> String -> Parser Input
fileInputParser defaultPath inputDescription =
  InputFile
    <$> strOption
      ( long "input"
          <> short 'i'
          <> metavar "FILE"
          <> value defaultPath
          <> showDefault
          <> help ("Read " <> inputDescription <> " from FILE; use - for stdin")
      )

outputPathOption
  :: String
  -> Maybe Char
  -> FilePath
  -> String
  -> String
  -> Parser FilePath
outputPathOption longName shortName defaultPath meta description =
  strOption
    ( long longName
        <> foldMap short shortName
        <> metavar meta
        <> value defaultPath
        <> showDefault
        <> help description
    )

localeOption :: Parser Locale
localeOption =
  option localeReader
    ( long "locale"
        <> metavar "LOCALE"
        <> value English
        <> showDefaultWith localeName
        <> help "Diagnostic locale: english or romanian"
    )

localeReader :: ReadM Locale
localeReader = eitherReader $ \localeText ->
  Bifunctor.first renderCommandLineOptionFailure
    (parseLocaleOption localeText)

parseLocaleOption
  :: String
  -> Either CommandLineOptionFailure Locale
parseLocaleOption localeText =
  case map toLower localeText of
    "en" -> Right English
    "english" -> Right English
    "ro" -> Right Romanian
    "romana" -> Right Romanian
    "romanian" -> Right Romanian
    _ -> Left (UnsupportedDiagnosticLocale localeText)

localeName :: Locale -> String
localeName English = "english"
localeName Romanian = "romanian"

renderCommandLineOptionFailure :: CommandLineOptionFailure -> String
renderCommandLineOptionFailure =
  renderDatraError English . withoutSourceSpan

runCommand :: Command -> IO ()
runCommand commandValue =
  case commandValue of
    Build input modulePaths astPath outputPath locale
        standardLibraryVisibility -> do
      let errorPath = errorPathFor input [outputPath, astPath]
      (sourceName, source) <- readInput input
      modules <- loadRequestedModules sourceName modulePaths
        >>= diagnosticOrFail locale errorPath
      parsed <- diagnosticOrFail locale errorPath
        (parseDatraSourceSyntax standardLibraryVisibility sourceName source)
      locatedExpression <-
        diagnosticOrFail locale errorPath
          (rewriteParsedDatraSourceWithModules modules parsed)
      writeOutput astPath
        (renderExpression (locatedValue locatedExpression))
      interpreted <- either (failWithOutput errorPath . renderDatraError locale) pure
        (interpretLocatedWithModulesAndStandardLibraryVisibility
          standardLibraryVisibility modules locatedExpression)
      writeOutput outputPath (renderInterpretedValue interpreted)
    GenerateAst input modulePaths outputPath standardLibraryVisibility -> do
      let errorPath = errorPathFor input [outputPath]
      (sourceName, source) <- readInput input
      modules <- loadRequestedModules sourceName modulePaths
        >>= diagnosticOrFail English errorPath
      parsed <- diagnosticOrFail English errorPath
        (parseDatraSourceSyntax standardLibraryVisibility sourceName source)
      locatedExpression <-
        diagnosticOrFail English errorPath
          (rewriteParsedDatraSourceWithModules modules parsed)
      writeOutput outputPath
        (renderExpression (locatedValue locatedExpression))
    InterpretAst input modulePaths outputPath locale
        standardLibraryVisibility -> do
      let errorPath = errorPathFor input [outputPath]
      (sourceName, source) <- readInput input
      locatedExpression <-
        diagnosticOrFail locale errorPath
          (parseDatraAstLocatedWithSourceName sourceName source)
      modules <- loadRequestedModules sourceName modulePaths
        >>= diagnosticOrFail locale errorPath
      interpreted <- either (failWithOutput errorPath . renderDatraError locale) pure
        (interpretLocatedWithModulesAndStandardLibraryVisibility
          standardLibraryVisibility modules locatedExpression)
      writeOutput outputPath (renderInterpretedValue interpreted)

errorPathFor :: Input -> [FilePath] -> FilePath
errorPathFor input outputPaths =
  takeDirectory companionPath </> defaultErrorFileName
  where
    companionPath =
      case filter (/= "-") outputPaths of
        outputPath : _ -> outputPath
        [] ->
          case input of
            InputFile path | path /= "-" -> path
            _ -> defaultOutputPath

diagnosticOrFail
  :: LocalizedDiagnostic failure
  => Locale
  -> FilePath
  -> Either failure value
  -> IO value
diagnosticOrFail locale errorPath =
  either
    (failWithOutput errorPath
      . renderDatraError locale
      . withoutSourceSpan)
    pure

failWithOutput :: FilePath -> String -> IO value
failWithOutput errorPath rendered = do
  writeOutput errorPath rendered
  die rendered

readInput :: Input -> IO (FilePath, String)
readInput (InlineInput source) = pure ("<command-line>", source)
readInput (InputFile "-") = do
  source <- getContents
  pure ("<stdin>", source)
readInput (InputFile path) = do
  source <- readFile path
  pure (path, source)

writeOutput :: FilePath -> String -> IO ()
writeOutput "-" rendered = putStrLn rendered
writeOutput path rendered = writeFile path (rendered <> sourceLineFeed)
