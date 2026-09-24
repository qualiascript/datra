module Main (main) where

import Data.Char (toLower)
import Data.Bifunctor qualified as Bifunctor
import DatraLanguage.AST (renderExpression)
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
  ( EvaluationMode (DevelopmentMode, ProductionMode)
  , interpretLocatedWithImportsInMode
  )
import ModuleLoading (loadImports, loadExpressionImports, importSyntax)
import Options.Applicative
import Parsing
  ( parseDatraAstLocatedWithSourceName
  , parseDatraLocatedWithSyntaxImports
  )
import Rendering
  ( renderInterpretedValue
  )
import System.Exit (die)
import System.FilePath ((</>), takeDirectory)

data Command
  = Build Input FilePath FilePath Locale EvaluationMode
  | GenerateAst Input FilePath
  | InterpretAst Input FilePath Locale EvaluationMode

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
    <*> modeOption

generateAstParser :: Parser Command
generateAstParser =
  GenerateAst
    <$> sourceInputParser defaultSourcePath
    <*> outputPathOption
      "output"
      (Just 'o')
      defaultAstPath
      "FILE"
      "Write the canonical AST to FILE; use - for stdout"

interpretAstParser :: Parser Command
interpretAstParser =
  InterpretAst
    <$> astInputParser defaultAstPath
    <*> outputPathOption
      "output"
      (Just 'o')
      defaultOutputPath
      "FILE"
      "Write the interpreted value to FILE; use - for stdout"
    <*> localeOption
    <*> modeOption

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

modeOption :: Parser EvaluationMode
modeOption =
  option modeReader
    ( long "mode"
        <> metavar "MODE"
        <> value DevelopmentMode
        <> showDefaultWith modeName
        <> help "Assertion mode: dev or prod"
    )

modeReader :: ReadM EvaluationMode
modeReader = eitherReader $ \modeText ->
  Bifunctor.first renderCommandLineOptionFailure
    (parseModeOption modeText)

parseModeOption
  :: String
  -> Either CommandLineOptionFailure EvaluationMode
parseModeOption modeText =
  case map toLower modeText of
    "dev" -> Right DevelopmentMode
    "development" -> Right DevelopmentMode
    "prod" -> Right ProductionMode
    "production" -> Right ProductionMode
    _ -> Left (UnsupportedEvaluationMode modeText)

renderCommandLineOptionFailure :: CommandLineOptionFailure -> String
renderCommandLineOptionFailure =
  renderDatraError English . withoutSourceSpan

modeName :: EvaluationMode -> String
modeName DevelopmentMode = "dev"
modeName ProductionMode = "prod"

runCommand :: Command -> IO ()
runCommand commandValue =
  case commandValue of
    Build input astPath outputPath locale mode -> do
      let errorPath = errorPathFor input [outputPath, astPath]
      (sourceName, source) <- readInput input
      imports <- loadImports sourceName source
        >>= diagnosticOrFail locale errorPath
      locatedExpression <-
        diagnosticOrFail locale errorPath
          (parseDatraLocatedWithSyntaxImports (importSyntax imports) sourceName source)
      writeOutput astPath
        (renderExpression (locatedValue locatedExpression))
      interpreted <- either (failWithOutput errorPath . renderDatraError locale) pure
        (interpretLocatedWithImportsInMode mode imports locatedExpression)
      writeOutput outputPath (renderInterpretedValue interpreted)
    GenerateAst input outputPath -> do
      let errorPath = errorPathFor input [outputPath]
      (sourceName, source) <- readInput input
      imports <- loadImports sourceName source
        >>= diagnosticOrFail English errorPath
      locatedExpression <-
        diagnosticOrFail English errorPath
          (parseDatraLocatedWithSyntaxImports (importSyntax imports) sourceName source)
      writeOutput outputPath
        (renderExpression (locatedValue locatedExpression))
    InterpretAst input outputPath locale mode -> do
      let errorPath = errorPathFor input [outputPath]
      (sourceName, source) <- readInput input
      locatedExpression <-
        diagnosticOrFail locale errorPath
          (parseDatraAstLocatedWithSourceName sourceName source)
      imports <- loadExpressionImports sourceName (locatedValue locatedExpression)
        >>= diagnosticOrFail locale errorPath
      interpreted <- either (failWithOutput errorPath . renderDatraError locale) pure
        (interpretLocatedWithImportsInMode mode imports locatedExpression)
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
writeOutput path rendered = writeFile path (rendered <> "\n")
