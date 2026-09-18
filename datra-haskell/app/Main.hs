module Main (main) where

import Datra.AST (renderExpression)
import Datra.Parsing (parseDatraWithSourceName)

main :: IO ()
main = do
  let inputPath = "resources/input.datra"
  source <- readFile inputPath
  case parseDatraWithSourceName inputPath source of
    Left message -> ioError (userError message)
    Right expression ->
      writeFile
        "resources/output.datra.ast"
        (renderExpression expression <> "\n")
