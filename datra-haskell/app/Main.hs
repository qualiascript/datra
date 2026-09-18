module Main (main) where

import Datra.AST (renderExpression)
import Datra.Parsing (parseDatra)

main :: IO ()
main = do
  source <- readFile "input.datra"
  case parseDatra source of
    Left message -> ioError (userError message)
    Right expression ->
      writeFile "output.datra.ast" (renderExpression expression <> "\n")
