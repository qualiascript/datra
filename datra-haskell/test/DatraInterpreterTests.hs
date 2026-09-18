module DatraInterpreterTests (main) where

import Main (interpretDatra)

main :: IO ()
main = do
  assertInterpretation
    "flat map"
    "[1; 2; 10]"
    "1 <:> 2 <:> 10"
  assertInterpretation
    "nested map"
    "[[1; 2];[3;4]]"
    "1 <:> 2 <+> 3 <:> 4"
  assertInterpretation
    "comments and whitespace"
    "  [1; # retain the next value\n [2; 3]] # end\n"
    "1 <+> 2 <:> 3"
  assertInterpretation
    "empty nested maps are trimmed recursively"
    "[1; [[ ]  ]; 2]"
    "1 <:> 2"
  assertInterpretation
    "expansions are parenthesized at recursive depth"
    "[[[1;2];[3;4]];[5;6]]"
    "(1 <:> 2 <+> 3 <:> 4) <+> 5 <:> 6"
  assertInterpretation
    "the empty map is retained at the root"
    "[]"
    "[]"
  assertRejected "top-level expression must be a map" "10"
  assertInterpretation
    "trailing semicolons are ignored"
    "[1; 2; # trailing separators\n ; ; ]"
    "1 <:> 2"
  assertRejected "empty entries in the middle are rejected" "[1;;2]"

assertInterpretation :: String -> String -> String -> IO ()
assertInterpretation label source expected =
  case interpretDatra source of
    Left message -> fail (label <> ": unexpected parse failure: " <> message)
    Right actual
      | actual == expected -> pure ()
      | otherwise ->
          fail
            ( label
                <> ": expected "
                <> show expected
                <> ", got "
                <> show actual
            )

assertRejected :: String -> String -> IO ()
assertRejected label source =
  case interpretDatra source of
    Left _ -> pure ()
    Right actual ->
      fail (label <> ": unexpectedly interpreted as " <> show actual)
