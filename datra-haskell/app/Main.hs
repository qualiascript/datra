module Main where

import qualified DatraHaskell (datraHaskellFunc)

main :: IO ()
main = do
  putStrLn "Hello, Datra from main.hs!"
  DatraHaskell.datraHaskellFunc
