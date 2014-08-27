module Main where

import IO.IO (..)

import BigInt as I

console = putStrLn << show <| I.quotRem (I.fromString "10239487") (I.fromString "7")
