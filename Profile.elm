module Main where

import IO.IO (..)

import BigInt as I

-- With schoolboy method, <1s
multProf _ = I.multiply (I.fromString "12304987123") (I.fromString "1230981")

-- With repeated subtraction, ~30s
quotProf _ = I.quotRem (I.fromString "10239487") (I.fromString "7")

console = putStrLn << show << multProf <| ()
