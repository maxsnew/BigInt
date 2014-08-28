module Main where

import IO.IO (..)

import BigInt as I

-- With schoolboy method, <1s
multProf _ = I.multiply (I.fromString "12304987123") (I.fromString "1230981")

-- With repeated subtraction, <1s
quotProf _ = I.quotRem (I.fromString "1023948700") (I.fromString "7123")

console = putStrLn << show << quotProf <| ()
