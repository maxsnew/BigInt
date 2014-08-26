module Main where

import BigInt as I

import ElmTest.Runner.Console (runDisplay)
import ElmTest.Test (..)

tests = suite "BigInt tests" [
          suite "From String tests" fromStringTests
        , suite "To String tests" toStringTests
        , suite "Addition tests" additionTests
        , suite "Subtraction tests" subtractionTests
        , suite "Multiplication tests" multiplicationTests
        , suite "Division tests" divisionTests
        , suite "Comparison tests" comparisonTests
        , suite "Square Root tests" squareRootTests
        ]

fromStringTests = []

toStringTests = []

additionTests = [ 
    I.fromString "101" `equals` (I.add (I.fromString "100") I.one)
  , I.fromString "101" `equals` (I.add I.one (I.fromString "100"))
  , I.fromString "100" `equals` (I.add (I.fromString "99") I.one)
  , I.fromString "100" `equals` (I.add (I.fromString "99") I.one)
  ]

subtractionTests = []

multiplicationTests = []

divisionTests = []

comparisonTests = []

squareRootTests = []

console = runDisplay tests
