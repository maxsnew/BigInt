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

multiplicationTests = [
    (I.fromString "3") `equals` ((I.fromString "3") `I.multiply` (I.fromString "1"))
  , I.fromString "6" `equals` (I.fromString "3" `I.multiply` I.fromString "2")
  , I.fromString "-4286878" `equals` (I.fromString "943" `I.multiply` I.fromString "-4546")
  ]

divisionTests = [
    (I.fromString "3",    I.one) `equals` (I.quotRem (I.fromString "10") (I.fromString "3"))
  , (I.fromString "100", I.zero) `equals` (I.quotRem (I.fromString "600") (I.fromString "6"))
  , (I.fromString "127", I.zero) `equals` (I.quotRem (I.fromString "8890") (I.fromString "70"))
  , (I.fromString "70", I.zero) `equals` (I.quotRem (I.fromString "8890") (I.fromString "127"))
  , (I.fromString "-4546", I.fromString "20") `equals` (I.quotRem (I.fromString "-4286858") (I.fromString "943"))
  , (I.fromString "943", I.fromString "20") `equals` (I.quotRem (I.fromString "-4286858") (I.fromString "-4546"))
  ]

comparisonTests = []

squareRootTests = []

console = runDisplay tests
