module Test (tests) where

import BigInt as I

import Debug
import ElmTest.Assertion (assertEqual)
import ElmTest.Test (suite, test)
import String

unsafeFromString s = case I.fromString s of
                       Err e -> Debug.crash "Test failure in fromString"
                       Ok  n -> n

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

opTest opName op arg1 arg2 ans =
  let name = String.concat [arg1, " ", opName, " ", arg2, " = ", ans]
  in test name (assertEqual (unsafeFromString ans)
                            (unsafeFromString arg1 `op` unsafeFromString arg2))

addTest = opTest "+" I.add

additionTests = [
    addTest "100" "1" "101"
  , addTest "1" "100" "101"
  , addTest "99" "1" "100"
  , addTest "1" "99" "100"
  ]

subtractionTests = []

multTest = opTest "*" I.multiply
multiplicationTests = [
    multTest "3" "1" "3"
  , multTest "3" "2" "6"
  , multTest "943" "-4546" "-4286878"
  ]

divTest num denom quot rem =
  let name = num ++ " ÷ " ++ denom ++ " = " ++ quot ++ " rem " ++ rem
  in test name  (assertEqual (unsafeFromString quot, unsafeFromString rem) 
                             (I.quotRem (unsafeFromString num) (unsafeFromString denom)))

divisionTests = [
    divTest "10" "3" "3" "1" 
  , divTest "600" "6" "100" "0"
  , divTest "8890" "70" "127" "0"
  , divTest "8890" "127" "70" "0"
  , divTest "-4286858" "943" "-4546" "20"
  , divTest "-4286858" "-4546" "943" "20"
  ]

comparisonTests = []

squareRootTests = []
