module BigInt where

import Basics
import Dict (Dict)
import Dict
import Either (Either(..), either)
import List
import Native.Error
import String

import BigInt.Err ((<=<))
import BigInt.Err as Err

data BigInt = Positive Digits
            | Negative Digits
            | Zero

-- Invariants: non-empty, most significant digit is non-zero
-- Interpretation: a backwards number, i.e., 1024 is represented as [4,2,0,1]
type Digits = [Digit]

-- A decimal digit, invariant: 0-9
type Digit  = Int

fromString : String -> BigInt
fromString = either Native.Error.raise id . safeFromString

safeFromString : String -> Either String BigInt
safeFromString =
  let getSign : [Char] -> Either String (Bool, [Char]) -- ^ True for Positive
      getSign cs = case cs of
        [] -> Left "Empty String is invalid Integer"
        '-'::c::more -> Right (False, c::more)
        c::more      -> Right (True, cs)

      readDigit c = Dict.get c digits
      
      readDigits : (Bool, [Char]) -> Either String (Bool, [Int])
      readDigits (b, cs) = Err.map ((,) b) . Err.forEach cs <| \c ->
        case readDigit c of
          Nothing -> Left (String.cons c " is not a digit.")
          Just  d -> Right d

      interpret : (Bool, [Int]) -> BigInt
      interpret (b, is) = 
        let shortened = dropZeros is
            ctor b = if b then Positive else Negative
              
        in if List.isEmpty shortened
           then Zero
           else ctor b (reverse shortened)

  in Err.map interpret . (readDigits <=< getSign) . String.toList

digits : Dict Char Int
digits = Dict.fromList [ ('0', 0)
                       , ('1', 1)
                       , ('2', 2)
                       , ('3', 3)
                       , ('4', 4)
                       , ('5', 5)
                       , ('6', 6)
                       , ('7', 7)
                       , ('8', 8)
                       , ('9', 9) ]

toString : BigInt -> String
toString i = 
  let digitString = String.join "" . map show . reverse
  in case i of
    Zero        -> "0"
    Positive ds -> digitString ds
    Negative ds -> String.cons '-' . digitString <| ds

dropWhile : (a -> Bool) -> [a] -> [a]
dropWhile p =
  let loop xs = case xs of
    [] -> []
    x::xs' -> if p x
              then loop xs'
              else xs
  in loop

zero : BigInt
zero = Zero

negate : BigInt -> BigInt
negate i = case i of
  Zero -> Zero
  Positive ds -> Negative ds
  Negative ds -> Positive ds

-- Addition and Subtraction
add : BigInt -> BigInt -> BigInt
add m n = case (m, n) of
  (Zero, _) -> n
  (_, Zero) -> m
  (Positive ds1, Positive ds2) -> Positive (addDigits ds1 ds2)
  (Negative ds1, Negative ds2) -> Negative (addDigits ds1 ds2)
  (Positive pos, Negative neg) -> subtractDigits pos neg
  (Negative neg, Positive pos) -> subtractDigits pos neg


quotRem10 : Int -> (Int, Int)
quotRem10 s = (s `div` 10, s `mod` 10)

-- | Addition of natural numbers
addDigits : Digits -> Digits -> Digits
addDigits ds1 ds2 = 
  let pushCarry carry acc = if carry == 0 then acc else carry :: acc
      go acc carry ds1 ds2 = case (ds1, ds2) of
        ([], [])             -> pushCarry carry acc
        ([], d::ds)          -> goWith acc (d + carry) ds
        (d::ds, [])          -> goOne acc (carry + d) ds
        (d1::ds1', d2::ds2') -> let (carry', d) = quotRem10 <| d1 + d2 + carry
                                in go (d::acc) carry' ds1' ds2'
      goWith acc c' ds = let (carry, d) = quotRem10 <| c'
                         in goOne (d::acc) carry ds

      goOne acc carry ds = case ds of
        [] -> pushCarry carry acc
        (d :: ds') -> let (carry', d') = quotRem10 <| d + carry
                      in goOne (d'::acc) carry' ds'
  in reverse <| go [] 0 ds1 ds2

-- | TODO
subtractDigits : Digits -> Digits -> BigInt
subtractDigits pos neg =
  case compareDigits pos neg of
    EQ -> Zero
    LT -> Negative (subtractFromGreater neg pos)
    GT -> Positive (subtractFromGreater pos neg)

-- First argument is assumed to be larger
subtractFromGreater : Digits -> Digits -> Digits
subtractFromGreater minuend subtrahend =
  let go minuend subtrahend carry diffAcc = case (minuend, subtrahend) of
        ([], _) -> diffAcc
        (_, []) -> carryOut minuend carry diffAcc
        (m::ms, s::ss) ->
        let newM = m - carry
            (newM', newCarry) = if newM < s
                                then (newM + 10, 1)
                                else (newM, 0)
        in go ms ss newCarry (newM' - s :: diffAcc)
      carryOut minuend carry diffAcc = case minuend of
        []   -> diffAcc
        m::ms -> let newM = m - carry
                     (newM', newCarry) = if newM < 0
                                         then (newM + 10, 1)
                                         else (newM, 0)
                 in carryOut ms newCarry (newM' :: diffAcc)
  in reverse . dropZeros <| go minuend subtrahend 0 []

subtract : BigInt -> BigInt -> BigInt
subtract m n = add m (negate n)

compare : BigInt -> BigInt -> Order
compare m n = case (m, n) of
  (Zero, Zero) -> EQ
  (Zero, Positive _) -> LT
  (Zero, Negative _) -> GT
  (Positive _, Zero) -> GT
  (Negative _, Zero) -> LT
  (Positive _, Negative _) -> GT
  (Negative _, Positive _) -> LT
  (Positive ds1, Positive ds2) -> compareDigits ds1 ds2
  (Negative ds1, Negative ds2) -> compareDigits ds2 ds1

-- Multiplication and Division
multiply : BigInt -> BigInt -> BigInt
multiply m n = case (m, n) of
  (Zero, _) -> Zero
  (_, Zero) -> Zero
  (Positive ds1, Positive ds2) -> Positive (multDigits ds1 ds2)
  (Positive ds1, Negative ds2) -> Negative (multDigits ds1 ds2)
  (Negative ds1, Positive ds2) -> Negative (multDigits ds1 ds2)
  (Negative ds1, Negative ds2) -> Positive (multDigits ds1 ds2)

multDigits : Digits -> Digits -> Digits
multDigits ds1 ds2 = Native.Error.raise "Not implemented: multiplication"

-- Quotient and remainder
quotRem : BigInt -> BigInt -> (BigInt, BigInt)
quotRem m n = case (m, n) of
  (_, Zero) -> Native.Error.raise "Error, quotRem: can't divide by zero"
  (Zero, _) -> (Zero, Zero)
  (Positive ds1, Positive ds2) -> positively (longDivide ds1 ds2)
  (Positive ds1, Negative ds2) -> negatively (longDivide ds1 ds2)
  (Negative ds1, Positive ds2) -> negatively (longDivide ds1 ds2)
  (Negative ds1, Negative ds2) -> positively (longDivide ds1 ds2)

positively (m, n) = (Positive m, n)
negatively (m, n) = (Negative m, n)

longDivide : Digits -> Digits -> (Digits, BigInt)
longDivide ds1 ds2 = Native.Error.raise "Not implemented: division"

-- Comparison
compareDigits : Digits -> Digits -> Order
compareDigits ds1 ds2 = case Basics.compare (length ds1) (length ds2) of
  EQ  -> fstDiff . reverse <| zipWith Basics.compare ds1 ds2
  ord -> ord

fstDiff : [Order] -> Order
fstDiff ords = case dropWhile ((==) EQ) ords of
  []     -> EQ
  ord::_ -> ord

dropZeros : [Int] -> [Int]
dropZeros = dropWhile ((==) 0)
