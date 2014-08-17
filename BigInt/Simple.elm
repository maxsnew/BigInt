module BigInt.Simple where

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
        let shortened = dropWhile ((==) 0) is
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
                       , ('9', 9)]

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

add : BigInt -> BigInt -> BigInt
add m n = case (m, n) of
  (Zero, _) -> n
  (_, Zero) -> m
  (Positive ds1, Positive ds2) -> Positive (addDigits ds1 ds2)
  (Negative ds1, Negative ds2) -> Negative (addDigits ds1 ds2)
  (Positive pos, Negative neg) -> subtractDigits pos neg
  (Negative neg, Positive pos) -> subtractDigits pos neg

-- | Addition of natural numbers
addDigits : Digits -> Digits -> Digits
addDigits ds1 ds2 = [1]

-- | TODO
subtractDigits : Digits -> Digits -> BigInt
subtractDigits pos neg = Zero

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

compareDigits : Digits -> Digits -> Order
compareDigits ds1 ds2 = case Basics.compare (length ds1) (length ds2) of
  EQ  -> fstDiff . reverse <| zipWith Basics.compare ds1 ds2
  ord -> ord

fstDiff : [Order] -> Order
fstDiff ords = case dropWhile ((==) EQ) ords of
  []     -> EQ
  ord::_ -> ord
