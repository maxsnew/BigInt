module BigInt where

import Basics
import Dict (Dict)
import Dict
import Either (Either(..), either)
import List
import Native.Error
import String
import Trampoline (Trampoline(Continue, Done), trampoline)

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


startFuel = 2
-- Can fail if the int is not an integer
fromInt : Int -> BigInt
fromInt i = if not (i >= minInt && i <= maxInt)
            then Native.Error.raise (show i ++ " is not an exact integer")
            else (fromString << show) i

maxInt : Int
maxInt = 9007199254740992
minInt : Int
minInt = -9007199254740992

maxBInt : BigInt
maxBInt = fromInt maxInt
minBInt : BigInt
minBInt = fromInt minInt

toInt : BigInt -> Int
toInt b = if (b `lt` minBInt || b `gt` maxBInt)
          then Native.Error.raise (toString b ++ " is not small enough to be an exact int")
          else case b of
            Zero     -> 0
            Positive ds -> sumDigits ds
            Negative ds -> (Basics.negate << sumDigits) ds

sumDigits : Digits -> Int
sumDigits = List.sum << List.indexedMap (\i d -> 10 ^ i * d)

fromString : String -> BigInt
fromString = either Native.Error.raise Basics.identity << safeFromString

safeFromString : String -> Either String BigInt
safeFromString =
  let getSign : [Char] -> Either String (Bool, [Char]) -- ^ True for Positive
      getSign cs = case cs of
        [] -> Left "Empty String is invalid Integer"
        '-'::c::more -> Right (False, c::more)
        c::more      -> Right (True, cs)

      readDigit c = Dict.get c digits
      
      readDigits : (Bool, [Char]) -> Either String (Bool, [Int])
      readDigits (b, cs) = Err.map ((,) b) << Err.forEach cs <| \c ->
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

  in Err.map interpret << (readDigits <=< getSign) << String.toList

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
  let digitString = String.join "" << map show << reverse
  in case i of
    Zero        -> "0"
    Positive ds -> digitString ds
    Negative ds -> String.cons '-' << digitString <| ds

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

inc : BigInt -> BigInt
inc = add one

dec : BigInt -> BigInt
dec m = subtract m one

quotRem10 : Int -> (Int, Int)
quotRem10 s = (s // 10, s % 10)

-- | Addition of natural numbers
addDigits : Digits -> Digits -> Digits
addDigits ds1 ds2 = 
  let pushCarry carry acc = Done <| if carry == 0 then acc else carry :: acc
      go fuel acc carry ds1 ds2 = 
        if | fuel < 0  -> Continue (\_ -> go startFuel acc carry ds1 ds2)
           | otherwise -> case (ds1, ds2) of
               ([], [])             -> pushCarry carry acc
               ([], d::ds)          -> goWith acc (d + carry) ds
               (d::ds, [])          -> goWith acc (carry + d) ds
               (d1::ds1', d2::ds2') -> let (carry', d) = quotRem10 <| d1 + d2 + carry
                                       in go (fuel - 1) (d::acc) carry' ds1' ds2'

      goWith acc c' ds = let (carry, d) = quotRem10 <| c'
                         in goOne 0 (d::acc) carry ds

      goOne fuel acc carry ds = 
        if | fuel < 0  -> goOne startFuel acc carry ds
           | otherwise -> case ds of
               [] -> pushCarry carry acc
               (d :: ds') -> let (carry', d') = quotRem10 <| d + carry
                             in goOne (fuel - 1) (d'::acc) carry' ds'
  in reverse << trampoline <| go startFuel [] 0 ds1 ds2

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
  let go fuel minuend subtrahend carry diffAcc = 
        if | fuel < 0  -> Continue (\_ -> go startFuel minuend subtrahend carry diffAcc)
           | otherwise -> case (minuend, subtrahend) of
               ([], _) -> Done diffAcc
               (_, []) -> carryOut fuel minuend carry diffAcc
               (m::ms, s::ss) ->
                 let newM = m - carry
                     (newM', newCarry) = if newM < s
                                         then (newM + 10, 1)
                                         else (newM, 0)
                 in go (fuel - 1) ms ss newCarry (newM' - s :: diffAcc)
      carryOut fuel minuend carry diffAcc = 
          if | fuel < 0  -> Continue (\_ -> carryOut startFuel minuend carry diffAcc)
             | otherwise -> case minuend of
                 []    -> Done diffAcc
                 m::ms -> let newM = m - carry
                              (newM', newCarry) = if newM < 0
                                                  then (newM + 10, 1)
                                                  else (newM, 0)
                          in carryOut (fuel - 1) ms newCarry (newM' :: diffAcc)
  in reverse << dropZeros << trampoline <| go startFuel minuend subtrahend 0 []

subtract : BigInt -> BigInt -> BigInt
subtract m n = add m (negate n)

-- Multiplication and Division
multiply : BigInt -> BigInt -> BigInt
multiply m n = case (m, n) of
  (Zero, _) -> Zero
  (_, Zero) -> Zero
  (Positive ds1, Positive ds2) -> Positive (multDigits ds1 ds2)
  (Positive ds1, Negative ds2) -> Negative (multDigits ds1 ds2)
  (Negative ds1, Positive ds2) -> Negative (multDigits ds1 ds2)
  (Negative ds1, Negative ds2) -> Positive (multDigits ds1 ds2)

-- | Should not be exposed!!! Exposes implementation details!!!
leftShift : Digits -> Int -> Digits
leftShift ds n = repeat n 0 ++ ds

multDigits : Digits -> Digits -> Digits
multDigits ds1 ds2 =
  let (big, less) = case compareDigits ds1 ds2 of
        LT -> (ds2, ds1)
        _  -> (ds1, ds2)
      -- multiply a single digit by the bigger number
      go fuel digit ds carry acc =
        if | fuel < 0  -> Continue (\_ -> go startFuel digit ds carry acc)
           | otherwise ->
             case (ds, carry) of
               ([],     0) -> Done (reverse acc)
               ([],     _) -> Done (reverse (carry :: acc))
               (d::ds', _) ->
                 let (newD, newCarry) = quotRem10 (d * digit)
                 in go (fuel - 1) digit ds' newCarry (newD :: acc)
      multDigit d = trampoline (go startFuel d big 0 [])
  in foldl1 addDigits << List.indexedMap (\i d -> (multDigit d) `leftShift` i) <| less

one : BigInt
one = fromString "1"

two : BigInt
two = fromString "2"

-- Quotient and remainder
quotRem : BigInt -> BigInt -> (BigInt, BigInt)
quotRem m n = case (m, n) of
  (_, Zero) -> Native.Error.raise "Error, quotRem: can't divide by zero"
  (Zero, _) -> (Zero, Zero)
  (Positive ds1, Positive ds2) -> divideDigits ds1 ds2
  (_, Negative _) -> negatively <| quotRem m (negate n)
  (Negative _, _) -> let (q, r) = quotRem (negate m) n
                     in if isZero r
                        then (negate q, r)
                        else (subtract (negate q) one, subtract n r)

div : BigInt -> BigInt -> BigInt
div x y = fst (quotRem x y)

mod : BigInt -> BigInt -> BigInt
mod x y = snd (quotRem x y)

negatively (m, n) = (negate m, n)

-- Euclidean Division, produces quotient and remainder, as in
--    let (q, r) = longDivide a b
--    a = bq + r
divideDigits : Digits -> Digits -> (BigInt, BigInt)
divideDigits ds1 ds2 = case compareDigits ds1 ds2 of
  LT -> (zero, Positive ds1)
  EQ -> (one, zero)
  GT -> 
    let dvisor = Positive ds2
        go fuel dvend acc = 
          if | fuel < 0  -> Continue (\_ -> go startFuel dvend acc)
             | otherwise -> case compare dvend dvisor of
                 LT -> Done (acc, dvend)
                 EQ -> Done (add one acc, zero)
                 GT -> go (fuel - 1) (subtract dvend dvisor) (add one acc)
    in trampoline (go startFuel (Positive ds1) zero)

half m = fst (quotRem m two)

-- returns the floor of the sqroot
-- uses Newton's Method
flroot : BigInt -> BigInt
flroot m = case m of
  Zero         -> zero
  Negative _   -> Native.Error.raise "Can't take square root of a negative number"
  Positive [1] -> one
  Positive _ ->
    -- Newton's method using integer division
    -- x_(k+1) = 1/2 (x_k + m / x_k)
    let newton fuel prevGuess curGuess =
          if | fuel < 0                -> Continue (\_ -> newton startFuel prevGuess curGuess)
             | curGuess `lt` prevGuess ->
                 let nextGuess = half (add curGuess (div m curGuess))
                 in newton fuel curGuess nextGuess
             | otherwise               -> Done curGuess
    in  trampoline (newton startFuel m (half (inc m))) -- (m+1)//2 is always the second guess, saving a division

square : BigInt -> BigInt
square m = multiply m m

avg : BigInt -> BigInt -> BigInt
avg m n = fst <| quotRem (add m n) two

-- Comparison
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
  EQ  -> fstDiff << reverse <| zipWith Basics.compare ds1 ds2
  ord -> ord

lt : BigInt -> BigInt -> Bool
lt m n = LT == (compare m n)

gt : BigInt -> BigInt -> Bool
gt m n = GT == (compare m n)

gte : BigInt -> BigInt -> Bool
gte m n = LT /= (compare m n)

max : BigInt -> BigInt -> BigInt
max m n = case compare m n of
  LT -> n
  _  -> m

min : BigInt -> BigInt -> BigInt
min m n = case compare m n of
  GT -> n
  _  -> m

fstDiff : [Order] -> Order
fstDiff ords = case dropWhile ((==) EQ) ords of
  []     -> EQ
  ord::_ -> ord

-- Utilities
isZero : BigInt -> Bool
isZero i = case i of 
  Zero -> True
  _    -> False

abs : BigInt -> BigInt
abs b = case b of
  Zero        -> Zero
  Positive _  -> b
  Negative ds -> Positive ds

range : BigInt -> BigInt -> [BigInt]
range lo hi = case compare lo hi of
  GT -> []
  _  -> let loop cur left acc = case left of
              Zero       -> reverse acc
              Positive _ -> loop (inc cur) (dec left) (cur :: acc)
        in  loop lo ((hi `add` one) `subtract` lo) []

dropZeros : [Int] -> [Int]
dropZeros = dropWhile ((==) 0)
