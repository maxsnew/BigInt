module BigInt (BigInt, fromString, show, negate, add, subtract,
               multiply, quotRem, div, mod, sqrt, compare, lt, gt, gte, max, min,
               isZero, abs, range)
    where


import Basics
import Debug
import Dict (Dict)
import Dict
import List
import Result
import String
import Trampoline (Trampoline(Continue, Done), trampoline)

import BigInt.Err ((<=<), either)
import BigInt.Err as Err

type BigInt = Positive Digits
            | Negative Digits
            | Zero

-- Invariants: non-empty, most significant digit is non-zero
-- Interpretation: a backwards number, i.e., if base == 10, 1024 is represented as [4,2,0,1]
type alias Digits = List Digit

-- A BigInt digit, invariant: d : Digit ==> (0 <= d <= base-1)
type alias Digit  = Int

-- TODO: this might make division slower, but maybe we can just do a better division
-- 10^7: Highest power of 10 such that base ^ 2 < maxInt, needed for multiply
-- Power of 10 so it can be quickly changed to base 10
baseZeros = 7
base = 10 ^ baseZeros

type alias Fuel = Int
startFuel : Fuel
startFuel = 100

-- Can fail if the int is not an integer
-- fromInt : Int -> BigInt
-- fromInt i = if not (i >= minInt && i <= maxInt)
--             then Debug.crash (show i ++ " is not an exact integer")
--             else (fromString << show) i

maxInt : Int
maxInt = unsafeToInt maxBInt
minInt : Int
minInt = unsafeToInt minBInt

maxBInt : BigInt
maxBInt = unsafeFromString "9007199254740992"
minBInt : BigInt
minBInt = negate maxBInt

unsafeToInt : BigInt -> Int
unsafeToInt b = case b of
  Zero     -> 0
  Positive ds -> sumDigits ds
  Negative ds -> ((\x -> -x) << sumDigits) ds

toInt : BigInt -> Maybe Int
toInt b = if (b `lt` minBInt || b `gt` maxBInt)
          then Nothing
          else Just (unsafeToInt b) 

sumDigits : Digits -> Int
sumDigits = List.sum << List.indexedMap (\i d -> base ^ i * d)

unsafeFromString : String -> BigInt
unsafeFromString = either Debug.crash Basics.identity << fromString

fromString : String -> Result String BigInt
fromString =
  let getSign : List Char -> Result String (Bool, List Char) -- ^ True for Positive
      getSign cs = case cs of
        [] -> Err "Empty String is invalid Integer"
        '-'::c::more -> Ok (False, c::more)
        c::more      -> Ok (True, cs)

      checkDigit c = Dict.member c digits
      
      checkDigits : (Bool, List Char) -> Result String (Bool, List Char)
      checkDigits (b, cs) = Result.map ((,) b) << Err.forEach cs <| \c ->
        case checkDigit c of
          False -> Err (String.cons c " is not a digit.")
          True  -> Ok c

      bunch : List Char -> List (List Char)
      bunch cs =
        case splitAt (baseZeros) cs of
          ([], []) -> []
          (l,  []) -> [l]
          (l,   r) -> l :: bunch r

      readSmallInt : List Char -> Int
      readSmallInt cs = case String.toInt (String.fromList cs) of
                          Ok n -> n
                          Err e -> Debug.crash ("Internal error in BigInt, please report: readSmallInt " ++ e)

      interpret : (Bool, List Char) -> BigInt
      interpret (b, is) = 
        let shortened = dropWhile ((==) '0') is
            ctor = if b then Positive else Negative
              
        in if List.isEmpty shortened
           then Zero
           else ctor (List.map (readSmallInt << List.reverse) (bunch (List.reverse shortened)))

  in Result.map interpret << (checkDigits <=< getSign) << String.toList

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

pad : String -> String
pad s = 
  let len = String.length s
  in 
    if | len < baseZeros -> (String.fromList (List.repeat (baseZeros - len) '0')) ++ s
       | otherwise       -> s


digitString : Digits -> String
digitString = String.fromList <<
              dropWhile ((==) '0') <<
              String.toList <<
              String.join "" << 
              List.map (pad << toString) <<
              List.reverse

show : BigInt -> String
show i = 
  case i of
    Zero        -> "0"
    Positive ds -> digitString ds
    Negative ds -> String.cons '-' << digitString <| ds

splitAt : Int -> List a -> (List a, List a)
splitAt n xs =
  case (n, xs) of
    (0,     _) -> ([], xs)
    (_,    []) -> ([], [])
    (_, x::xs) -> let (l', r') = splitAt (n-1) xs
                  in (x::l', r')

dropWhile : (a -> Bool) -> List a -> List a
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

-- Possibly incorrect now with changed base
quotRemBase : Int -> (Int, Int)
quotRemBase s = (s // base, s % base)

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
               (d1::ds1', d2::ds2') -> let (carry', d) = quotRemBase <| d1 + d2 + carry
                                       in go (fuel - 1) (d::acc) carry' ds1' ds2'

      goWith acc c' ds = let (carry, d) = quotRemBase <| c'
                         in goOne 0 (d::acc) carry ds

      goOne fuel acc carry ds = 
        if | fuel < 0  -> goOne startFuel acc carry ds
           | otherwise -> case ds of
               [] -> pushCarry carry acc
               (d :: ds') -> let (carry', d') = quotRemBase <| d + carry
                             in goOne (fuel - 1) (d'::acc) carry' ds'
  in List.reverse << trampoline <| go startFuel [] 0 ds1 ds2

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
                                         then (newM + base, 1)
                                         else (newM, 0)
                 in go (fuel - 1) ms ss newCarry (newM' - s :: diffAcc)
      carryOut fuel minuend carry diffAcc = 
          if | fuel < 0  -> Continue (\_ -> carryOut startFuel minuend carry diffAcc)
             | otherwise -> case minuend of
                 []    -> Done diffAcc
                 m::ms -> let newM = m - carry
                              (newM', newCarry) = if newM < 0
                                                  then (newM + base, 1)
                                                  else (newM, 0)
                          in carryOut (fuel - 1) ms newCarry (newM' :: diffAcc)
  in List.reverse << dropZeros << trampoline <| go startFuel minuend subtrahend 0 []

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
leftShift ds n = List.repeat n 0 ++ ds

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
               ([],     0) -> Done (List.reverse acc)
               ([],     _) -> Done (List.reverse (carry :: acc))
               (d::ds', _) ->
                 let (newCarry, newD) = quotRemBase (d * digit + carry)
                 in go (fuel - 1) digit ds' newCarry (newD :: acc)
      multDigit d = trampoline (go startFuel d big 0 [])
  in List.foldl1 addDigits << List.indexedMap (\i d -> (multDigit d) `leftShift` i) <| less

one : BigInt
one = unsafeFromString "1"

two : BigInt
two = unsafeFromString "2"

-- Quotient and remainder
quotRem : BigInt -> BigInt -> (BigInt, BigInt)
quotRem m n = case (m, n) of
  (_, Zero) -> Debug.crash "Error, quotRem: can't divide by zero"
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
    let dvisor        = ds2
        push d ds = case d of
          0 -> pushZero ds
          _ -> d :: ds
        pushZero ds = case ds of
          [] -> []
          _  -> 0::ds
        go : Fuel -> Digits -> Digits -> Digits -> Trampoline (Digits, Digits)
        go fuel front back acc =
          if | fuel < 0  -> Continue (\_ -> go startFuel front back acc)
             | otherwise ->
                 case back of
                   []         -> Done (acc, front)
                   (d::back') -> 
                       let front' = push d front
                       in case compareDigits front' dvisor of
                            LT -> go (fuel - 1) front' back' (pushZero acc)
                            GT ->
                                let (digit, rem) = div1Digit front' dvisor
                                in  go (fuel - 1) rem back' (digit :: acc)
                            EQ -> go (fuel - 1)     [] back' (1 :: acc)

        (quotDs, remDs) = trampoline (go startFuel [] (List.reverse ds1) [])
        quot = Positive quotDs
        rem = case List.reverse << dropZeros << List.reverse <| remDs of
          [] -> Zero
          _  -> Positive remDs
    in (quot, rem)

-- arguments should both be positive
div1Digit : Digits -> Digits -> (Digit, Digits)
div1Digit dvend dvisor =
  let go fuel cur =
          if | fuel < 0 -> Continue (\_ -> go startFuel cur)
             | otherwise ->
                 let prod = [cur] `multDigits` dvisor
                 in case compareDigits prod dvend of
                      LT -> go (fuel-1) (cur+1)
                      EQ -> Done (cur, [])
                      GT -> Done (cur - 1, subtractFromGreater dvend ([cur - 1] `multDigits` dvisor))
  in  trampoline (go startFuel 1)

half : BigInt -> BigInt
half m = m `div` two

-- returns the floor of the sqroot
-- uses Newton's Method
sqrt : BigInt -> BigInt
sqrt m = case m of
  Zero         -> zero
  Negative _   -> Debug.crash "Can't take square root of a negative number"
  Positive [1] -> one
  Positive _ ->
    -- Newton's method using integer division
    -- x_(k+1) = 1/2 (x_k + m / x_k)
    let newton fuel prevGuess curGuess =
          if | fuel < 0                -> Continue (\_ -> newton startFuel prevGuess curGuess)
             | curGuess `lt` prevGuess ->
                 let nextGuess = half (add curGuess (div m curGuess))
                 in newton fuel curGuess nextGuess
             | otherwise               -> Done prevGuess
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
compareDigits ds1 ds2 = case Basics.compare (List.length ds1) (List.length ds2) of
  EQ  -> fstDiff << List.reverse <| List.map2 Basics.compare ds1 ds2
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

fstDiff : List Order -> Order
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

range : BigInt -> BigInt -> List BigInt
range lo hi = case compare lo hi of
  GT -> []
  _  -> let loop fuel cur left acc =
              if | fuel < 0  -> Continue (\_ -> loop startFuel cur left acc)
                 | otherwise -> case left of
                     Zero       -> Done (List.reverse acc)
                     Positive _ -> loop (fuel - 1) (inc cur) (dec left) (cur :: acc)
        in trampoline (loop startFuel lo ((hi `add` one) `subtract` lo) [])

dropZeros : List Int -> List Int
dropZeros = dropWhile ((==) 0)
