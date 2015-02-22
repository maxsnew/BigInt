module BigInt where

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

-- Highest power of 10 such that base ^ 2 < maxInt, needed for multiply
-- Power of 10 so it can be quickly changed to base 10
base = 10 ^ 7

type alias Fuel = Int
startFuel : Fuel
startFuel = 100

-- Can fail if the int is not an integer
-- fromInt : Int -> BigInt
-- fromInt i = if not (i >= minInt && i <= maxInt)
--             then Debug.crash (show i ++ " is not an exact integer")
--             else (fromString << show) i

maxInt : Int
maxInt = toInt maxBInt
minInt : Int
minInt = toInt minBInt

maxBInt : BigInt
maxBInt = fromString "9007199254740992"
minBInt : BigInt
minBInt = negate maxBInt

toInt : BigInt -> Int
toInt b = if (b `lt` minBInt || b `gt` maxBInt)
          then Debug.crash (toString b ++ " is not small enough to be an exact int")
          else case b of
            Zero     -> 0
            Positive ds -> sumDigits ds
            Negative ds -> ((\x -> -x) << sumDigits) ds

sumDigits : Digits -> Int
sumDigits = List.sum << List.indexedMap (\i d -> 10 ^ i * d)

fromString : String -> BigInt
fromString = either Debug.crash Basics.identity << safeFromString

safeFromString : String -> Result String BigInt
safeFromString =
  let getSign : List Char -> Result String (Bool, List Char) -- ^ True for Positive
      getSign cs = case cs of
        [] -> Err "Empty String is invalid Integer"
        '-'::c::more -> Ok (False, c::more)
        c::more      -> Ok (True, cs)

      readDigit c = Dict.get c digits
      
      readDigits : (Bool, List Char) -> Result String (Bool, List Int)
      readDigits (b, cs) = Result.map ((,) b) << Err.forEach cs <| \c ->
        case readDigit c of
          Nothing -> Err (String.cons c " is not a digit.")
          Just  d -> Ok d

      interpret : (Bool, List Int) -> BigInt
      interpret (b, is) = 
        let shortened = dropZeros is
            ctor b = if b then Positive else Negative
              
        in if List.isEmpty shortened
           then Zero
           else ctor b (List.reverse shortened)

  in Result.map interpret << (readDigits <=< getSign) << String.toList

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

show : BigInt -> String
show i = 
  let digitString : Digits -> String
      digitString = String.join "" << List.map toString << List.reverse
  in case i of
    Zero        -> "0"
    Positive ds -> digitString ds
    Negative ds -> String.cons '-' << digitString <| ds

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
                 let (newCarry, newD) = quotRem10 (d * digit + carry)
                 in go (fuel - 1) digit ds' newCarry (newD :: acc)
      multDigit d = trampoline (go startFuel d big 0 [])
  in List.foldl1 addDigits << List.indexedMap (\i d -> (multDigit d) `leftShift` i) <| less

one : BigInt
one = fromString "1"

two : BigInt
two = fromString "2"

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
  let go cur =
        let prod = [cur] `multDigits` dvisor
        in case compareDigits prod dvend of
          LT -> go (cur+1)
          EQ -> (cur, [])
          GT -> (cur - 1, subtractFromGreater dvend ([cur - 1] `multDigits` dvisor))
  in  go 1

half : BigInt -> BigInt
half m = m `div` two

-- returns the floor of the sqroot
-- uses Newton's Method
flroot : BigInt -> BigInt
flroot m = case m of
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

length : List a -> BigInt
length = List.foldl (\_ i -> inc i) zero

splitAt : BigInt -> List a -> (List a, List a)
splitAt count xs =
  let go fuel count front back =
        if | fuel < 0  -> Continue (\_ -> go startFuel count front back)
           | otherwise -> case compare count zero of
               LT -> Debug.crash "bug: permsE: splitAt: negative index!"
               EQ -> Done (List.reverse front, back)
               GT -> case back of
                 []    -> Done (List.reverse front, [])
                 x::xs -> go (fuel - 1) (dec count) (x::front) xs
  in trampoline (go startFuel count [] xs)

take : BigInt -> List a -> List a
take i = fst << splitAt i

drop : BigInt -> List a -> List a
drop i = snd << splitAt i

remove : BigInt -> List a -> List a
remove n xs =
  let (front, back) = splitAt n xs
      rest = case back of
        []    -> []
        _::xs -> xs
  in front ++ rest
