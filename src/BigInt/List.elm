module BigInt.List where


-- | Use these if you have a list with more than 9007199254740992 elements

-- | List functions that normally use Ints, now using exact BigInts
length : List a -> BigInt
length = List.foldl (\_ i -> inc i) zero

splitAt : BigInt -> List a -> (List a, List a)
splitAt count xs =
  let go fuel count front back =
        if | fuel < 0  -> Continue (\_ -> go startFuel count front back)
           | otherwise -> case compare count zero of
               LT -> Debug.crash "bug: splitAt: negative index!"
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
