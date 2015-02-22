module BigInt.Convenient (zero, one, two, three, four, five, six, seven, eight, nine) where

import BigInt as I
import Debug

unsafeFromString s =
  case I.fromString s of
    Ok n  -> n
    Err l ->
        Debug.crash <| "Initialization error in BigInt.Convenient: report at github.com/maxsnew/BigInt" ++ s

zero  = unsafeFromString "0"
one   = unsafeFromString "1"
two   = unsafeFromString "2"
three = unsafeFromString "3"
four  = unsafeFromString "4"
five  = unsafeFromString "5"
six   = unsafeFromString "6"
seven = unsafeFromString "7"
eight = unsafeFromString "8"
nine  = unsafeFromString "9"
