module BigInt.Err where

import List
import List ((::), foldr)
import Result
import Result (Result(..))

either : (e -> b) -> (a -> b) -> Result e a -> b
either kerr kok r =
  case r of
    Err e -> kerr e
    Ok  x -> kok  x

(<=<) : (b -> Result e c) -> (a -> Result e b) -> a -> Result e c
(<=<) f g x = g x `Result.andThen` f

forEach : List a -> (a -> Result e b) -> Result e (List b)
forEach xs k = foldr (Result.map2 (::)) (Ok []) << List.map k <| xs
