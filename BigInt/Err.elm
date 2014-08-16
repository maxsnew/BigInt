module BigInt.Err where

import Either (Either(..))
import Either
import List


map : (a -> b) -> Either e a -> Either e b
map f = Either.either Left (Right . f)

andThen : Either e a -> (a -> Either e b) -> Either e b
andThen e k = Either.either Left k e

(<=<) : (b -> Either e c) -> (a -> Either e b) -> a -> Either e c
(<=<) f g x = g x `andThen` f

forEach : [a] -> (a -> Either e b) -> Either e [b]
forEach xs k = 
  let consM : Either e b -> Either e [b] -> Either e [b]
      consM ex exs = ex  `andThen` (\x -> 
                     exs `andThen` (\xs ->
                     Right (x :: xs)))
  in foldr consM (Right []) . List.map k <| xs
