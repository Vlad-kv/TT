module Prims
import Data.Fin
import Data.Vect

x : Int
x = 42

foo : String
foo = "Sausage machine"

bar : Char
bar = 'Z'

quux : Bool
quux = False

isSingleton : Bool -> Type
isSingleton True = Nat
isSingleton False = List Nat

sum : (single : Bool) -> isSingleton single -> Nat
sum True x = x
sum False [] = 0
sum False (x :: xs) = x + sum False xs

test_list : List Nat
test_list = 1 :: 2 :: 3 :: 4 :: []

{-
index : Fin n -> Vect n a -> a
index FZ     (x :: xs) = x
index (FS k) (x :: xs) = index k xs
-}

test_v : Vect 4 Nat
test_v = (2 :: 3 :: 4 :: 5 :: Nil)


