module Main
%default total

main : IO ()
main = putStrLn "Hello world"

x : Int
x = 42

fiveIsFive : S Z = S Z
fiveIsFive = Refl

twoPlusTwo : 2 + 2 = 4
twoPlusTwo = Refl

disjoint : (n : Nat) -> Z = S n -> Void
disjoint n p = replace {P = disjointTy} p ()
  where
    disjointTy : Nat -> Type
    disjointTy Z = ()
    disjointTy (S k) = Void

plusReduces : (n:Nat) -> plus Z n = n
plusReduces n = Refl

plusReducesZ : (n:Nat) -> n = plus n Z
plusReducesZ Z = Refl
plusReducesZ (S k) = cong {f = S} (plusReducesZ k)

my_cong : {f : t -> u} -> (a = b) -> f a = f b
my_cong Refl = Refl

plusReducesS : (n:Nat) -> (m:Nat) -> S (plus n m) = plus n (S m)
plusReducesS Z m = Refl
plusReducesS (S k) m = cong {f = S} (plusReducesS k m) -- ( S (S (plus k m)) = S (plus k (S m))   )

equ_transitivity : a = b -> b = c -> a = c
equ_transitivity Refl Refl = Refl

commutativity : (n:Nat) -> (m:Nat) -> plus n m = plus m n
commutativity Z m = induction_1 m where
	induction_1 : (m:Nat) -> m = plus m Z
	induction_1 Z = Refl
	induction_1 (S m_1) = cong {f = S} (induction_1 m_1)
commutativity (S n_1) m = 
	let equ_1 = cong {f = S} (commutativity n_1 m) in -- S (plus n_1 m) = S (plus m n_1)
	let equ_2 = plusReducesS m n_1 in -- S (plus m n_1) = plus m (S n_1)
	equ_transitivity equ_1 equ_2 -- S (plus n_1 m) = plus m (S n_1)

test_1 : Integer
test_1 = 1

test_2 : Type
test_2 = Integer

test_3 : Type->Type
test_3 f = f

