module Revision
%default total

{-
	plus : Nat -> Nat -> Nat
	plus Z     y = y
	plus (S k) y = S (plus k y)

	data (=) : a -> b -> Type where
	Refl : x = x
-}

zero_plus_n : (n : Nat) -> plus Z n = n
zero_plus_n n = Refl

my_cong : {f : t_1 -> t_2} -> a = b -> f a = f b
my_cong Refl = Refl

n_plus_zero : (n : Nat) -> plus n Z = n
n_plus_zero Z = Refl
n_plus_zero (S m) = my_cong {f = S} (n_plus_zero m)


inv_reflection : (a = b) -> (b = a)
inv_reflection Refl = Refl

refl_r : (a_1 = a_2) -> (a_1 = b) -> (a_2 = c) -> (b = c)
refl_r Refl Refl Refl = Refl

lockal_p_2 : (n : Nat) -> (m : Nat) -> S (plus n m) = plus n (S m)
lockal_p_2 Z m = Refl   -- (S m = S m)
lockal_p_2 (S k) m = my_cong {f = S} (lockal_p_2 k m)  -- (S (S (plus k m)) = S (plus k (S m)))

commutativity : (n : Nat) -> (m : Nat) -> plus n m = plus m n
commutativity Z m = inv_reflection (n_plus_zero m) -- (m = plus m Z) ?, 
commutativity (S n) m = lockal_p n m where -- (S (plus n m) = plus m (S n)) ?
	lockal_p : (n : Nat) -> (m : Nat) -> S (plus n m) = plus m (S n)
	lockal_p n Z = my_cong {f = S} (n_plus_zero n) -- (S (plus n Z) = S n) ?
	lockal_p n (S m) = my_cong {f = S} (lockal_p_3 n m) where -- (S (plus n (S m)) = S (plus m (S n))) ? , (plus n (S m) = plus m (S n)) ?
		lockal_p_3 : (n : Nat) -> (m : Nat) -> plus n (S m) = plus m (S n)
		lockal_p_3 n m =
			let eq_1 = lockal_p_2 n m in -- (S (plus n m) = plus n (S m))
			let eq_2 = lockal_p_2 m n in -- (S (plus m n) = plus m (S n))
			let eq_3 = my_cong {f = S} (commutativity n m) in -- (S (plus n m) = S (plus m n))
			refl_r eq_3 eq_1 eq_2



