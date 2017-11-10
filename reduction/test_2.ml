open Hw1;;
open Hw1_reduction;;

let _ = Gc.set {(Gc.get()) with Gc.stack_limit = 64 * 1024 * 1024};;

let test_1_1 = lambda_of_string "\\a0.\\a2.a0";;
let test_1_2 = lambda_of_string "\\a1.\\a0.a1";;
assert ((is_alpha_equivalent test_1_1 test_1_2) == true);;

let test_2_1 = lambda_of_string "\\a0.\\a2.a2";;
let test_2_2 = lambda_of_string "\\a1.\\a0.a1";;
assert ((is_alpha_equivalent test_2_1 test_1_2) == false);;

let test_1_1 = lambda_of_string "a";;
let test_1_2 = lambda_of_string "\\a.\\b.c";;
let test_1_3 = "c";;
assert ((free_to_subst test_1_1 test_1_2 test_1_3) == false);;

let test_2_1 = lambda_of_string "a";;
let test_2_2 = lambda_of_string "c \\a.\\c.c";;
let test_2_3 = "c";;
assert ((free_to_subst test_2_1 test_2_2 test_2_3) == true);;

let test_3_1 = lambda_of_string "q w e r t y \\a.a z";;
let test_3_2 = lambda_of_string "c \\z.\\b.c";;
let test_3_3 = "c";;
assert ((free_to_subst test_3_1 test_3_2 test_3_3) == false);;

(*-----------------------------------------------------------*)

let test = lambda_of_string "q w e r \\t.\\y.t(t y)";;
assert ((is_normal_form test) == true);;

let test = lambda_of_string "(\\x.x x)(\\x.x x)";;
assert ((is_normal_form test) == false);;

let test = lambda_of_string "(\\x.\\y.x x)(y y)";;
assert ((is_normal_form test) == true);; (* * *)

(*-----------------------------------------------------------*)

let test = lambda_of_string "(\\x.x x)(\\x.x x)";;
assert (is_alpha_equivalent (normal_beta_reduction test) test);;

let test = lambda_of_string "(x x)((\\x.\\y.\\z.y (x z x)) a1 a2 a3)";;
assert (is_alpha_equivalent (normal_beta_reduction test) (lambda_of_string "(x x)((\\y.\\z.y(a1 z a1))a2 a3)"));;

let test = lambda_of_string "\\x.\\y.x";;
assert (is_alpha_equivalent (normal_beta_reduction test) test);;

(*-----------------------------------------------------------*)

let check_name_unif expr =
	let test = lambda_of_string expr in
	assert (is_alpha_equivalent (alpha_equ_unification_of_names test) test);
	print_string ((string_of_lambda (alpha_equ_unification_of_names test)) ^ "\n")
;;

check_name_unif "(\\x.\\y.\\z.y (x z x)) a1 a2";;
check_name_unif "(\\a. (\\a. (\\a. (\\a. a a) a) a) a) a c";;
check_name_unif "(\\a. (\\a. (\\a. a) (\\a. a) (\\a. a) (\\a. a) (\\a. a) a) a) f";;

(*-----------------------------------------------------------*)

let check_reduce_to_normal_form expr result =
	let expr = lambda_of_string expr in
	let res = reduce_to_normal_form expr in
	print_string ((* (string_of_lambda expr) ^ " ---> " ^  *) (string_of_lambda res) ^ "\n");
	assert (is_alpha_equivalent res (lambda_of_string result))
;;

check_reduce_to_normal_form "x x" "x x";;
check_reduce_to_normal_form "(\\x.x x) (\\x.x z)" "z z";;

let unreachable = "((\\x.x x) (\\x.x x))" in

check_reduce_to_normal_form ("( (\\x.\\y. y c1 c2 x)"^unreachable^" )(\\x.\\y.\\z.x y)") "c1 c2";;

check_reduce_to_normal_form ("(\\x.x x x)((\\x.x x x) ((\\x.x x x) ((\\x.x x x) ((\\x.x x x) ((\\x.x x x)" ^
							"((\\x.x x x)((\\x.x x x) ((\\x.x x x) ((\\x.x x x) ((\\x.x x x) ((\\x.x x x)" ^
							"((\\x.x x x)((\\x.x x x) ((\\x.x x x) ((\\x.x x x) ((\\x.x x x) ((\\x.x x x)" ^
							"((\\x.x x x)((\\x.x x x) ((\\x.x x x) ((\\x.x x x) ((\\x.x x x) ((\\x.x x x)" ^
										"(\\x.x)" ^
							"))))))" ^
							"))))))" ^
							"))))))" ^
							")))))")
							"\\x.x";;

let f = "(\\a.\\b.b)";;
let t = "(\\a.\\b.a)";;
let _not = "(\\a.a" ^ f ^ t ^ ")";;
let _xor = "(\\a.\\b.a(" ^ _not ^ " b)b)";;
let _and = "(\\a.\\b.a b " ^ f ^ ")";;
let _or = "(\\a.\\b."^_not^"("^_and^" ("^_not^" a) ("^_not^" b)))";;
let __xor = "(\\a.\\b."^_or^" ("^_and^"("^_not^"a)b) ("^_and^"a("^_not^"b)) )";;

check_reduce_to_normal_form (__xor ^ t ^ f) t;;

let is_zero = "(\\n.n (\\a. "^f^") "^t^")";;
let _inc = "(\\n.\\f.\\x.n f (f x))";;
let _mult = "(\\a.\\b.\\f.a (b f))"

let n_0 = "(\\f.\\x.x)";;
let n_1 = "(\\f.\\x.f x)";;
let n_2 = "(\\f.\\x.f (f x))";;
let n_3 = "(\\f.\\x.f (f (f x)))";;
let n_4 = "(\\f.\\x.f (f (f (f x))))";;
let n_5 = "(\\f.\\x.f (f (f (f (f x)))))";;
let n_6 = "(\\f.\\x.f (f (f (f (f (f x))))))";;

check_reduce_to_normal_form (_mult ^ n_2 ^ n_2) n_4;;
check_reduce_to_normal_form (_mult ^ n_2 ^ n_3) n_6;;

check_reduce_to_normal_form (is_zero ^ n_0) t;;
check_reduce_to_normal_form (is_zero ^ n_1) f;;
check_reduce_to_normal_form (is_zero ^ n_2) f;;

let _fst = "(\\x.x "^t^")";;
let _snd = "(\\x.x "^f^")";;
let one_step = "(\\pair. \\s.s ("^_snd^"pair)("^_inc^"("^_snd^"pair)) )";;

check_reduce_to_normal_form (one_step ^ "(\\s.s"^n_2^n_2^")") ("(\\s.s"^n_2^n_3^")");;

let _dec = "(\\n."^_fst^"(n "^one_step^" (\\s.s"^n_0^n_0^")) )";;

check_reduce_to_normal_form (_dec ^ n_0) n_0;;
check_reduce_to_normal_form (_dec ^ n_1) n_0;;
check_reduce_to_normal_form (_dec ^ n_2) n_1;;
check_reduce_to_normal_form (_dec ^ n_3) n_2;;

let y_comb = "(\\f.(\\x.f(x x)) (\\x.f(x x)))";;
let fact_base = "(\\f.\\n.("^is_zero^"n)"^n_1^"("^_mult^"n (f ("^_dec^" n)) ))";;
let fact = "("^y_comb ^ fact_base^")";;

check_reduce_to_normal_form (fact ^ n_0) n_1;;
check_reduce_to_normal_form (fact ^ n_1) n_1;;
check_reduce_to_normal_form (fact ^ n_2) n_2;;
check_reduce_to_normal_form (fact ^ n_3) n_6;;

let rec test_pack l =
	if (l = []) then
		()
	else
		begin
			let pair = List.hd l in
			check_reduce_to_normal_form (fst pair) (snd pair);
			test_pack (List.tl l)
		end
;;

test_pack
[ ("((\\l0.((\\l1.((\\l2.((\\l3.((\\l4.((\\l5.((\\l6.((\\l7.((\\l8.((\\l9.((\\l10.((\\l11.((\\l12.((\\l13.((l13 (\\l14.(\\l15.(l14 (l14 l15))))) (\\l14.(\\l15.(l14 (l14 (l14 l15))))))) (\\l13.(\\l14.(((l0 (\\l15.(\\l16.(\\l17.(((l1 (l10 l16)) (l12 l17)) (((l1 (l10 l17)) ((l15 (l11 l16)) (\\l18.(\\l19.(l18 l19))))) ((l15 (l11 l16)) ((l15 l16) (l11 l17))))))))) l13) l14))))) (\\l12.(\\l13.(\\l14.((l12 l13) (l13 l14))))))) (\\l11.(\\l12.(\\l13.(((l11 (\\l14.(\\l15.(l15 (l14 l12))))) (\\l14.l13)) (\\l14.l14))))))) (\\l10.((l10 (\\l11.l3)) l2)))) (l0 (\\l9.(\\l10.(\\l11.((\\l12.((\\l13.(((l1 l12) l13) (((l1 l13) l12) ((l9 (l4 l10)) (l4 l11))))) (l8 l11))) (l8 l10)))))))) (\\l8.((l8 (\\l9.l3)) l2)))) (\\l7.(\\l8.((l8 l4) l7))))) (\\l6.(\\l7.((l6 l5) l7))))) (\\l5.(\\l6.(\\l7.((l5 l6) (l6 l7))))))) (\\l4.(\\l5.(\\l6.(((l4 (\\l7.(\\l8.(l8 (l7 l5))))) (\\l7.l6)) (\\l7.l7))))))) (\\l3.(\\l4.l4)))) (\\l2.(\\l3.l2)))) (\\l1.(\\l2.(\\l3.((l1 l2) l3)))))) (\\l0.((\\l1.(l0 (l1 l1))) (\\l1.(l0 (l1 l1))))))",
   "\\a.\\b.a (a (a (a (a (a (a (a (a b))))))))");
  ("((\\l0.((\\l1.((\\l2.((\\l3.((\\l4.((\\l5.((\\l6.((\\l7.((\\l8.((\\l9.((\\l10.((\\l11.((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l3 l10) ((l2 ((l3 l10) ((l2 ((l3 l10) ((l2 ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) ((l3 l10) ((l3 l10) ((l2 ((l2 ((l3 l10) ((l2 ((l3 l10) l11)) l10))) l10)) l10))))) l10))) l10)) l10)) l10))) l10))) l10)))) l10)) l10)) l10))) l10)) l10)))) l10)))) l10))) l10)) l10)) l10)) l10)) l10))) l10)) l10))) l10)) l10)))) l10))))))))) l10)) l10)) l10)))))) l10))) l10)) l10))))) l10))) l10)))))) l10)))) l10)) l10)) l10)) l10)) l10)) l10)))))) l10))) l10)) l10))) l10)) l10))) l10)) l10)) l10))) l10))) l10))))) l10)) l10))) l10)) l10)) l10))) l10)))) l10)) l10))) l10)) l10)) l10)) l10)) l10)) l10)) l10)))) l10))) l10)))) l10)) l10))) l10)) l10))) l10))) l10)) l10))) l10))) l10))) l10))) l10))) l10)))))) l10)) l10))))) l10)) l10)) l10))) l10)) l10)) l10)) l10))) l10)))) l10)) l10)) l10)) l10)) l10))) l10))) l10)) l10)))) l10))) l10)) l10))) l10))) l10))) l10)) l10)) l10))) l10))) l10))) l10))) l10))) l10)))) l10)) l10)))) l10)))))))))))) l10))) l10))) l10))) l10)) l10))))) l10))) l10))) l10))))) l10)))))))) l10)))))))) l10))) l10))))) l10)) l10)) l10))))) l10))) l10)) l10)) l10)) l10)) l10))) l10)) l10)) l10)) l10))) l10))))))) l10)))) l10))) l10)) l10)) l10)))) l10)) l10)) l10)) l10)) l10))))) l10)))) l10)) l10)) l10)) l10))) l10))) l10)) l10)))) l10)) l10)) l10)))) l10))) l10)) l10)) l10)))) l10)))) l10)) l10)) l10))) l10))) l10)) l10))) l10))) l10)))) l10)))) l10)) l10))))) l10))) l10))))) l10)) l10))) l10)) l10)))) l10))) l10)))))) l10)) l10)) l10)) l10)) l10)) l10)) l10)))) l10))) l10)) l10))))))) l10)) l10)) l10))))) l10)) l10)) l10)) l10)) l10)) l10)))))) l10)) l10))) l10))))) l10)) l10)) l10)) l10))) l10)) l10))) l10)) l10))) l10)) l10)) l10))) l10)) l10)))))))) l10)) l10))) l10)) l10))) l10)) l10))))) l10))) l10)))) l10)) l10)) l10)) l10)) l10)))) l10))) l10)) l10)) l10))) l10)))))) l10))) l10))) l10))) l10)) l10)) l10)) l10)) l10)) l10)) l10)))) l10)) l10)))) l10)) l10)))))) l10))) l10))))) l10)) l10)) l10))) l10)) l10))) l10)) l10))) l10))) l10)))) l10)))) l10)))) l10)) l10)) l10)) l10)) l10)) l10)) l10)))) l10))) l10)) l10))) l10)) l10)) l10)) l10)) l10)) l10)) l10))))) l10)) l10))))) l10)))))) l10)) l10))) l10))) l10)) l10)) l10)))) l10)))) l10)) l10)) l10))) l10)) l10)))) l10)) l10)))) l10)) l10)) l10))))))))))) l10))))) l10)) l10))) l10))) l10)) l10)) l10)) l10)) l10))) l10)))) l10))) l10))))) l10))))))) l10))) l10))) l10)) l10))) l10)))) l10)) l10))) l10))) l10)) l10)) l10)) l10))))) l10)) l10))))))) l10)) l10)) l10)) l10)) l10)) l10)))) l10))) l10))) l10))))) l10)) l10)) l10)))) l10)))) l10)) l10))))) l10))))))) l10)) l10))) l10)))) l10))))) l10)))) l10))) l10)))) l10)) l10)) l10)) l10)) l10)) l10)) l10)) l10)))))) l10)))) l10))) l10)) l10))) l10)) l10)) l10)) l10))))) l10)))) l10)))) l10)) l10)) l10)) l10))) l10))) l10))))))) l10)))) l10))) l10)) l10)) l10))) l10))) l10)) l10)))) l10)) l10)) l10)) l10)) l10)) l10)) l10)) l10)))) l10))) l10)))) l10)) l10)) l10))) l10))) l10)) l10))) l10)) l10))))))))) l10)) l10)) l10)) l10))) l10))))) l10)) l10))))) l10)) l10))) l10))) l10)) l10))) l10)) l10)) l10))) l10)))) l10)) l10)) l10)) l10)) l10)) l10)))) l10))) l10)) l10))) l10)) l10)) l10)) l10)))) l10))))))))))) l10))) l10)) l10)) l10)))) l10))) l10)))))) l10)) l10)) l10)))) l10)))))) l10)) l10)) l10))))) l10))) l10))) l10)) l10)) l10)) l10))) l10)))) l10)) l10)) l10))) l10)))))) l10)) l10)) l10))) l10)) l10)) l10)) l10))))))) l10)) l10)))) l10)))) l10))) l10)) l10))) l10)) l10)))) l10))) l10))) l10))) l10)) l10)) l10)) l10)))))))) l10)) l10)) l10))) l10)))) l10)) l10)) l10)) l10)) l10))) l10)))) l10)))))))) l10)) l10)) l10))) l10)) l10))))))) l10)) l10)) l10))) l10))) l10)) l10)) l10)) (\\l11.l11))) ((\\l10.(l10 l10)) (\\l10.(l10 l10))))) (l0 (\\l9.(\\l10.(\\l11.((\\l12.((\\l13.(((l1 l12) l13) (((l1 l13) l12) ((l9 (l4 l10)) (l4 l11))))) (l8 l11))) (l8 l10)))))))) (\\l8.((l8 (\\l9.l3)) l2)))) (\\l7.(\\l8.((l8 l4) l7))))) (\\l6.(\\l7.((l6 l5) l7))))) (\\l5.(\\l6.(\\l7.((l5 l6) (l6 l7))))))) (\\l4.(\\l5.(\\l6.(((l4 (\\l7.(\\l8.(l8 (l7 l5))))) (\\l7.l6)) (\\l7.l7))))))) (\\l3.(\\l4.l4)))) (\\l2.(\\l3.l2)))) (\\l1.(\\l2.(\\l3.((l1 l2) l3)))))) (\\l0.((\\l1.(l0 (l1 l1))) (\\l1.(l0 (l1 l1))))))",
   "\\x.x");
  ("(\\k.\\i.\\o.k (k (k i o) o) o) (\\x.\\y.x) (\\x.x) ((\\x.x x) (\\x.x x))", "\\x.x")]
;;

test_pack
[("(\\x.\\y.y)((\\z.z z)(\\z.z z))", "\\y.y");
  ("a ((\\y.\\z.y) (\\p.p))", "a \\z.\\p.p");
  ("(\\x.x) (\\y.y) (\\z.z))", "(\\z.z)");
  ("(\\x.x x)(\\a.\\b.b b b)", "\\b.b b b");
  ("(\\x.x x x)((\\x.x)(\\x.x))", "\\x.x");
  ("(\\x.\\y.x)(\\x.x)((\\x.x x)(\\x.x x))", "\\x.x");
  ("(\\n.\\f.\\x.n (\\g.\\h.h (g f)) (\\u.x) (\\u.u)) (\\f.\\x.f (f (f x)))", "(\\f.(\\x.(f (f x))))");
  ("((\\x.\\y.x)(\\z.y)) k", "\\z.y");
  ("(\\x.\\y.x) k", "\\y.k");
  ("(\\y.\\m.y (\\f.\\n.(\\s.(s (\\x.\\a.\\b.b) (\\a.\\b.a)) (\\f.\\x.x) (f s)) (m n)) (\\f.\\x.f (f (f x)))) (\\f.(\\x.f (x x)) (\\x.f (x x))) ((\\n.\\f.\\x.n (\\g.\\h.h (g f)) (\\u.x) (\\u.u)))",
  	"(\\t.(\\t1.t1))");
  ("(\\n.\\f.\\x.n (\\g.\\h.h (g f)) (\\u.x) (\\u.u)) (\\f.\\x.f (f (f x)))", "\\x1.\\x2.(x1 (x1 x2))");
  ("((\\l0.((\\l1.((\\l2.((\\l3.((\\l4.((\\l5.((\\l6.((\\l7.((\\l8.((\\l9.((\\l10.((\\l11.((\\l12.((\\l13.((l13 (\\l14.(\\l15.(l14 (l14 l15))))) (\\l14.(\\l15.(l14 (l14 (l14 l15))))))) (\\l13.(\\l14.(((l0 (\\l15.(\\l16.(\\l17.(((l1 (l10 l16)) (l12 l17)) (((l1 (l10 l17)) ((l15 (l11 l16)) (\\l18.(\\l19.(l18 l19))))) ((l15 (l11 l16)) ((l15 l16) (l11 l17))))))))) l13) l14))))) (\\l12.(\\l13.(\\l14.((l12 l13) (l13 l14))))))) (\\l11.(\\l12.(\\l13.(((l11 (\\l14.(\\l15.(l15 (l14 l12))))) (\\l14.l13)) (\\l14.l14))))))) (\\l10.((l10 (\\l11.l3)) l2)))) (l0 (\\l9.(\\l10.(\\l11.((\\l12.((\\l13.(((l1 l12) l13) (((l1 l13) l12) ((l9 (l4 l10)) (l4 l11))))) (l8 l11))) (l8 l10)))))))) (\\l8.((l8 (\\l9.l3)) l2)))) (\\l7.(\\l8.((l8 l4) l7))))) (\\l6.(\\l7.((l6 l5) l7))))) (\\l5.(\\l6.(\\l7.((l5 l6) (l6 l7))))))) (\\l4.(\\l5.(\\l6.(((l4 (\\l7.(\\l8.(l8 (l7 l5))))) (\\l7.l6)) (\\l7.l7))))))) (\\l3.(\\l4.l4)))) (\\l2.(\\l3.l2)))) (\\l1.(\\l2.(\\l3.((l1 l2) l3)))))) (\\l0.((\\l1.(l0 (l1 l1))) (\\l1.(l0 (l1 l1))))))",
    "\\x1.(\\x2.(x1 (x1 (x1 (x1 (x1 (x1 (x1 (x1 (x1 x2))))))))))");
  ("(\\s.\\k.\\i.(((s ((s (k s)) ((s ((s (k s)) ((s (k k)) i))) (k ((s (k (s ((s (k s)) ((s (k (s (k (s ((s ((s ((s i) (k (k (k i))))) (k ((s (k k)) i)))) (k ((s ((s (k s)) ((s (k k)) i))) (k i))))))))) ((s ((s (k s)) ((s (k k)) ((s (k s)) ((s (k (s (k ((s ((s (k s)) ((s (k k)) ((s (k s)) ((s (k k)) i))))) (k ((s ((s (k s)) ((s (k k)) i))) (k i)))))))) ((s ((s (k s)) ((s (k k)) i))) (k i))))))) (k ((s (k k)) i)))))))) ((s (k k)) ((s ((s (k s)) ((s (k k)) i))) (k i)))))))) (k (k ((s ((s (k s)) ((s (k k)) i))) ((s ((s (k s)) ((s (k k)) i))) ((s ((s (k s)) ((s (k k)) i))) (k i))))))) ((s ((s ((s (k s)) ((s (k k)) i))) (k ((s i) i)))) ((s ((s (k s)) ((s (k k)) i))) (k ((s i) i))))) ((s ((s (k s)) ((s (k (s (k s)))) ((s ((s (k s)) ((s (k (s (k s)))) ((s (k (s (k k)))) ((s ((s (k s)) ((s (k k)) i))) (k ((s (k (s (k (s i))))) ((s (k (s (k k)))) ((s (k (s i))) ((s (k k)) i)))))))))) (k (k ((s (k k)) i))))))) (k (k (k i))))) (\\x.\\y.\\z.x z (y z)) (\\x.\\y.x) (\\x.x)",
    "(\\t9.(\\t2.(t9 (t9 (t9 (t9 (t9 (t9 t2))))))))")]
;;
