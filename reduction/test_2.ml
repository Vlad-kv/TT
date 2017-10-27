open Hw1;;
open Hw2;;

let _ = Gc.set {(Gc.get()) with Gc.stack_limit = 64 * 1024 * 1024};;

let test_1_1 = lambda_of_string "\\a0.\\a2.a0";;
let test_1_2 = lambda_of_string "\\a1.\\a0.a1";;
assert ((is_alpha_equivalent test_1_1 test_1_2) == true);;

let test_2_1 = lambda_of_string "\\a0.\\a2.a2";;
let test_2_2 = lambda_of_string "\\a1.\\a0.a1";;
assert ((is_alpha_equivalent test_2_1 test_1_2) == false);;

(* print_int (int_of_peano (S(S(S Z))) );;
print_string "\n";;

print_int 10;;
let test_str = read_line();;
print_string test_str;; *)

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
	let res = reduce_to_normal_form (lambda_of_string expr) in
	print_string ((string_of_lambda res) ^ "\n");
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
let xor = "(\\a.\\b.a(" ^ _not ^ " b)b)";;
let _and = "(\\a.\\b.a b " ^ f ^ ")";;
let _or = "(\\a.\\b."^_not^"("^_and^" ("^_not^" a) ("^_not^" b)))";;
let _xor = "(\\a.\\b."^_or^" ("^_and^"("^_not^"a)b) ("^_and^"a("^_not^"b)) )";;

check_reduce_to_normal_form (_xor ^ t ^ f) t;;

