open Hw2_unify;;

let t_1 = Fun("f", [Var("a"); Fun("f_2", [Var("a")]); Var("b")]);;

print_string ((string_of_algebraic_term t_1) ^ "\n");;
(*-----------------------------*)

let system = [(t_1, Var("m")); (Var("f1"), Var("f2")); (Var("f3"), Var("f4"))];;
let res = system_to_equation system;;
print_string ((string_of_algebraic_term (fst res)) ^ " = " ^ (string_of_algebraic_term (snd res)) ^ "\n");;
(*-----------------------------*)

let main_term = Fun("f0", [Var("z"); t_1; t_1]);;
let rules = [("z", t_1); ("a", Var("a2"))];;
let res = apply_substitution rules main_term;;
print_string ((string_of_algebraic_term main_term) ^ "    :   " ^ (string_of_algebraic_term res) ^ "\n");;
(*-----------------------------*)

let system = [
	(Var("x_1"), Var("x_2"));
	(Fun("f1", [Var("x_3"); Var("x_4")]), Var("x_5"))
];;
let solution = [
	("x_1", Var("z_1"));
	("x_2", Var("z_1"));
	("x_3", t_1);
	("x_5", Fun("f1", [t_1; Var("x_4")]))
];;
assert((check_solution solution system));;
let solution = [
	("x_1", Var("z_2"));
	("x_2", Var("z_1"));
	("x_3", t_1);
	("x_5", Fun("f1", [t_1; Var("x_4")]))
];;
assert(not (check_solution solution system));;
let solution = [
	("x_1", Var("z_1"));
	("x_2", Var("z_1"));
	("x_3", t_1);
	("x_5", Fun("f1", [t_1; Var("x_6")]))
];;
assert(not (check_solution solution system));;
(*-----------------------------*)
