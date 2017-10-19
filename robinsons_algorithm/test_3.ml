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

let check system expected_res = 
	print_string "system:\n";
	let lok_print pair =
		print_string ("  " ^ (string_of_algebraic_term (fst pair)) ^ " = " ^ (string_of_algebraic_term (snd pair)) ^ "\n");
	in
	List.iter lok_print system;
	let result = solve_system system in
	begin
		match result with
		  | None ->
		  		print_string "no solution\n";
		  		assert(expected_res = false);
		  | Some solution ->
		  		begin
			  		print_string "solution:\n";
			  		let lok_print pair =
						print_string ("  " ^ (fst pair) ^ " = " ^ (string_of_algebraic_term (snd pair)) ^ "\n");
					in
					List.iter lok_print solution;
					assert(check_solution solution system);
					assert(expected_res);
				end
	end;
	print_string "\n";
;;

let system = [
	(Var("x_1"), Var("x_2"));
	(Fun("f1", [Var("x_1"); Var("x_4")]), Var("x_5"));
	(Fun("f1", [Var("a"); Var("b")]), Var("x_5"));
];;
check system true;;

check [
	(Var("x_1"), Fun("f", [Var("x_2"); Var("a")]));
	(Var("x_2"), Fun("f", [Var("x_3"); Var("b")]));
	(Var("x_3"), Fun("f", [Var("x_1"); Var("c")]));
] false;;

check [
	(Var("x_1"), Fun("f", [Var("x_2"); Var("a")]));
	(Var("x_2"), Fun("f", [Var("x_3"); Var("b")]));
	(Var("x_3"), Fun("f", [Var("x_4"); Var("c")]));
] true;;

check [
	(Var("x_1"), Fun("f", [Var("x_2"); Var("a")]));
	(Var("x_2"), Fun("f", [Var("x_3"); Var("b")]));
	(Var("x_1"), Var("x_2"));
] false;;

check [
	(Var("x_1"), Var("x_2"));
	(Var("x_2"), Var("x_3"));
	(Var("x_3"), Var("x_4"));
	(Var("x_4"), Var("x_4"));
] true;;

check [
	(Var("t_<\\f.<\\x.<f_<f_x>>>>"), Fun("f", [Var("a_f"); Var("t_<\\x.<f_<f_x>>>")]));
	(Var("t_<\\x.<f_<f_x>>>"), Fun("f", [Var("a_x"); Var("t_<f_<f_x>>")]));
	(Var("t_f"), Fun("f", [Var("t_<f_x>"); Var("t_<f_<f_x>>")]));
	(Var("t_f"), Fun("f", [Var("t_x"); Var("t_<f_x>")]));
	(Var("a_x"), Var("t_x"));
	(Var("a_f"), Var("t_f"));
	(Var("a_f"), Var("t_f"));
] true;;

