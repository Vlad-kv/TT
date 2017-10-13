open Hw2_unify;;

let t_1 = Fun("f", [Var("a"); Fun("f_2", [Var("a")]); Var("b")]);;

print_string ((algebraic_term_to_string t_1) ^ "\n");;
(*******************************)

let system = [(t_1, Var("m")); (Var("f1"), Var("f2")); (Var("f3"), Var("f4"))];;
let res = system_to_equation system;;
print_string ((algebraic_term_to_string (fst res)) ^ " = " ^ (algebraic_term_to_string (snd res)) ^ "\n");;
(*******************************)

