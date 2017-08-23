open Hw1;;
open Hw2;;

(*
let l1 = lambda_of_string "x y";;
let l2 = lambda_of_string "x x";;
let l3 = lambda_of_string "\\x.y";;
let l4 = lambda_of_string "\\a0.\\a3.\\a4.\\w.\\a6.q";;
let l5 = lambda_of_string "q w e r t y u i";;
let l6 = lambda_of_string "(\\x.y t) \\c.\\x.c";;

let l7 = lambda_of_string "\\a0.\\a3.(a4 \\a4.a4 \\a4.\\a4.q)";;


let test_1_1 = lambda_of_string "\\a0.\\a2.a0";;
let test_1_2 = lambda_of_string "\\a1.\\a0.a1";; (*true*)

let test_2_1 = lambda_of_string "\\a0.\\a2.a2";;
let test_2_2 = lambda_of_string "\\a1.\\a0.a1";; (*false*)

is_alpha_equivalent test_2_1 test_2_2;;

(* substitute l7 "a4" "q785";;  *)
*)

print_int (int_of_peano (S(S(S Z))) );;
print_string "\n";;

print_int 10;;
let test_str = read_line();;
print_string test_str;;


(*
let test_1_1 = lambda_of_string "\\a.\\b.c";;
let test_1_2 = lambda_of_string "a";;
let test_1_3 = "c";;

free_to_subst test_1_1 test_1_2 test_1_3;; (*false*)

let test_2_1 = lambda_of_string "c \\a.\\c.c";;
let test_2_2 = lambda_of_string "a";;
let test_2_3 = "c";;

free_to_subst test_2_1 test_2_2 test_2_3;; (*true*)

let test_3_1 = lambda_of_string "c \\z.\\b.c";;
let test_3_2 = lambda_of_string "q w e r t y \\a.a z";;
let test_3_3 = "c";;

free_to_subst test_3_1 test_3_2 test_3_3;; (*false*)
*)
