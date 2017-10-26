open Hw2_inference;;
open Hw1;;
open Hw2_unify;;
open Hw2;;

module StrSet = Set.Make(String);;
module StrMap = Map.Make(String);;

let check_get_reused_name_in_lambda l =
	let l = lambda_of_string l in
	print_string ("lambda: " ^ (string_of_lambda l) ^ "\n");
	let res = get_reused_name_in_lambda l in
	match res with
	  | None -> print_string "no name reused\n"
	  | Some name -> print_string ("reused name : \"" ^ name ^ "\"\n")
;;

check_get_reused_name_in_lambda "\\x.\\y.\\z.x (z y) x";;
check_get_reused_name_in_lambda "\\x.\\y.\\z.x (z y) (\\c.c) (\\c.c)";;
check_get_reused_name_in_lambda "(\\x.\\y.(z y) (\\c.c))z";;
check_get_reused_name_in_lambda "(\\x.\\y.y (\\z.c))z";;
(*-------*)
print_string("\n");;

let check_infer_simp_type l expected_result =
	print_string ("lambda " ^ (string_of_lambda l) ^ "\n");
	(* print_string "system:\n";
	let res = make_system l in
	let printer pair =
		let to_str term = string_of_simp_type (simp_type_of_algebraic_term term) in
		print_string ("  " ^ (to_str (fst pair)) ^ " = " ^ (to_str (snd pair)) ^ "\n");
	in
	List.iter printer (fst res);
	print_string "\n"; *)
	let res = infer_simp_type l in
	begin
		match res with
		  | None -> print_string "no solution\n";
		  			assert(expected_result = false)
		  | Some result ->
		  	begin
		  		print_string "solution:\n";
		  		let printer pair =
		  			print_string ("  " ^ (fst pair) ^ " = " ^ (string_of_simp_type (snd pair)) ^ "\n")
		  		in
		  		List.iter printer (fst result);
		  		print_string ("main type : " ^ (string_of_simp_type (snd result)) ^ "\n");
		  		assert(expected_result = true)
		  	end
	end;
	print_string ("\n")
;;

let check_infer_simp_type_with_renaming l expected_result =
	check_infer_simp_type (alpha_equ_unification_of_names l) expected_result
;;

check_infer_simp_type (lambda_of_string "\\f.\\x.f(f x)") true;;
check_infer_simp_type (lambda_of_string "(\\f.(f f))(\\x.(x x))") false;;

let f = "(\\a.\\b.b)";;
let t = "(\\a.\\b.a)";;
let negation = "(\\a.a" ^ f ^ t ^ ")";;
let xor = "(\\a.\\b.a(" ^ negation ^ " b)b)";;
let inc = "(\\n.\\f.\\x.(n f)(f x))";;
let two = "(\\f.\\x.f(f x))";;

let pair = "(\\s.s a b)";;
let first = "(\\p.p" ^ t ^ ")";;
let second = "(\\p.p" ^ f ^ ")";;

check_infer_simp_type_with_renaming (lambda_of_string (inc ^ two)) true;;
check_infer_simp_type_with_renaming (lambda_of_string negation) true;;

check_infer_simp_type (lambda_of_string "\\s.s a b") true;;
check_infer_simp_type_with_renaming (lambda_of_string (first)) true;;
check_infer_simp_type_with_renaming (lambda_of_string (first ^ pair)) true;;
check_infer_simp_type_with_renaming (lambda_of_string (second ^ pair)) true;;

(*-------*)

let check_composition list_subst_1 list_subst_2 hm_type =
	let rec create_substitution list_subst =
		if (list_subst = []) then
			StrMap.empty
		else
			let res = create_substitution (List.tl list_subst) in
			match (List.hd list_subst) with (str, hm_type) ->
				(StrMap.add str hm_type res)
	in
	let subst_1 = create_substitution list_subst_1 in
	let subst_2 = create_substitution list_subst_2 in
	let composition = make_composition_of_substitutions subst_1 subst_2 in
	assert( ((substitute (substitute hm_type subst_2) subst_1) = (substitute hm_type composition)))
;;

check_composition
	[("a", HM_Elem("b"))]
	[("c", HM_Elem("a"))]
	(HM_Elem("c"));;

check_composition
	[
		("a", HM_Elem("b"));
		("z", HM_Elem("m"));
	]
	[
		( "c", HM_Arrow(HM_Elem("a"), HM_Elem("c")) );
		("a", HM_Elem("b"));
	]
	(HM_Arrow(HM_Elem("c"), HM_Arrow(HM_Elem("a"), HM_Elem("z"))));;

(*-------*)

let check_hm_lambda_of_string str =
	print_string ("original : " ^ str ^ "\n");
	print_string ("after_tranform : " ^ (string_of_hm_lambda (hm_lambda_of_string str)) ^ "\n\n")
;;
check_hm_lambda_of_string "x";;
check_hm_lambda_of_string "q w e r t";;
check_hm_lambda_of_string "q (w e) (r ((t)))";;
check_hm_lambda_of_string "(\\q.\\v.q (w e) \\t.(r ((t))) z) q \\e.w e";;
check_hm_lambda_of_string "let x = \\c.c c in x x w";;
check_hm_lambda_of_string "let x = a let x = \\m.m in (qwert) f_1 f_2 in x (\\m.a v_4) x";;

(*-------*)

let check_hm_type_of_string str =
	print_string ("original : " ^ str ^ "\n");
	print_string ("after_tranform : " ^ (string_of_hm_type (hm_type_of_string str)) ^ "\n\n")
;;
check_hm_type_of_string "x";;
check_hm_type_of_string "a -> b -> a";;
check_hm_type_of_string "@a.@b.(a -> (b)) -> a";;

(*-------*)

let check_algorithm_w hm_lambda expected_result =
	print_string ("hm_lambda : " ^ (string_of_hm_lambda hm_lambda) ^ "\n");
	let res = algorithm_w  hm_lambda in
	begin
		match res with
		  | Some pair ->
		  	begin
		  		print_string "Solution:\n";
		  		let printer pair =
		  			print_string ("  " ^ (fst pair) ^ " = " ^ (string_of_hm_type (snd pair)) ^ "\n")
		  		in
		  		List.iter printer (fst pair);
		  		print_string ("main type : " ^ (string_of_hm_type (snd pair)) ^ "\n");
		  		assert(expected_result = true)
		  	end
		  | None ->
	  		begin
	  			print_string "No solution.\n";
	  			assert(expected_result = false)
	  		end
  	end;
  	print_string "\n"
;;

let check_algorithm_w_of_str hm_lambda expected_result =
	check_algorithm_w (hm_lambda_of_string hm_lambda) expected_result
;;
(* 
check_algorithm_w_of_str "\\x.x" true;;
check_algorithm_w_of_str "\\x.\\y.x y" true;;
check_algorithm_w_of_str "\\x.x x" false;;

check_algorithm_w_of_str (inc ^ two) true;;

check_algorithm_w_of_str
	"let inc = \\n.\\f.\\x.(n f)(f x) in
	 let x = \\f.\\x.f(f(f x)) in
	 inc x"
true;; *)

check_algorithm_w_of_str (xor ^ f ^ f) true;;


check_algorithm_w_of_str "(((\\a.(\\b.((a ((\\a.((a (\\a.\\b.b)) (\\a.\\b.a))) b)) b))) (\\a.\\b.b)) (\\a.\\b.b))" true;; (* ((e -> (f -> f)) -> ((h -> (i -> h)) -> (h -> (i -> h)))) *)

check_algorithm_w_of_str "((     (\\b.( (\\a.\\b.b) ((\\a.((a (\\a.\\b.b)) (\\a.\\b.a))) b)) b))   (\\a.\\b.b))" true;; (*((f -> (g -> g)) -> ((i -> (j -> i)) -> (i -> (j -> i))))*)

check_algorithm_w_of_str "((    ( (\\a.\\b.b) ((\\a.((a (\\a.\\b.b)) (\\a.\\b.a))) (\\a.\\b.b) )) (\\a.\\b.b) ))" true;; (* (o -> (p -> p))  *)

(* 
(\a.((a (\a.(\b.b))) (\a.(\b.a)))) : (((e -> (f -> f)) -> ((h -> (i -> h)) -> j)) -> j)

(xor ^ f ^ f)

((     (\\a.(\\b.((a ((\\a.((a (\\a.\\b.b)) (\\a.\\b.a))) b)) b)))  (\\a.\\b.b)) (\\a.\\b.b))
((     (\\b.( (\\a.\\b.b) ((\\a.((a (\\a.\\b.b)) (\\a.\\b.a))) b)) b))   (\\a.\\b.b))

( (\\a.\\b.b) ((\\a.((a (\\a.\\b.b)) (\\a.\\b.a))) (\\a.\\b.b) )) (\\a.\\b.b)
 *)


let check_algorithm_w_with_context hm_lambda context expected_result =
	print_string ("hm_lambda : " ^ (string_of_hm_lambda hm_lambda) ^ "\n");
	print_string ("context :\n");
	let printer pair =
		print_string ("  " ^ (fst pair) ^ " : " ^ (string_of_hm_type (snd pair)) ^ "\n")
	in
	List.iter printer context;
	let res = algorithm_w_with_context hm_lambda context in
	begin
		match res with
		  | Some pair ->
		  	begin
		  		print_string "Solution:\n";
		  		let printer pair =
		  			print_string ("  " ^ (fst pair) ^ " = " ^ (string_of_hm_type (snd pair)) ^ "\n")
		  		in
		  		List.iter printer (fst pair);
		  		print_string ("main type : " ^ (string_of_hm_type (snd pair)) ^ "\n");
		  		assert(expected_result = true)
		  	end
		  | None ->
	  		begin
	  			print_string "No solution.\n";
	  			assert(expected_result = false)
	  		end
  	end;
  	print_string "\n"
;;

let check_algorithm_w_with_context_of_str hm_lambda context expected_result =
	let convert pair = (fst pair, hm_type_of_string (snd pair)) in
	let context = List.map convert context in
	check_algorithm_w_with_context (hm_lambda_of_string hm_lambda) context expected_result
;;

(* let string_of_var var = 
	if ((snd var) = 0) then
		(Char.escaped  (fst var))
	else
		(Char.escaped  (fst var)) ^ (string_of_int (snd var))
;; *)

(* check_algorithm_w_with_context_of_str "
	
"
[
	("fst", "(((c -> (d -> c)) -> e) -> e)");
	("snd", "(((c -> (d -> d)) -> e) -> e)");
	("is_ints_equal", "@a.int -> int -> a -> a -> a")
]
true
;;
 *)
