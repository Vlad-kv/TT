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

(*
let t a b = a;;
let f a b = b;;
let _not a = ((a f) t);;
let _and a b = ((a b) f);;
let _or a b = (_not ((_and (_not a)) (_not b)));;

let _not_a_and_b a b = _and (_not a) b;;
let _a_and_not_b a b = _and a (_not b);;

(* let __xor a b = _or (_not_a_and_b a b) (_a_and_not_b a b);; *)

let _xor a b = ((_or ((_and a) (_not b))) ((_and (_not a)) b));;
*)

let f = "(\\a.\\b.b)";;
let t = "(\\a.\\b.a)";;
let _not = "(\\a.a" ^ f ^ t ^ ")";;
let xor = "(\\a.\\b.a(" ^ _not ^ " b)b)";;
let _and = "(\\a.\\b.a b " ^ f ^ ")";;
let _or = "(\\a.\\b."^_not^"("^_and^" ("^_not^" a) ("^_not^" b)))";;

let _not_a_and_b = "(\\a.\\b."^_and^"("^_not^"a)b)";;
let _a_and_not_b = "(\\a.\\b."^_and^"a("^_not^"b))";;
let __xor = "(\\a.\\b."^_or^"("^_not_a_and_b^" a b) ("^_a_and_not_b^" a b))";;

let _xor = "(\\a.\\b."^_or^" ("^_and^"a("^_not^"b)) ("^_and^"("^_not^"a)b) )";;

let inc = "(\\n.\\f.\\x.(n f)(f x))";;
let two = "(\\f.\\x.f(f x))";;

let pair = "(\\s.s a b)";;
let first = "(\\p.p" ^ t ^ ")";;
let second = "(\\p.p" ^ f ^ ")";;

check_infer_simp_type_with_renaming (lambda_of_string (inc ^ two)) true;;
check_infer_simp_type_with_renaming (lambda_of_string _not) true;;

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

check_algorithm_w_of_str "\\x.x" true;;
check_algorithm_w_of_str "\\x.\\y.x y" true;;
check_algorithm_w_of_str "\\x.x x" false;;

check_algorithm_w_of_str (inc ^ two) true;;

check_algorithm_w_of_str
	"let inc = \\n.\\f.\\x.(n f)(f x) in
	 let x = \\f.\\x.f(f(f x)) in
	 inc x"
true;;

check_algorithm_w_of_str (xor) true;;
check_algorithm_w_of_str (xor ^ t ^ f) true;;
check_algorithm_w_of_str (xor ^ f ^ f) true;;

check_algorithm_w_of_str (_xor ^ f ^ t)  true;;
check_algorithm_w_of_str (_xor ^ t ^ f)  false;;

check_algorithm_w_of_str "
	let make_pair = \\first.\\second.
		\\s.s first second
	in
	make_pair" true
;;

let check_algorithm_w_with_context context hm_lambda expected_result =
	print_string ("hm_lambda : " ^ (string_of_hm_lambda hm_lambda) ^ "\n");
	print_string ("context :\n");
	let printer pair =
		print_string ("  " ^ (fst pair) ^ " : " ^ (string_of_hm_type (snd pair)) ^ "\n")
	in
	List.iter printer context;
	let res = algorithm_w_with_context context hm_lambda in
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

let check_algorithm_w_with_context_of_str context hm_lambda expected_result =
	let convert pair = (fst pair, hm_type_of_string (snd pair)) in
	let context = List.map convert context in
	check_algorithm_w_with_context context (hm_lambda_of_string hm_lambda) expected_result
;;

(* let string_of_var var = 
	if ((snd var) = 0) then
		(Char.escaped  (fst var))
	else
		(Char.escaped  (fst var)) ^ (string_of_int (snd var))
;;
let get_next_var var = 
	if ((fst var) < 'z') then
		(Pervasives.char_of_int ((Pervasives.int_of_char (fst var)) + 1), (snd var))
	else
		('a', (snd var) + 1)
;;
*)

check_algorithm_w_with_context_of_str
	[
		("if", "@a.bool -> a -> a -> a");
		("make_pair", "@a.@b.a -> b -> pair_t -> a -> b");
		
		("is_equal", "@a.a -> a -> bool");
		("is_less", "@a.a -> a -> bool");
		("concat", "string -> string -> string");

		("int_add", "int -> int -> int");

		("Char_escaped", "char -> string");
		("string_of_int", "int -> string");
		("Pervasives_char_of_int", "int -> char");
		("Pervasives_int_of_char", "char -> int");
		("fst", "@a.@b.(pair_t -> a -> b) -> a");
		("snd", "@a.@b.(pair_t -> a -> b) -> b");

		("0", "int"); ("1", "int");
		("'a'", "char"); ("'z'", "char");
	] "
	let string_of_var = \\var.
		if (is_equal (snd var) 0)
			(Char_escaped (fst var))
			(concat (Char_escaped  (fst var)) (string_of_int (snd var)))
	in
	let get_next_var = \\var. 
		if (is_less (fst var) 'z')
			(make_pair (Pervasives_char_of_int (int_add (Pervasives_int_of_char (fst var)) 1)) (snd var))
			(make_pair 'a' (int_add (snd var) 1))
	in
	get_next_var (make_pair 'a' 0)
	" true
;;
