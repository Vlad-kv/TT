open Hw1;;
open Hw2_unify;;

type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type

module StrSet = Set.Make(String);;
module StrMap = Map.Make(String);;

let rec string_of_simp_type s_t =
	match s_t with
	  | S_Elem(str) -> str
	  | S_Arrow(s_1, s_2) -> "(" ^ (string_of_simp_type s_1) ^ " -> " ^ (string_of_simp_type s_2) ^ ")"
;;

let get_reused_name_in_lambda l =
	let rec calc_global_vars l global_vars lokal_vars = 
		match l with
		  | Abs(str, l) ->
		  		calc_global_vars l global_vars (StrSet.add str lokal_vars)
		  | Var(str) ->
		  		if (StrSet.mem str lokal_vars) then
		  			global_vars
		  		else
		  			(StrSet.add str global_vars)
		  | App(l_1, l_2) ->
		  		let global_vars = calc_global_vars l_1 global_vars lokal_vars in
		  		calc_global_vars l_2 global_vars lokal_vars
	in
	let rec check l global_vars lokal_vars =
		match l with
		  | Abs(str, l) ->
		  		let res_1 = if ((StrSet.mem str global_vars) || (StrSet.mem str lokal_vars)) then
		  						Some str
		  					else
		  						None
		  		in
		  		begin
			  		match check l global_vars (StrSet.add str lokal_vars) with
			  		  | (lokal_vars, res_2) ->
			  		  		if (res_2 <> None) then
			  		  			(lokal_vars, res_2)
			  		  		else
			  		  			(lokal_vars, res_1)
		  		end
		  | Var(str) -> (lokal_vars, None)
		  | App(l_1, l_2) -> 
		  	begin
		  		match check l_1 global_vars lokal_vars with
		  		  | (lokal_vars, res_1) ->
		  			match check l_2 global_vars lokal_vars with
		  			  | (lokal_vars, res_2) ->
		  			  		if (res_1 = None) then
		  			  			(lokal_vars, res_2)
		  			  		else
		  			  			(lokal_vars, res_1)
		  	end
	in
	let global_vars = calc_global_vars l StrSet.empty StrSet.empty in
	let res = check l global_vars StrSet.empty in
	snd res
;;

let s_arrow_symbol = "";;

let make_system l =
	let rec string_of_lambda x = 
		match x with
		  | Abs (str, l) -> "<\\" ^ str ^ "." ^ (string_of_lambda l) ^ ">"
		  | Var k        -> k
		  | App (l1, l2) -> "<" ^ (string_of_lambda l1) ^ "_" ^ (string_of_lambda l2) ^ ">"
	in
	let reused_name = get_reused_name_in_lambda l in
	begin
		match reused_name with
			| None -> ()
			| Some name -> failwith ("lambda \"" ^ (string_of_lambda l) ^ "\" have reused var \"" ^ name ^ "\"")
	end;
	let get_var first_s l =
		Var(first_s ^ "_" ^ (string_of_lambda l))
	in
	let rec calc res l =
		match l with
		  | Abs(str, l_1) ->
		  		let equation = ((get_var "t" l), Fun(s_arrow_symbol, [Var("a_" ^ str); (get_var "t" l_1)])) in
		  		equation :: (calc res l_1)
		  | Var(str) -> (Var("a_" ^ str), Var("t_" ^ str)) :: res
		  | App(l_1, l_2) ->
		  		let res = calc res l_1 in
		  		let res = calc res l_2 in
		  		let equation_1 = ((get_var "t" l_1), Fun(s_arrow_symbol, [(get_var "t" l_2); (get_var "a" l)])) in
		  		let equation_2 = ((get_var "t" l), (get_var "a" l)) in
		  		equation_1 :: equation_2 :: res
	in
	(calc [] l, ("t_" ^ (string_of_lambda l)))
;;

let rec simp_type_of_algebraic_term term =
	match term with
	  | Fun(f, l) ->
	  	if (f = s_arrow_symbol) then
		  	begin
		  		match l with
		  		  | [term_1; term_2] ->
		  		  		let res_1 = simp_type_of_algebraic_term term_1 in
		  		  		let res_2 = simp_type_of_algebraic_term term_2 in
		  		  		S_Arrow(res_1, res_2)
		  		  | _ -> failwith "impossible to convert algebraic_term to simp_type"
		  	end
  		else
  			failwith ("unknown function name : " ^ f)
	  | Var(str) -> S_Elem(str)
;;

let infer_simp_type l_term = 
	let res = make_system l_term in
	let system = fst res in
	let main_var = snd res in
	match solve_system system with
	  | None -> None
	  | Some solution ->
	  	begin
	  		(* let printer pair = 
	  			print_string ("  " ^ (fst pair) ^ " = " ^ (string_of_algebraic_term (snd pair)) ^ "\n")
	  		in
	  		print_string "original solution:\n";
	  		List.iter printer solution; *)
	  		assert(check_solution solution system); (*debug*)
	  		let convert pair = 
	  			((fst pair), (simp_type_of_algebraic_term (snd pair)))
	  		in
	  		let solution = List.map convert solution in
	  		let find pair = (fst pair) = main_var in
	  		let main_pair = List.find find solution in
	  		let filter pair = (String.get (fst pair) 0) = 'a' in 
	  		let solution = List.filter filter solution in
	  		Some(solution, (snd main_pair))
	  	end
;;

type hm_lambda = HM_Var of string | HM_Abs of string * hm_lambda | HM_App of hm_lambda * hm_lambda | HM_Let of string * hm_lambda * hm_lambda
type hm_type = HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type

let rec string_of_hm_type hm_type =
	match hm_type with
	  | HM_Elem(var) -> var
	  | HM_Arrow(type_1, type_2) -> ("(" ^ (string_of_hm_type type_1) ^ " -> " ^ (string_of_hm_type type_2) ^ ")")
	  | HM_ForAll(var, type_1) -> ("(@" ^ var ^ "." ^ (string_of_hm_type type_1) ^ ")")
;;

let rec string_of_hm_lambda hm_lambda = 
	match hm_lambda with
	  | HM_Var(var) -> var
	  | HM_Abs(var, lambda_1) -> ("(\\" ^ var ^ "." ^ (string_of_hm_lambda lambda_1) ^ ")")
	  | HM_App(lambda_1, lambda_2) -> ("(" ^ (string_of_hm_lambda lambda_1) ^ " " ^ (string_of_hm_lambda lambda_2) ^ ")")
	  | HM_Let(var, lambda_1, lambda_2) -> ("(let " ^ var ^ " = " ^ (string_of_hm_lambda lambda_1) ^ " in " ^ (string_of_hm_lambda lambda_2) ^ ")")
;;

let string_of_var var = 
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
let rec get_next_not_used_var var used_vars =
	let new_var = get_next_var var in
	if (StrSet.mem (string_of_var new_var) used_vars) then
		get_next_not_used_var new_var used_vars
	else
		new_var
;;
(* Применяет подстановку substitution к свободным переменным типа hm_type. *)
let substitute hm_type substitution =
	let rec lok_subst hm_type substitution used_vars =
		match hm_type with
		  | HM_Elem(str) ->
		  		if ((not(StrSet.mem str used_vars)) && (StrMap.mem str substitution)) then
		  			StrMap.find str substitution
		  		else
		  			HM_Elem(str)
		  | HM_Arrow(type_1, type_2) ->
		  		HM_Arrow(lok_subst type_1 substitution used_vars, lok_subst type_2 substitution used_vars)
		  | HM_ForAll(str, type_1) ->
		  		HM_ForAll(str, lok_subst type_1 substitution (StrSet.add str used_vars))
	in
	lok_subst hm_type substitution StrSet.empty
;;
(* Делает композицию данных подстановок - new_subst, такую что 
   (substitute (substitute hm_type subst_2) subst_1) = (substitute hm_type new_subst)
   для любого hm_type. *)
let make_composition_of_substitutions subst_1 subst_2 =
	let convert hm_type = substitute hm_type subst_1 in
	let upd_subst_2 = StrMap.map convert subst_2 in
	let merge key val_1 val_2 = 
		match (val_1, val_2) with
		  | (Some type_1, Some type_2) -> val_2
		  | (None, Some type_2) -> val_2
		  | (Some type_1, None) -> val_1
		  | (None, None) -> None
	in
	StrMap.merge merge subst_1 upd_subst_2
;;
(* Преобразует безкванторный hm_type в algebraic_term. *)
let rec algebraic_term_of_hm_type hm_type =
	match hm_type with
	  | HM_Elem(str) -> Var(str)
	  | HM_Arrow(type_1, type_2) -> Fun("", [algebraic_term_of_hm_type type_1; algebraic_term_of_hm_type type_2])
	  | HM_ForAll(var, type_1) -> failwith "hm_type contains quantifier - conversion impossible"
;;
(* Преобразует algebraic_term в hm_type, если все функциональные переменные равны "" и количество аргументов у каждой функции = 2. *)
let rec hm_type_of_algebraic_term algebraic_term =
	match algebraic_term with
	  | Fun(var, l) ->
	  		if (var = "") then
	  			if ((List.length l) = 2) then
	  				let t_1 = (List.nth l 0) in
	  				let t_2 = (List.nth l 1) in
	  				HM_Arrow(hm_type_of_algebraic_term t_1, hm_type_of_algebraic_term t_2)
	  			else
	  				failwith "wrong number of arguments (in hm_type_of_algebraic_term)"
	  		else
	  			failwith ("unknown name of function : " ^ var)
	  | Var(var) -> HM_Elem(var)
;;
(* Возвращает: set несвязанных переменных. *)
let get_free_vars hm_type =
	let rec lok_get_free_vars hm_type used_vars free_vars =
		match hm_type with
		  | HM_Elem(str) ->
		  		if (not(StrSet.mem str used_vars)) then
		  			StrSet.add str free_vars
		  		else
		  			free_vars
		  | HM_Arrow(type_1, type_2) ->
		  		let free_vars = lok_get_free_vars type_1 used_vars free_vars in
		  		lok_get_free_vars type_2 used_vars free_vars
		  | HM_ForAll(str, type_1) ->
		  		lok_get_free_vars type_1 (StrSet.add str used_vars) free_vars
	in
	lok_get_free_vars hm_type StrSet.empty StrSet.empty
;;
(* Возвращает: set из всех свободных типовых переменных контекста. *)
let get_free_vars_from_context context =
	let rec lok_get l =
		if (l = []) then
			StrSet.empty
		else
			let res = lok_get (List.tl l) in
			StrSet.union (get_free_vars (snd (List.hd l))) res
	in
	lok_get (StrMap.bindings context)
;;
(* Возвращает: (substitution, hm_type, new_next_var) *)
let rec lok_algoritm_w context hm_term next_var used_vars =
	let res =
	begin
	match hm_term with
	  | HM_Var(var) ->
	  		if (StrMap.mem var context) then
	  			(* Возвращает: (new_display, new_next_var, new_hm_type) - new_hm_type - тот же тип, но без поверхностных кванторов. *)
	  			let rec get_map_for_renaming hm_type next_var = 
	  				match hm_type with
	  				  | HM_ForAll(str, type_1) ->
	  				  	begin
	  				  		let new_var = get_next_not_used_var next_var used_vars in
	  				  		let res = get_map_for_renaming type_1 new_var in
	  				  		match res with (new_display, new_next_var, new_hm_type) ->
	  				  			(StrMap.add str (HM_Elem(string_of_var new_var)) new_display, new_next_var, new_hm_type)
	  				  	end
	  				  | _ ->
	  				  		(StrMap.empty, next_var, hm_type)
	  			in
	  			let var_type = StrMap.find var context in
	  			match (get_map_for_renaming var_type next_var) with
	  				(new_display, new_next_var, new_hm_type) ->
	  					Some (StrMap.empty, substitute new_hm_type new_display, new_next_var)
	  		else
	  			failwith ("Unbound value " ^ var)
	  | HM_Abs(var, expr_1) ->
	 	begin
	  		let new_var = get_next_not_used_var next_var used_vars in
	  		let lok_context = StrMap.add var (HM_Elem (string_of_var new_var)) context in
	  		let res = lok_algoritm_w lok_context expr_1 new_var used_vars in
	  		match res with
	  		  | Some (substitution, hm_type, new_next_var) ->
	  		  	let str_new_var = string_of_var new_var in
	  		  	let new_type = 
	  		  		if (StrMap.mem str_new_var substitution) then
	  		  			StrMap.find str_new_var substitution
	  		  		else
	  		  			HM_Elem(str_new_var)
	  		  	in
	  		  	Some (substitution, HM_Arrow(new_type, hm_type), new_next_var)
	  		  | None -> None
	  	end
	  | HM_App(expr_1, expr_2) ->
	  	begin
	  		let res = lok_algoritm_w context expr_1 next_var used_vars in
	  		match res with
	  		  | None -> None
	  		  | Some (subst_1, type_1, next_var) ->
	  		    begin
	  		    	let convert hm_type = substitute hm_type subst_1 in
	  		    	let upd_context = StrMap.map convert context in
	  		    	let res = lok_algoritm_w upd_context expr_2 next_var used_vars in
	  		    	match res with
	  		    	  | None -> None
	  		    	  | Some (subst_2, type_2, next_var) ->
	  		    	  	begin
	  		    	  		let new_var = get_next_not_used_var next_var used_vars in
	  		    	  		let str_new_var = string_of_var new_var in
	  		    	  		let type_1 = substitute type_1 subst_2 in
	  		    	  		let a_term_1 = algebraic_term_of_hm_type type_1 in
	  		    	  		let a_term_2 = algebraic_term_of_hm_type (HM_Arrow(type_2, (HM_Elem str_new_var))) in
	  		    	  		let res = solve_system [(a_term_1, a_term_2)] in
	  		    	  		match res with
	  		    	  		  | None -> None
	  		    	  		  | Some l ->
	  		    	  		  	begin
	  		    	  		  		let rec create_subst l =
	  		    	  		  			if (l = []) then
	  		    	  		  				StrMap.empty
	  		    	  		  			else
	  		    	  		  				let map = create_subst (List.tl l) in
	  		    	  		  				let var = fst (List.hd l) in
	  		    	  		  				let var_type = hm_type_of_algebraic_term (snd (List.hd l)) in
	  		    	  		  				StrMap.add var var_type map
	  		    	  		  		in
	  		    	  		  		let subst_3 = create_subst l in
	  		    	  		  		let res_subst = make_composition_of_substitutions subst_3 (make_composition_of_substitutions subst_2 subst_1) in
	  		    	  		  		let res_type =
	  		    	  		  			if (StrMap.mem str_new_var res_subst) then
	  		    	  		  				StrMap.find str_new_var res_subst
	  		    	  		  			else
	  		    	  		  				HM_Elem(str_new_var)
	  		    	  		  		in
	  		    	  		  		Some (res_subst, res_type, new_var)
	  		    	  		  	end
	  		    	  	end
	  		    end
	  	end
	  | HM_Let(var, expr_1, expr_2) -> 
	  	begin
	  		(* Замыкает все свободные переменные hm_type за исключением тех, которые свободны в context-е. *)
	  		let closure hm_type context =
	  			let set_to_closure = StrSet.inter (get_free_vars hm_type) (get_free_vars_from_context context) in
	  			let rec apply_closure l =
	  				if (l = []) then
	  					hm_type
	  				else
	  					let res = apply_closure (List.tl l) in
	  					HM_ForAll(List.hd l, res)
	  			in
	  			apply_closure (StrSet.elements set_to_closure)
	  		in
	  		let res_1 = lok_algoritm_w context expr_1 next_var used_vars in
	  		match res_1 with
	  		  | None -> None
	  		  | Some (subst_1, type_1, next_var) ->
		  		begin
		  			let convert hm_type = substitute hm_type subst_1 in
		  			let upd_context = StrMap.map convert (StrMap.remove var context) in
		  			let upd_context = StrMap.add var (closure type_1 upd_context) upd_context in
		  			let res_2 = lok_algoritm_w upd_context expr_2 next_var used_vars in
		  			match res_2 with
		  			  | None -> None
		  			  | Some (subst_2, type_2, next_var) ->
			  				Some (make_composition_of_substitutions subst_2 subst_1, type_2, next_var)
		  		end
	  	end
	end
	in
	let print_state context hm_term res =
		let printer var var_type =
			print_string ("  " ^ var ^ " : " ^ (string_of_hm_type var_type) ^ "\n")
		in
		print_string "\n----------\n";
		print_string "context :\n";
		StrMap.iter printer context;
		print_string ("hm_term : " ^ (string_of_hm_lambda hm_term) ^ "\n");
		match res with
		  | None -> print_string "No solution.\n"
		  | Some (substitution, hm_type, new_next_var) ->
		  	begin
		  		print_string "Solution:\n";
		  		let printer var var_type =
		  			print_string ("  " ^ var ^ " = " ^ (string_of_hm_type var_type) ^ "\n")
		  		in
		  		StrMap.iter printer substitution;
		  		print_string ("main type : " ^ (string_of_hm_type hm_type) ^ "\n");
		  	end
	in
	print_state context hm_term res;
	res
;;

let algorithm_w hm_term =
	match (lok_algoritm_w StrMap.empty hm_term ('a', 0) StrSet.empty) with
	  | Some (substitution, hm_type, new_next_var) ->
	  		Some ((StrMap.bindings substitution), hm_type)
	  | None -> None
;;

(* Возвращает: list из token-ов. *)
let rec get_tokens str pos token = 
	let is_whitespace c =
		((c = ' ') || (c = '\012') || (c = '\n') || (c = '\r') || (c = '\t'))
	in
	let is_main_sumbol c =
		((c = '(') || (c = ')') || (c = '.') || (c = '\\') || (c = '=') || (c = '@') || (c = '-') || (c = '>'))
	in
	if (pos = (String.length str)) then
		if (token <> "") then
			[token]
		else
			[]
	else
	begin
		let c = String.get str pos in
		if (is_whitespace c) then
			let res = get_tokens str (pos + 1) "" in
			if (token <> "") then
				token :: res
			else
				res
		else
			if (is_main_sumbol c) then
				let res = (String.make 1 c) :: (get_tokens str (pos + 1) "") in
				if (token <> "") then
					token :: res
				else
					res
			else
				get_tokens str (pos + 1) (String.concat "" [token; String.make 1 c])
	end
;;
(* Возвращает list без первого, если он (первый) совпал.*)
let next_token_is expected l =
	if (l = []) then
		failwith ("Error - no tokens, expected \"" ^ expected ^ "\"")
	else
		let first = List.hd l in
		if (first = expected) then
			List.tl l
		else
			failwith ("Unexpected token - expected \"" ^ expected ^ "\", found \"" ^ first ^ "\"")
;;

let hm_lambda_of_string str = 
	let is_valid_name name =
		((name <> "(") && (name <> ")") && (name <> ".") && (name <> "\\") && (name <> "=") && (name <> "let") && (name <> "in") && (name <> "@"))
	in
	(* Возвращает: (lambda, new_list). *)
	let rec parse prev_expr l =
		let try_parse_next prev_expr l =
			if (l = []) then
				(prev_expr, l)
			else
				let f = List.hd l in
				if ((f = "(") || (f = "\\") || (f = "let") || (is_valid_name f)) then
  					parse (Some(prev_expr)) l
  				else
  					(prev_expr, l)
		in
		let merge prev_expr new_expr =
			match prev_expr with
			  | None -> new_expr
			  | Some expr -> HM_App(expr, new_expr)
		in
		match l with
		  | "(" :: tail ->
		  	begin
		  		let res = parse None tail in
		  		let res_lambda = merge prev_expr (fst res) in
		  		let new_list = next_token_is ")" (snd res) in
		  		try_parse_next res_lambda new_list
		  	end
		  | "\\" :: var :: "." :: l ->
  		  	begin
  		  		if (is_valid_name var) then
  		  			match (parse None l) with
  		  				(lambda, new_list) ->
  		  					let res = HM_Abs(var, lambda) in
  		  					(merge prev_expr res, new_list)
  		  		else
  		  			failwith ("Error - not valid name \"" ^ var ^ "\"")
  		  	end
		  | "let" :: var :: "=" :: l ->
		  	begin
		  		if (not (is_valid_name var)) then
		  			failwith ("Error - not valid name \"" ^ var ^ "\"")
		  		else
		  		let res_1 = parse None l in
		  		let l = next_token_is "in" (snd res_1) in
		  		let res_2 = parse None l in
		  		let res = HM_Let(var, fst res_1, fst res_2) in
		  		(merge prev_expr res, snd res_2)
		  	end
		  | var :: l ->
		  		if (not (is_valid_name var)) then
		  			failwith ("Error - not valid name \"" ^ var ^ "\"")
		  		else
		  			let res = merge prev_expr (HM_Var(var)) in
		  			try_parse_next res l
		  | _ -> failwith "Error - unexpected condition"
	in
	let res = parse None (get_tokens str 0 "") in
	if ((snd res) <> []) then
		failwith "Error!"
	else
		fst res
;;

let hm_type_of_string str = 
	let is_valid_name name =
		((name <> "(") && (name <> ")") && (name <> ".") && (name <> "\\") && (name <> "=") && (name <> "@") && (name <> "-")  && (name <> ">"))
	in
	(* Возвращает: (calc_type, new_list). *)
	let rec parse l =
		let try_parse_next prev_expr l =
			if (l = []) then
				(prev_expr, l)
			else
				match l with
				  | "-" :: ">" :: l ->
				  		let res = parse l in
  						(HM_Arrow(prev_expr, fst res), snd res)
				  | _ -> (prev_expr, l)
		in
		match l with
		  | "(" :: tail ->
		  	begin
		  		let res = parse tail in
		  		let res_type = fst res in
		  		let new_list = next_token_is ")" (snd res) in
		  		try_parse_next res_type new_list
		  	end
		  | "@" :: var :: "." :: l ->
  		  	begin
  		  		if (is_valid_name var) then
  		  			match (parse l) with
  		  				(res_type, new_list) ->
  		  					(HM_ForAll(var, res_type), new_list) 
  		  		else
  		  			failwith ("Error - not valid name \"" ^ var ^ "\"")
  		  	end
		  | var :: l ->
		  		if (not (is_valid_name var)) then
		  			failwith ("Error - not valid name \"" ^ var ^ "\"")
		  		else
		  			let res = HM_Elem(var) in
		  			try_parse_next res l
		  | _ -> failwith "Error - unexpected condition"
	in
	let res = parse (get_tokens str 0 "") in
	if ((snd res) <> []) then
		failwith "Error!"
	else
		fst res
;;

(* Алгоритм W, где можно указать внешний контекст. *)
let algorithm_w_with_context hm_term context =
	let rec map_of_list l =
		if (l = []) then
			StrMap.empty
		else
			let res = map_of_list (List.tl l) in
			match List.hd l with
			(var, var_type) ->
				StrMap.add var var_type res
	in
	let context = (map_of_list context) in
	match lok_algoritm_w context hm_term ('z', -1) (get_free_vars_from_context context) with
	  | Some (substitution, hm_type, new_next_var) ->
	  		Some ((StrMap.bindings substitution), hm_type)
	  | None -> None
;;
