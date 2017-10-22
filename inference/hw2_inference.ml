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
(* Возвращает: (substitution, hm_type, new_next_var) *)
let lok_algoritm_w context hm_term next_var used_vars =
	match hm_term with
	  | HM_Var(var) ->
	  		if (StrMap.mem var context) then
	  			(* Возвращает: (new_display, new_next_var, new_hm_type) - new_hm_type - тот же тип, но без поверхностных кванторов. *)
	  			let rec get_map_for_renaming hm_type next_var = 
	  				match hm_type with
	  				  | HM_ForAll(str, type_1) ->
	  				  		let new_var = get_next_not_used_var next_var used_vars in
	  				  		let res = get_map_for_renaming type_1 new_var in
	  				  		match res with (new_display, new_next_var, new_hm_type) ->
	  				  			(StrMap.add str (HM_Elem(string_of_var new_var)) new_display, new_next_var, new_hm_type)
	  				  | _ ->
	  				  		(StrMap.empty, next_var, hm_type)
	  			in
	  			let var_type = StrMap.find var context in
	  			match (get_map_for_renaming var_type next_var) with
	  				(new_display, new_next_var, new_hm_type) ->
	  					Some (StrMap.empty, substitute new_hm_type new_display, new_next_var)
	  		else
	  			failwith ("Unbound value " ^ var)
	  | HM_Abs(var, expr_1) -> failwith "Not implemented"
	  | HM_App(expr_1, expr_2) -> failwith "Not implemented"
	  | HM_Let(var, expr_1, expr_2) -> failwith "Not implemented"
;;

let algorithm_w hm_term =
	match (lok_algoritm_w StrMap.empty hm_term ('a', 0) StrSet.empty) with
	  | Some (substitution, hm_type, new_next_var) ->
	  		Some ((StrMap.bindings substitution), hm_type)
	  | None -> None
;;
