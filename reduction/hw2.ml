open Hw1;;
module StrSet = Set.Make(String);;

let max x y = if (x < y) then y else x;;

let rec substitute expr old_var new_expr =
	match expr with
	  | Var str -> if str = old_var then
	  			  	new_expr
	  			  else
	  			  	expr
	  | App(l1, l2) -> App(substitute l1 old_var new_expr, substitute l2 old_var new_expr)
	  | Abs(str, l1) -> if (str = old_var) then
	  						expr
	  					else
	  						Abs(str, substitute l1 old_var new_expr)
;;

let is_alpha_equivalent first second =
	let rec get_all_existing_vars l =
		match l with
		  | Var str -> StrSet.singleton str
		  | App(expr1, expr2) -> StrSet.union (get_all_existing_vars expr1) (get_all_existing_vars expr2)
		  | Abs(str, expr) -> StrSet.add str (get_all_existing_vars expr)
	in
	let rec calc_depth l = 
		match l with
		  | Var str -> 0
		  | App(expr1, expr2) -> max (calc_depth expr1) (calc_depth expr2)
		  | Abs(str, expr) -> calc_depth expr + 1
	in
	let get_list_of_not_ex_vars l1 l2 = 
		let s = StrSet.union (get_all_existing_vars l1) (get_all_existing_vars l2) in
		let check_if_present no s = StrSet.mem ("a" ^ string_of_int no) s in
		let rec build_list set res next to_add =
			if (to_add == 0) then
				res
			else
				if (check_if_present next set) then
					build_list set res (next + 1) to_add
				else
					begin
						build_list set (("a" ^ string_of_int next) :: res) (next + 1) (to_add - 1)
					end
		in
		build_list s [] 0 (max (calc_depth l1) (calc_depth l2))
	in

	let not_exist = get_list_of_not_ex_vars first second in

	let rec lok_compare_lambda_equ first second not_exist = 
		match first with
		  | Var str -> (second = first)
		  | App(l1_f, l2_f) -> 
		  		begin
		  			match second with
		  			  | App(l1_s, l2_s) ->
				  			((lok_compare_lambda_equ l1_f l1_s not_exist) && (lok_compare_lambda_equ l2_f l2_s not_exist))
		  			  | _ -> false
		  		end
		  | Abs(str_f, expr_f) ->
		  		begin
		  			match second with
		  			  | Abs(str_s, expr_s) ->
		  			  		lok_compare_lambda_equ
		  			  			(substitute expr_f str_f (Var (List.hd not_exist)))
		  			  			(substitute expr_s str_s (Var (List.hd not_exist)))
		  			  			(List.tl not_exist)
		  			  | _ -> false
		  		end
	in
	lok_compare_lambda_equ first second not_exist
;;

let rec get_set_of_free_vars expr locked_vars =
	match expr with
	  | Var str ->
	  		if (StrSet.mem str locked_vars) then
	  			StrSet.empty
	  		else
	  			StrSet.singleton str
	  | App(expr1, expr2) -> StrSet.union (get_set_of_free_vars expr1 locked_vars) (get_set_of_free_vars expr2 locked_vars)
	  | Abs(str, expr) ->
	  		get_set_of_free_vars expr (StrSet.add str locked_vars)
;;

let rec free_vars expr = StrSet.elements (get_set_of_free_vars expr StrSet.empty);;

let free_to_subst substituted where_to_substitute var =
	let forbidden_vars = get_set_of_free_vars substituted StrSet.empty in
	let rec check expr = (*0 - всё хорошо, 1 - в expr входит свободно var, 2 - свободное вхождение связалось*)
		match expr with
		  | Var str ->
		  		if (str = var) then 1
		  		else 0
		  | App(expr1, expr2) -> max (check expr1) (check expr2)
		  | Abs(str, expr) ->
		  		if (str = var) then 0
		  		else
			  		begin
			  			let res = check expr in
			  			match res with
			  			  | 1 ->
			  			  		if (StrSet.mem str forbidden_vars) then 2
			  			  		else 1
			  			  | _ -> res
			  		end
	in
	if ((check where_to_substitute) = 2) then false
	else true
;;

(* Проверить, находится ли лямбда-выражение в нормальной форме *)
let rec is_normal_form expr =
	match expr with
	  | App(Abs(var, expr_1), expr_2) ->
	  		not (free_to_subst expr_2 expr_1 var)
	  | App(expr_1, expr_2) ->
	  		(is_normal_form expr_1) && (is_normal_form expr_2)
	  | Abs(var, expr) -> is_normal_form expr
	  | Var(var) -> true
;;

(* Выполнить один шаг бета-редукции, используя нормальный порядок *)
let normal_beta_reduction expr = 
	let rec lok_reduction expr = 
		let app_reduction expr_1 expr_2 = 
			let res_1 = lok_reduction expr_1 in
			let res_2 = lok_reduction expr_2 in
			if ((snd res_1) == true) then
				(App((fst res_1), expr_2), true)
			else
				if ((snd res_2) == true) then
	  				(App(expr_1, (fst res_2)), true)
	  			else
	  				(App(expr_1, expr_2), false)
		in
		match expr with
		  | App(Abs(var, expr_1), expr_2) ->
		  		if (free_to_subst expr_2 expr_1 var) then
		  			((substitute expr_1 var expr_2), true)
		  		else
		  			app_reduction (Abs(var, expr_1)) expr_2
		  | App(expr_1, expr_2) -> app_reduction expr_1 expr_2
		  | Abs(var, expr) ->
		  		let res = lok_reduction expr in
		  		if ((snd res) == true) then
		  			(Abs(var, (fst res)), true)
		  		else
		  			(Abs(var, expr), false)
		  | Var(var) -> (Var(var), false)
	in
	(fst (lok_reduction expr))
;;

module StrMap = Map.Make(String);;

let string_of_var var = 
	if ((snd var) = 0) then
		(Char.escaped  (fst var))
	else
		(Char.escaped  (fst var)) ^ (string_of_int (snd var))
;;
let next_var var = 
	if ((fst var) < 'z') then
		(Pervasives.char_of_int ((Pervasives.int_of_char (fst var)) + 1), (snd var))
	else
		('a', (snd var) + 1)
;;
let rec get_next_var var used_vars =
	let new_var = next_var var in
	if (StrSet.mem (string_of_var new_var) used_vars) then
		get_next_var new_var used_vars
	else
		new_var
;;
let rec build_maps vars number_of_similar_vars new_vars used_vars next_var = 
	if (vars = []) then
		((number_of_similar_vars, new_vars), next_var)
	else
		build_maps (List.tl vars)
			(StrMap.add (List.hd vars) 1 number_of_similar_vars)
			(StrMap.add ("1#" ^ (List.hd vars)) (string_of_var next_var) new_vars)
			used_vars
			(get_next_var next_var used_vars)
;;
let get_number_of_sim_vars var number_of_similar_vars = 
	if (StrMap.mem var number_of_similar_vars) then
		StrMap.find var number_of_similar_vars
	else
		0
;;
let rec lock_unify expr number_of_similar_vars new_vars used_vars next_var =
	match expr with
	  | App(expr_1, expr_2) ->
	  		let res_1 = lock_unify expr_1 number_of_similar_vars new_vars used_vars next_var in
	  		let res_2 = lock_unify expr_2 number_of_similar_vars new_vars used_vars (snd res_1) in
	  		(App((fst res_1), (fst res_2)), (snd res_2))
	  | Abs(var, expr) ->
	  		let number = (get_number_of_sim_vars var number_of_similar_vars) + 1 in
	  		let new_number_of_similar_vars = StrMap.add var number number_of_similar_vars in
	  		let new_new_vars = StrMap.add ((string_of_int number) ^ "#" ^ var) (string_of_var next_var) new_vars in
	  		let res = lock_unify expr new_number_of_similar_vars new_new_vars used_vars (get_next_var next_var used_vars) in
	  		(Abs(string_of_var next_var, (fst res)), (snd res))
	  | Var(var) ->
			let number = get_number_of_sim_vars var number_of_similar_vars in
	  		(Var(StrMap.find ((string_of_int number) ^ "#" ^ var) new_vars), next_var)
;;
let rec alpha_equ_build_maps vars number_of_similar_vars new_vars =
	if (vars = []) then
		(number_of_similar_vars, new_vars)
	else
		alpha_equ_build_maps (List.tl vars)
			(StrMap.add (List.hd vars) 1 number_of_similar_vars)
			(StrMap.add ("1#" ^ (List.hd vars)) (List.hd vars) new_vars)
;;

let unify_varaible_names expr = 
	let res_1 = build_maps (free_vars expr) StrMap.empty StrMap.empty StrSet.empty ('a', 0) in
	let maps = fst res_1 in
	let res_2 = lock_unify expr (fst maps) (snd maps) StrSet.empty (snd res_1) in
	(fst res_2)
;;
let alpha_equ_unification expr = 
	let set = get_set_of_free_vars expr StrSet.empty in
	let res_1 = alpha_equ_build_maps (StrSet.elements set) StrMap.empty StrMap.empty in
	let res_2 = lock_unify expr (fst res_1) (snd res_1) set ('a', 0) in
	(fst res_2)
;;

(* Свести выражение к нормальной форме с использованием нормального
   порядка редукции; реализация должна быть эффективной: использовать 
   мемоизацию *)
let reduce_to_normal_form first = failwith "---"
;;


