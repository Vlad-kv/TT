open Hw1;;
module StrSet = Set.Make(String);;

(* Проверить, находится ли лямбда-выражение в нормальной форме *)
let is_normal_form q = failwith "Not implemented";;

(* Выполнить один шаг бета-редукции, используя нормальный порядок *)
let normal_beta_reduction first = failwith "Not implemented";;

(* Свести выражение к нормальной форме с использованием нормального
   порядка редукции; реализация должна быть эффективной: использовать 
   мемоизацию *)
let reduce_to_normal_form first = failwith "Not implemented";;

let max x y = if (x < y) then y else x;;

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
	let rec substitute expr old_var new_var =
		match expr with
		  | Var str -> if str = old_var then
		  			  	Var new_var
		  			  else
		  			  	expr
		  | App(l1, l2) -> App(substitute l1 old_var new_var, substitute l2 old_var new_var)
		  | Abs(str, l1) -> if (str = old_var) then
		  						expr
		  					else
		  						Abs(str, substitute l1 old_var new_var)
	in
	let not_exist = get_list_of_not_ex_vars first second in

	let rec lok_compare_lambda_equ first second not_exist = 
		match first with
		  | Var str -> (second = first)
		  | App(l1_f, l2_f) -> 
		  		begin
		  			match second with
		  			  | App(l1_s, l2_s) ->
		  			    	if (second <> App(l1_s, l2_s) ) then
				  				false
				  			else
				  				((lok_compare_lambda_equ l1_f l1_s not_exist) && (lok_compare_lambda_equ l2_f l2_s not_exist))
		  			  | _ -> false
		  		end
		  | Abs(str_f, expr_f) ->
		  		begin
		  			match second with
		  			  | Abs(str_s, expr_s) ->
		  			  		lok_compare_lambda_equ
		  			  			(substitute expr_f str_f (List.hd not_exist))
		  			  			(substitute expr_s str_s (List.hd not_exist))
		  			  			(List.tl not_exist)
		  			  | _ -> false
		  		end
	in
	lok_compare_lambda_equ first second not_exist
;;

let rec get_free_vars expr locked_vars =
	match expr with
	  | Var str ->
	  		if (StrSet.mem str locked_vars) then
	  			StrSet.empty
	  		else
	  			StrSet.singleton str
	  | App(expr1, expr2) -> StrSet.union (get_free_vars expr1 locked_vars) (get_free_vars expr2 locked_vars)
	  | Abs(str, expr) ->
	  		get_free_vars expr (StrSet.add str locked_vars)
;;

let rec free_vars expr = StrSet.elements (get_free_vars expr StrSet.empty);;

let free_to_subst substitute where_to_substitute var =
	let forbidden_vars = get_free_vars substitute StrSet.empty in
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
