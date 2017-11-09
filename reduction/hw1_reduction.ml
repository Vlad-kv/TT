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

(* Возвращает list из свободных переменных. *)
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
(* Выдаёт следующую поле var неиспользованную переменную.*)
let rec get_next_var var used_vars =
	let new_var = next_var var in
	if (StrSet.mem (string_of_var new_var) used_vars) then
		get_next_var new_var used_vars
	else
		new_var
;;
(* По map-у (ответственному за хранение информации за количестве переменных) и имени переменной получает 
  количество этих переменных.
*)
let get_number_of_sim_vars var number_of_similar_vars = 
	if (StrMap.mem var number_of_similar_vars) then
		StrMap.find var number_of_similar_vars
	else
		0
;;
(* Принимает:
	- expr - выражение, которое хочется привести к общему виду;
	- number_of_similar_vars - map из string в int - хранит информацию о количестве одинаковых переменных;
	- new_vars - map из string в string - отображение вида number#var -> new_name_of_var;
	- used_vars - set из использованных переменных;
	- next_var - переменная, начиная с которой будут подбираться новые переменные;
	
		Цели - преобразовать expr к общему виду, который зависит только от его структуры и соответствующих входных параметров,
	кроме того общий вид не должен иметь переменные с переиспользованными названиями (если только used_vars не сделает это невозможным,
	но в таких случаях lock_unify не употребляется).
		Отображение вида number#var -> new_name_of_var сделано для работы с вложенным переиспользованием имён
	(например (\x.(\x.(\x.x)x)x) ) - то есть "количество одинаковых переменных" - уровень вложенности соответствующей переменной в данный момент.
	Для каждой переменной можно легко посчитать уровень вложенности и по нему найти соответствующее отображение.
	
	Возвращает: (new_expr, new_next_var) - пару из преобразованного выражения и новой переменной с которой начнётся подбор.
*)
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
(* Преобразует выражение в стандартизированный вид (сохраняя структуру), переименовывает в том числе и глобальные переменные. *)
let unify_varaible_names expr = 
	(* По list-у из глобальных переменных строит number_of_similar_vars и new_vars для lock_unify, где глобальным переменным присваевается
	  уровень вложенности 1 (в формате как и у lock_unify).
	   Возвращает ((new_number_of_similar_vars, new_new_vars), new_next_var) - итоговые map-ы и переменная, с которой начнётся подбор.
	*)
	let rec build_maps vars number_of_similar_vars new_vars next_var = 
		if (vars = []) then
			((number_of_similar_vars, new_vars), next_var)
		else
			build_maps (List.tl vars)
				(StrMap.add (List.hd vars) 1 number_of_similar_vars)
				(StrMap.add ("1#" ^ (List.hd vars)) (string_of_var next_var) new_vars)
				(get_next_var next_var StrSet.empty)
	in
	let res_1 = build_maps (free_vars expr) StrMap.empty StrMap.empty ('a', 0) in
	let maps = fst res_1 in
	let res_2 = lock_unify expr (fst maps) (snd maps) StrSet.empty (snd res_1) in
	(fst res_2)
;;
(* Далает то же, что и unify_varaible_names, но с условием что новое выражение останется альфа-эквивалентным сторому (то есть
  переименовывает только связанные переменные).
   Возвращает (new_expr, new_next_var).*)
let full_alpha_equ_unification expr = 
	(* То же, что и build_maps в unify_varaible_names, но оставляет имена глобальных переменных оригинальными.
	   Возвращает (new_number_of_similar_vars, new_new_vars). *)
	let rec alpha_equ_build_maps vars number_of_similar_vars new_vars =
		if (vars = []) then
			(number_of_similar_vars, new_vars)
		else
			alpha_equ_build_maps (List.tl vars)
				(StrMap.add (List.hd vars) 1 number_of_similar_vars)
				(StrMap.add ("1#" ^ (List.hd vars)) (List.hd vars) new_vars)
	in
	let set = get_set_of_free_vars expr StrSet.empty in
	let res_1 = alpha_equ_build_maps (StrSet.elements set) StrMap.empty StrMap.empty in
	lock_unify expr (fst res_1) (snd res_1) set (get_next_var ('z', -1) set)
;;
let alpha_equ_unification_of_names expr = fst (full_alpha_equ_unification expr);;

(* Порядок на lambda. Имена переменных не могут состоять из пустой строки. *)
module Ord_lambda = struct
	type t = lambda
	(* Возвращает (res, upd_global_map_1, upd_global_map_2, new_n_var). *)
	let rec lok_compare  lambda_1 lambda_2 lokal_map_1 lokal_map_2 global_map_1 global_map_2 n_var = 
		match (lambda_1, lambda_2) with
		  | (Var(v_1), Var(v_2)) ->
		  	begin
		  		let get_name var map =
		  			if (StrMap.mem var map) then
		  				StrMap.find var map
		  			else
		  				""
		  		in
		  		let comp_vars var_1 var_2 = (* "" < var *)
		  			match (var_1, var_2) with
		  			  | ("", var) -> -1
			  		  | (var, "") -> 1
			  		  | (var_1, var_2) ->
			  		  		if (var_1 = var_2) then      0
			  		  		else if (var_1 < var_2) then -1
			  		  		else 					     1
		  		in
		  		let lok_1 = get_name v_1 lokal_map_1 in
		  		let lok_2 = get_name v_2 lokal_map_2 in
		  		match (lok_1, lok_2) with
		  		  | ("", "") ->
		  		  	begin
		  		  		let glob_1 = get_name v_1 global_map_1 in
		  		  		let glob_2 = get_name v_2 global_map_2 in
		  		  		match (glob_1, glob_2) with
		  		  		  | ("", "") -> 
		  		  		  	begin
		  		  		  		let global_map_1 = StrMap.add v_1 (string_of_var n_var) global_map_1 in
		  		  		  		let global_map_2 = StrMap.add v_2 (string_of_var n_var) global_map_2 in
		  		  		  		(0, global_map_1, global_map_2, next_var n_var)
		  		  		  	end
		  		  		  | (var_1, var_2) -> (comp_vars var_1 var_2, global_map_1, global_map_2, n_var)
		  		  	end
		  		  | (var_1, var_2) -> (comp_vars var_1 var_2, global_map_1, global_map_2, n_var)
		  	end
		  | (Abs(v_1, l_1), Abs(v_2, l_2)) ->
		  	begin
		  		let lokal_map_1 = StrMap.add v_1 (string_of_var n_var) lokal_map_1 in
		  		let lokal_map_2 = StrMap.add v_2 (string_of_var n_var) lokal_map_2 in
		  		lok_compare l_1 l_2 lokal_map_1 lokal_map_2 global_map_1 global_map_2 (next_var n_var)
		  	end
		  | (App(l_11, l_12), App(l_21, l_22)) ->
		  	begin
		  		match (lok_compare l_11 l_21 lokal_map_1 lokal_map_2 global_map_1 global_map_2 n_var) with
		  		  (res, upd_global_map_1, upd_global_map_2, new_n_var) ->
	  		 		if (res <> 0) then
	  		 			(res, upd_global_map_1, upd_global_map_2, new_n_var)
	  		 		else
	  		 		    (lok_compare l_12 l_22 lokal_map_1 lokal_map_2 upd_global_map_1 upd_global_map_2 new_n_var)
		  	end
		  | (Var(v_1), Abs(v_2, l_2)) -> (-1, global_map_1, global_map_2, n_var)
		  | (Var(v_1), App(l_21, l_22)) -> (-1, global_map_1, global_map_2, n_var)
		  | (Abs(v_1, l_1), App(l_21, l_22)) -> (-1, global_map_1, global_map_2, n_var)
		  | _ -> (1, global_map_1, global_map_2, n_var)
	;;
	(* Var < Abs < App *)
	let compare lambda_1 lambda_2 =
		match (lok_compare lambda_1 lambda_2 StrMap.empty StrMap.empty StrMap.empty StrMap.empty ('a', 0)) with
		  (res, upd_global_map_1, upd_global_map_2, new_n_var) -> res
	;;
end;;

module LambdaMap = Map.Make(Ord_lambda);;

(* Свести выражение к нормальной форме с использованием нормального
   порядка редукции; реализация должна быть эффективной: использовать 
   мемоизацию *)
let reduce_to_normal_form expr =
	(* По двум структурно эквивалентным выражениям строит отображение из имён первого выражения во второе, при этом в первом выражении все
	   переменные должны иметь различные имена. *)
	let rec get_map_of_vars expr_1 expr_2 map =
		match (expr_1, expr_2) with
		  | (App(expr_1_1, expr_1_2), App(expr_2_1, expr_2_2)) ->
		  		let res = get_map_of_vars expr_1_1 expr_2_1 map in
		  		get_map_of_vars expr_1_2 expr_2_2 res
		  | (Abs(var_1, expr_1), Abs(var_2, expr_2)) ->
		  		if (StrMap.mem var_1 map) then
		  			failwith ("there are some different variables with the same name : " ^ var_1 ^ " (in get_map_of_vars)")
		  		else
		  			get_map_of_vars expr_1 expr_2 (StrMap.add var_1 var_2 map)
		  | (Var(var_1), Var(var_2)) ->
		  		if ((StrMap.mem var_1 map) && ((StrMap.find var_1 map) <> var_2)) then
		  			failwith ("there are some different variables with the same name : " ^ var_1 ^ " (in get_map_of_vars)")
		  		else
		  			StrMap.add var_1 var_2 map
		  | _ -> failwith "expressions not equivalent"
	in
	let rec rename_vars expr map = 
		let find var map =
			if (StrMap.mem var map) then StrMap.find var map
			else 					var
		in
		match expr with
		  | App(expr_1, expr_2) -> App(rename_vars expr_1 map, rename_vars expr_2 map)
		  | Abs(var, expr)      -> Abs((find var map), rename_vars expr map)
		  | Var(var)            -> Var(find var map)
	in
	(* Принимает:
	  - orig_expr - выражение, которое надо отредуцировать;
	  - memory - map из lambda в (lambda, lambda) - 
	      если какое-либо выражение (expr) когда-то было полностью отредуцированно, то в memory для expr будет храниться отображение
	      в (результат редукции expr типа lambda, expr);
	  - used_global_vars - использованные (глобальные) переменные (нужны для substitute_with_renaming);
	  - next_var - переменная, начиная с которой будт подбираться новые уникальные переменные;
	  - is_prev_was_app - истина, если сейчас редуцируется некоторое подвыражение, которое стояло в оригинальном в левой части аппликации - если
	      выражение, редуцируемое сейчас, в какой-то момент станет абстракцией, необходимо остановить редукцию - оно может не иметь нормальной
	      формы, а после подстановки она может появиться;
	  Основная функция. Редуцирует, обновляет memory и т.д.

	  Возвращает: (new_expr, new_memory, new_next_var, is_it_fully_reducted), где is_it_fully_reducted - отредуцировали ли выражение до конца.
	*)
	let rec lok_reduction orig_expr memory used_global_vars next_var is_prev_was_app =
		(* Если данное выражение раньше отредуцировалось, то возвращает Some(результат), иначе - None. *)
		let lok_try_to_find expr memory = 
			if (LambdaMap.mem expr memory) then
				match (LambdaMap.find expr memory) with
				  (reducted_expr, key_lambda) ->
				begin
		  			match (Ord_lambda.lok_compare expr key_lambda StrMap.empty StrMap.empty StrMap.empty StrMap.empty ('a', 0)) with
		  			  (res, expr_global_map, key_lambda_global_map, new_n_var) ->
		  			begin
		  				assert(res == 0);
		  				let inverse_map map =
		  					let rec map_of_list l = 
		  						if (l = []) then
		  							StrMap.empty
		  						else
		  							let res = map_of_list (List.tl l) in
		  							let pair = List.hd l in
		  							StrMap.add (snd pair) (fst pair) res
		  					in
		  					map_of_list (StrMap.bindings map)
		  				in
		  				let inv_expr_map = inverse_map expr_global_map in
		  				let upd_map var = StrMap.find var inv_expr_map in
		  				let composed_map = StrMap.map upd_map key_lambda_global_map in
		  				let rec rename_global_vars expr map =
		  					match expr with
		  					  | Var(var) ->
		  					  		if (StrMap.mem var map) then
		  					  			Var(StrMap.find var map)
		  					  		else
		  					  			Var(var)
		  					  | App(expr_1, expr_2) -> 
		  					  		App(rename_global_vars expr_1 map, rename_global_vars expr_2 map)
		  					  | Abs(var, expr_1) ->
		  					  		Abs(var, rename_global_vars expr_1 (StrMap.remove var map))
		  				in
		  				Some(rename_global_vars reducted_expr composed_map)
		  			end
		  		end
	  		else
	  			None
		in
		(* Если данное выражение раньше отредуцировалось, то возвращает результат, иначе - возвращает его самого. *)
		let try_to_find expr memory =
			match (lok_try_to_find expr memory) with
			  | None -> expr
			  | Some(res) -> res
		in
		(* Выполняет подстановку и заодно переименовывает связанные переменные при каждой подстановке в new_expr для того, чтобы не было повторяющихся
		   имён переменных.
		   Возвращает: (new_expr, new_next_var) *)
		let substitute_with_renaming expr var new_expr next_var used_vars =
			let rec get_map_for_renaming expr next_var res_map =
				match expr with
				  | App(expr_1, expr_2) ->
				  		let res_1 = get_map_for_renaming expr_1 next_var res_map in
				  		get_map_for_renaming expr_2 (snd res_1) (fst res_1)
				  | Abs(var, expr) ->
				  		if (StrMap.mem var res_map) then
				  			failwith ("there are some different variables with the same name : " ^ var ^ " (in get_map_for_renaming)")
				  		else
				  			let new_var = get_next_var next_var used_vars in
				  			get_map_for_renaming expr new_var (StrMap.add var (string_of_var new_var) res_map)
				  | Var(var) ->
				  		let ret_map = 
				  			if (not (StrMap.mem var res_map)) then StrMap.add var var res_map
				  			else 							  res_map
				  		in
				  		(ret_map, next_var)
			in
			let rec substitute expr var_to_s new_expr next_var =
				match expr with
				  | App(expr_1, expr_2) ->
				  		let res_1 = substitute expr_1 var_to_s new_expr next_var in
				  		let res_2 = substitute expr_2 var_to_s new_expr (snd res_1) in
				  		(App(fst res_1, fst res_2), snd res_2)
				  | Abs(var, expr) -> 
				  		if (var = var_to_s) then
				  			failwith ("there are some different variables with the same name : " ^ var ^ " (in substitute in lok_reduction)")
				  		else
				  			let res = substitute expr var_to_s new_expr next_var in
				  			(Abs(var, (fst res)), snd res)
				  | Var(var) ->
				  		if (var = var_to_s) then
				  			let res_1 = get_map_for_renaming new_expr next_var StrMap.empty in
				  			let res_expr = rename_vars new_expr (fst res_1) in
				  			(res_expr, (snd res_1))
				  		else
				  			(Var(var), next_var)
			in
			substitute expr var new_expr next_var
		in
		(* Принимает:
		   - orig_expr - оригинальное выражение, которое надо было отредуцировать (прямо из lok_reduction);
		   - to_ret - (new_expr, new_memory, new_next_var, is_it_fully_reducted) - то самое значение, которое готово отправится вызывавшему
		       lok_reduction, но прежде чем отправить, если new_expr отредуцирован до конца, то добавим в memory соосветствующую запись, иначе-
		       вернём что и собирались.
		   Возвращает: (new_expr, updated_new_memory, new_next_var, is_it_fully_reducted)
		*)
		let upd_memory orig_expr to_ret =
			match to_ret with
			  (res_expr, new_memory, new_next_var, is_it_fully_reducted) ->
			begin
				if (is_it_fully_reducted) then
					(res_expr, LambdaMap.add orig_expr (res_expr, orig_expr) new_memory, new_next_var, is_it_fully_reducted)
				else
					to_ret
			end
		in
		match (lok_try_to_find orig_expr memory) with
		  | Some(res) -> (res, memory, next_var, true)
		  | None ->
		  begin
			match orig_expr with
			  | App(Abs(var, expr_1), expr_2) ->
			  		let expr_2 = try_to_find expr_2 memory in
			  		let expr_1 = try_to_find expr_1 memory in
			  		let subst_expr_res = (substitute_with_renaming expr_1 var expr_2 next_var used_global_vars) in
			  		let to_ret = lok_reduction (fst subst_expr_res) memory used_global_vars (snd subst_expr_res) is_prev_was_app in
			  		upd_memory orig_expr to_ret
			  | App(expr_1, expr_2) ->
			  	begin
			  		let res_1 = lok_reduction expr_1 memory used_global_vars next_var true in
			  		match res_1 with
			  		  (new_expr, new_memory, new_next_var, is_it_fully_reducted) ->
				  		let to_ret = 
				  			match new_expr with
				  			  | Abs(var, enclosed_expr) ->
				  			  		lok_reduction (App(new_expr, expr_2)) new_memory used_global_vars new_next_var is_prev_was_app
				  			  | _ ->
				  			  		let res_2 = lok_reduction expr_2 new_memory used_global_vars new_next_var false in
				  			  		match res_2 with
				  			  		  (new_expr_2, new_memory, new_next_var, is_it_fully_reducted) ->
				  			  		    (App(new_expr, new_expr_2), new_memory, new_next_var, is_it_fully_reducted)
					  	in
					  	upd_memory orig_expr to_ret
				end
			  | Abs(var, expr) ->
			 	begin
			  		if (is_prev_was_app) then
			  			(Abs(var, expr), memory, next_var, is_normal_form expr)
			  		else
			  			match (lok_reduction expr memory used_global_vars next_var false) with
			  			  (new_expr, new_memory, new_next_var, is_it_fully_reducted) ->
				  			let to_ret = (Abs(var, new_expr), new_memory, new_next_var, is_it_fully_reducted) in
				  			upd_memory orig_expr to_ret
				end
			  | Var(var) ->
			  		(orig_expr, memory, next_var, true)
		  end
	in
	let res_1 = full_alpha_equ_unification expr in
	let res_2 = (lok_reduction (fst res_1) LambdaMap.empty (get_set_of_free_vars (fst res_1) StrSet.empty) (snd res_1) false) in
	match res_2 with
	  (new_expr, new_memory, new_next_var, is_it_fully_reducted) ->
	 	begin
	 		(* let print key expr =
				print_string(key ^ " : " ^ (string_of_lambda expr) ^ "\n")
			in
			StrMap.iter print new_memory); *)
			new_expr
	 	end
;;
