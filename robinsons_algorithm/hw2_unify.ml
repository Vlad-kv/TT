type algebraic_term = Var of string | Fun of string * (algebraic_term list)

module Unique_name_getter = struct
    module StrSet = Set.Make(String);;
    type getter = {
        existing_names: StrSet.t;
        mutable prev_name: int;
    };;
    let create_getter set = {existing_names = set; prev_name = 0;};;
    let rec get_set_of_existing_names term =
    	let rec set_of_list l =
    		if (l = []) then
    		    StrSet.empty
    		else
                StrSet.union (get_set_of_existing_names (List.hd l)) (set_of_list (List.tl l))
    	in
        match term with
          | Var(str) -> StrSet.add str StrSet.empty
          | Fun(str, l) -> StrSet.add str (set_of_list l)
    ;;
    let create_getter_from_term term = create_getter (get_set_of_existing_names term);;
    let get_next g = 
    	let rec get_first_possible set var = 
    		if (StrSet.mem ("f" ^ (string_of_int var)) set) then
    			get_first_possible set (var + 1)
    		else
    			var
    	in
    	g.prev_name <- get_first_possible g.existing_names (g.prev_name + 1);
    	"f" ^ (string_of_int g.prev_name)
    ;;
end;;

module StrSet = Set.Make(String);;
module StrMap = Map.Make(String);;

let rec string_of_algebraic_term term =
	let rec list_to_string l =
		if (l == []) then
			""
		else
			(string_of_algebraic_term (List.hd l)) ^ " " ^ (list_to_string (List.tl l))
	in
	match term with
      | Var(str) -> str
	  | Fun(str, l) -> "(" ^ str ^ " " ^ (list_to_string l) ^ ")"
;;

let system_to_equation list_of_pairs =
	let rec get_set_of_names list_of_pairs = 
		if (list_of_pairs = []) then
			StrSet.empty
		else
			let pair = List.hd list_of_pairs in
			StrSet.union
				(StrSet.union
					(Unique_name_getter.get_set_of_existing_names (fst pair))
					(Unique_name_getter.get_set_of_existing_names (snd pair))
				)
				(get_set_of_names (List.tl list_of_pairs))
	in
	let set_of_names = get_set_of_names list_of_pairs in
	let unique_name = Unique_name_getter.get_next (Unique_name_getter.create_getter set_of_names) in
	let rec build_lists list_of_pairs =
		if (list_of_pairs = []) then
			([], [])
		else
			let head = List.hd list_of_pairs in
			let res = build_lists (List.tl list_of_pairs) in
			(((fst head) :: (fst res)), ((snd head) :: (snd res)))
	in
	let res = build_lists list_of_pairs in
	(Fun(unique_name, (fst res)), Fun(unique_name, (snd res)))
;;

let rec map_of_list_solution rules = 
	if (rules = []) then
		StrMap.empty
	else
		let first = List.hd rules in
		StrMap.add (fst first) (snd first) (map_of_list_solution (List.tl rules))
;;

let rec apply_substitution_with_map rules term =
	let rec subst_in_list rules l =
		if (l == []) then
			[]
		else
			(apply_substitution_with_map rules (List.hd l)) :: (subst_in_list rules (List.tl l))
	in
	match term with
	  | Var(str) ->
	  		if (StrMap.mem str rules) then
	  			StrMap.find str rules
	  		else
	  			Var(str)
	  | Fun(str, l) -> Fun(str, (subst_in_list rules l))
;;

let apply_substitution rules term = apply_substitution_with_map (map_of_list_solution rules) term;;

let rec check_solution_with_map solution system =
	let rec check_equation solution pair =
		(apply_substitution_with_map solution (fst pair)) = (apply_substitution_with_map solution (snd pair))
	in
	if (system = []) then
		true
	else
		let res = check_equation solution (List.hd system) in
		if (res == true) then
			check_solution_with_map solution (List.tl system)
		else
			false
;;

let check_solution solution system = check_solution_with_map (map_of_list_solution solution) system;;

module DisjointSet = struct
    module StrMap = Map.Make(String);;
    type disjoint_set = {
        mutable disp: string StrMap.t;
    };;
    let create = {disp = StrMap.empty;};;
    let clear disjoint_set = disjoint_set.disp <- StrMap.empty;;
    let iter func disj_set = StrMap.iter func disj_set.disp;;
    let get_leader var disj_set = 
    	let rec search var disj_set = 
    		let in_pair = (StrMap.find var disj_set.disp) in
    		if (in_pair = var) then
    			var
    		else
    			begin
    				let res = search in_pair disj_set in
    				disj_set.disp <- (StrMap.add var res disj_set.disp);
    				res
    			end
    	in
    	if (StrMap.mem var disj_set.disp) then
    		search var disj_set
	    else
	    	begin
	    		disj_set.disp <- (StrMap.add var var disj_set.disp);
	    		var
	    	end
	;;
	let add_link var_1 var_2 disj_set =
		assert(((get_leader var_1 disj_set) = var_1) && ((get_leader var_2 disj_set) = var_2));
		disj_set.disp <- (StrMap.add var_1 var_2 disj_set.disp)
	;;
	let rec update_to_leaders term disj_set =
		let rec upd_list l disj_set =
			if (l = []) then
				[]
			else
				(update_to_leaders (List.hd l) disj_set) :: (upd_list (List.tl l) disj_set)
		in
		match term with
		  | Var(str) -> Var(get_leader str disj_set)
		  | Fun(f, l) -> Fun(f, (upd_list l disj_set))
	;;
	let rec get_not_trivial_pairs disj_set =
		let modify value = get_leader value disj_set in
		let res = StrMap.map modify disj_set.disp in
		let filter key value = (key <> value) in
		let res = StrMap.filter filter res in
		let modify value = Var(value) in
		StrMap.map modify res
	;;
end;;

module Data = struct
	module StrSet = Set.Make(String);;
	module StrMap = Map.Make(String);;
	type data = {
		disjoint_set: DisjointSet.disjoint_set;
		mutable equations: algebraic_term StrMap.t;
		mutable to_calculate: (algebraic_term * algebraic_term) list;
	};;
	let create l = 
		let clear data =
			DisjointSet.clear data.disjoint_set;
			data.equations <- StrMap.empty;
			data.to_calculate <- [];
		in
		let res = {
			disjoint_set = DisjointSet.create;
			equations = StrMap.empty;
			to_calculate = [];
		} in
		clear res;
		res.to_calculate <- l;
		res
	;;
	let print_state data =
		print_string "\ndisjoint_set:\n";
		let lok_print first second =
			print_string ("  " ^ first ^ " -> " ^ second ^ "\n")
		in
		DisjointSet.iter lok_print data.disjoint_set;
		print_string "equations:\n";
		let lok_print var term = 
			print_string ("  " ^ var ^ " = " ^ (string_of_algebraic_term term) ^ "\n");
		in
		StrMap.iter lok_print data.equations;
		let rec print_calculate l = 
			if (l <> []) then
				begin
					let head = List.hd l in
					print_string (
						"  " ^
						(string_of_algebraic_term (fst head)) ^
						" = " ^
						(string_of_algebraic_term (snd head)) ^
						"\n"
					);
					print_calculate (List.tl l)
				end
		in
		print_string "to_calculate:\n";
		print_calculate data.to_calculate;
		print_string "--------\n"
	;;
	let extract_head data =
		let res = List.hd data.to_calculate in
		data.to_calculate <- (List.tl data.to_calculate);
		res
	;;
	let get_to_calculate data = data.to_calculate;;
	let add_equation_to_calculate pair data = data.to_calculate <- pair :: data.to_calculate;;

	let rec calc_var_term var_1 term data = 
		let var_1 = DisjointSet.get_leader var_1 data.disjoint_set in
		if (StrMap.mem var_1 data.equations) then
			let main_val = StrMap.find var_1 data.equations in
			data.to_calculate <- (main_val, term) :: data.to_calculate
		else
			data.equations <- StrMap.add var_1 term data.equations
	;;
	let get_leader var data = DisjointSet.get_leader var data.disjoint_set;;
	let add_link var_1 var_2 data comparator =
		let upd leader_1 leader_2 data = 
			if (StrMap.mem leader_1 data.equations) then
				begin
					calc_var_term leader_2 (StrMap.find leader_1 data.equations) data;
					data.equations <- (StrMap.remove leader_1 data.equations)
				end;
			DisjointSet.add_link leader_1 leader_2 data.disjoint_set
		in
		let var_1 = DisjointSet.get_leader var_1 data.disjoint_set in
		let var_2 = DisjointSet.get_leader var_2 data.disjoint_set in
		if (comparator var_2 var_1) then
			upd var_1 var_2 data
		else
			if (var_1 <> var_2) then
				upd var_2 var_1 data
	;;
	let update_to_leaders data =
		assert(data.to_calculate = []);
		let convert term = DisjointSet.update_to_leaders term data.disjoint_set in
		data.equations <- (StrMap.map convert data.equations)
	;;
	type result = {
		mutable map: algebraic_term StrMap.t;
		mutable is_it_fail: bool;
	};;
	let create_solution_from_equations data =
		let rec restore_var result var used_vars equations =
			if (StrMap.mem var result.map) then
				Some (StrMap.find var result.map)
			else if (StrSet.mem var used_vars) then
				None
			else if (not (StrMap.mem var equations)) then
				Some (Var(var))
			else
				let used_vars = StrSet.add var used_vars in
				let term = StrMap.find var equations in
				let res = restore_term result term used_vars equations in
				match res with
				  | None -> None
				  | Some not_none ->
				  		begin
							result.map <- StrMap.add var not_none result.map;
							Some not_none
						end
		and restore_term result term used_vars equations =
			match term with
			  | Var(str) -> restore_var result str used_vars equations
			  | Fun(f, l) ->
			  		let res = restore_list result l used_vars equations in
			  		match res with
			  		  | None -> None
			  		  | Some not_none -> Some (Fun(f, not_none))
		and restore_list result l used_vars equations = 
			if (l = []) then
				Some []
			else
				begin
					let res_1 = restore_term result (List.hd l) used_vars equations in
					let res_2 = restore_list result (List.tl l) used_vars equations in
					match (res_1, res_2) with
					  | ((Some not_none_1), (Some not_none_2)) -> Some (not_none_1 :: not_none_2)
					  | _ -> None
				end
		in
		let result = {
			map = StrMap.empty;
			is_it_fail = false;
		} in
		let func key unused =
			if (not (StrMap.mem key result.map)) then
				begin
					let res = restore_var result key StrSet.empty data.equations in
					if (res = None) then
						result.is_it_fail <- true
				end
		in
		let choice key val_1 val_2 =
			match (val_1, val_2) with
			  | (None, None) -> None
			  | (Some(v_1), None) -> Some(v_1)
			  | (None, Some(v_2)) -> Some(v_2)
			  | (Some(v_2), Some(v_1)) ->
			  		begin
			  			print_string ((string_of_algebraic_term v_2) ^ " " ^ (string_of_algebraic_term v_1) ^ "\n");
			  			assert(false);
			  			None
			  		end
		in
		let res_2 = DisjointSet.get_not_trivial_pairs data.disjoint_set in
		data.equations <- (StrMap.merge choice res_2 data.equations);
		StrMap.iter func data.equations;
		if (result.is_it_fail = true) then
			None
		else
			Some (result.map)
	;;
end;;
(* comparator - задаёт порядок на строках, возвращает true если первая строка меньше второй,
	и false иначе. Должен различать различные строки. *)
let solve_system_with_map system comparator =
	let rec solve data =
		let rec calc_var_term var_1 term data = 
			Data.calc_var_term var_1 term data;
			solve data
		in
		let rec calc_var_var var_1 var_2 data =
			Data.add_link var_1 var_2 data comparator;
			solve data
		in
		let rec calc_term_term term_1_f term_1_l term_2_f term_2_l data =
			let rec convert l_1 l_2 data =
				if ((l_1 = []) || (l_2 = [])) then
					if (l_1 = l_2) then
						solve data
					else
						None
				else
					begin
						Data.add_equation_to_calculate ((List.hd l_1), (List.hd l_2)) data;
						convert (List.tl l_1) (List.tl l_2) data
					end
			in
			if (term_1_f <> term_2_f) then
				None
			else
				convert term_1_l term_2_l data
		in
		(* Data.print_state data; *)
		if (Data.get_to_calculate data = []) then
			begin
				Data.update_to_leaders data;
				(* Data.print_state data; *)
				Data.create_solution_from_equations data
			end
		else
			let head = Data.extract_head data in
			match head with
			  | (Var(str_1), Var(str_2)) -> calc_var_var str_1 str_2 data
			  | (Var(str_1), t_2) -> calc_var_term str_1 t_2 data
			  | (t_1, Var(str_2)) -> calc_var_term str_2 t_1 data
			  | (Fun(str_1, l_1), Fun(str_2, l_2)) -> calc_term_term str_1 l_1 str_2 l_2 data
	in
	solve (Data.create system)
;;

let standart_comparator var_1 var_2 =
	let first_char str =
		if ((String.length str) = 0) then
			'_'
		else
			str.[0]
	in
	let c_1 = first_char var_1 in
	let c_2 = first_char var_2 in
	if (c_1 < c_2) then
		true
	else if (c_1 > c_2) then
		false
	else
	begin
		let is_composite str =
			if (String.contains str '<') then       true
			else if (String.contains str '.') then  true
			else if (String.contains str '\\') then true
			else                                    false
		in
		let c_1 = is_composite var_1 in
		let c_2 = is_composite var_2 in
		if ((c_1 = false) && (c_2 = true)) then
			true
		else if ((c_1 = true) && (c_2 = false)) then
			false
		else
			(var_1 < var_2)
	end
;;

let solve_system_with_comparator system comparator =
	let res = solve_system_with_map system comparator in
	match res with
	  | None -> None
	  | Some solution -> Some (StrMap.bindings solution)
;;

let solve_system system = solve_system_with_comparator system standart_comparator;;
