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
end;;

module Data = struct
	module StrSet = Set.Make(String);;
	module StrMap = Map.Make(String);;
	type data = {
		disjoint_set: DisjointSet.disjoint_set;
		mutable terms: StrSet.t StrMap.t;
		mutable to_calculate: (algebraic_term * algebraic_term) list;
		mutable modified: StrSet.t;
	};;
	let create_data l = {
		disjoint_set = {disp = StrMap.empty;};
		terms = StrMap.empty;
		to_calculate = l;
		modified = StrSet.empty;
	};;
	let print_state data =
		print_string "disjoint_set:\n";
		let lok_print first second =
			print_string ("  " ^ first ^ " -> " ^ second ^ "\n")
		in
		StrMap.iter lok_print data.disjoint_set.disp;
		print_string "terms:\n";
		let lok_print var set = 
			print_string ("  " ^ var ^ ":\n");
			let print_set el = print_string ("    " ^ el ^ "\n") in
			StrSet.iter print_set set
		in
		StrMap.iter lok_print data.terms;
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
		print_string "modified:\n";
		let lok_print var = print_string ("  " ^ var ^ "\n") in
		StrSet.iter lok_print data.modified;
		print_string "--------\n"
	;;
end;;

let solve_system_with_map system =
	let rec solve data =
		Data.print_state data;
		failwith "Not implemented"
	in
	solve (Data.create_data system)
;;
let system = [
	(Var("x_1"), Var("x_2"));
	(Fun("f1", [Var("x_3"); Var("x_4")]), Var("x_5"))
];;

let test = solve_system_with_map system;;

let solve_system system = failwith "Not implemented";;(* StrMap.bindings (solve_system_with_map system);; *)
