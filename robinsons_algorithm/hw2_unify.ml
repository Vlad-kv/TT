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

let rec algebraic_term_to_string term =
	let rec list_to_string l =
		if (l == []) then
			""
		else
			(algebraic_term_to_string (List.hd l)) ^ " " ^ (list_to_string (List.tl l))
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

let apply_substitution x y = failwith "Not implemented";;
let check_solution x y = failwith "Not implemented";;
let solve_system x = failwith "Not implemented";;
