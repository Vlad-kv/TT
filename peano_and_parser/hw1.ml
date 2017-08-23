type peano = Z | S of peano;;
type lambda = Var of string | Abs of string * lambda | App of lambda * lambda;;

let rec peano_of_int x =
	if (x = 0) then
		Z
	else
		S (peano_of_int (x-1));;

let rec int_of_peano p = match p with
    Z -> 0
  | S x -> 1 + int_of_peano x;;

let inc x = S x;;

let rec add x y = match y with
	Z -> x
  | S k -> S (add x k);;

let rec sub x y =
	let sub_1 x = match x with
		Z -> Z
	  | S k -> k
	in
	match y with
		Z -> x
	  | S k -> sub (sub_1 x) k;;

let rec mul x y = match y with
	Z -> Z
  | S Z -> x
  | S k -> add (mul x k) x;;

let div x y = match y with
	Z -> failwith "Division by zero."
  | y -> let rec lok_div x y = match x with
  			Z -> Z
  	 	  | x -> S (lok_div (sub x y) y)
	  	in
  		sub (lok_div (S x) y) (S Z);;

let rec power x y = match y with
	Z -> S Z
  | S k -> mul (power x k) x;;

(*----------------------------------------------------------------------------*)

let rev x = 
	let rec repacking list_1 list_2 =
		if (list_2 = []) then
			list_1
		else
			repacking ((List.hd list_2) :: list_1) (List.tl list_2)
	in
	repacking [] x;;

let rec merge_sort x = 
	let rec repacking list_1 list_2 =
		if (list_2 = []) then
			list_1
		else
			repacking ((List.hd list_2) :: list_1) (List.tl list_2)
	in
	let rec split x list_1 list_2 = 
		if (x = []) then
			(list_1, list_2)
		else
			split (List.tl x) list_2 ((List.hd x) :: list_1)
	in
	let rec merge list_1 list_2 res =
		if (list_1 = []) then
			repacking list_2 res
		else if (list_2 = []) then
			repacking list_1 res
		else if ((List.hd list_1) < (List.hd list_2)) then
			merge (List.tl list_1) list_2 ((List.hd list_1) :: res)
		else
			merge list_1 (List.tl list_2) ((List.hd list_2) :: res)
	in
	let pair = split x [] []
	in
	if (fst pair) = [] then
		x
	else
		merge (merge_sort (fst pair)) (merge_sort (snd pair)) []
	;;

(*------------------------------------------------------------------------*)
                     
let rec string_of_lambda x = 
	match x with
	  | Var k        -> k
	  | Abs (str, l) -> "(\\" ^ str ^ "." ^ (string_of_lambda l) ^ ")"
	  | App (l1, l2) -> "(" ^ (string_of_lambda l1) ^ " " ^ (string_of_lambda l2) ^ ")"
;;

let lambda_of_string str = 
	let str = str^";" in
	let pos = ref 0 in

	let rec next_not_space() =
		if (str.[!pos] = ' ') then
			begin
				pos := !pos + 1;
				next_not_space()
			end
		else
			()
	in
	let rec shift_and_next() = 
		pos := !pos + 1;
		next_not_space()
	in

	let get_var_name() = 
		let rec lok_get_name res =
			let sumb = str.[!pos] in 
			if ((('a' <= sumb) && (sumb <= 'z')) || (('0' <= sumb) && (sumb <= '9'))) then
				begin
					pos := !pos + 1;
					lok_get_name (res^(String.make 1 sumb))
				end
			else
				begin
					next_not_space();
					res
				end
		in
		next_not_space();
		if (('a' <= str.[!pos]) && (str.[!pos] <= 'z')) then
			lok_get_name ""
		else
			""
	in
	let null = Var "" in

	let rec parse_therm prev_atom = 
		next_not_space();
		let lok_res = match str.[!pos] with
				';' -> failwith ("Error on position " ^ (string_of_int !pos))
			  | '(' ->
			  		shift_and_next();
			  		let res = parse_therm null in
			  		if (str.[!pos] <> ')') then
			  			failwith ("Error - no ')'\n" ^ " on position " ^ (string_of_int !pos))
			  		else
			  			begin
			  				shift_and_next();
			  				res
			  			end
			  | '\\' ->
			  		shift_and_next();
			  		let var = get_var_name() in
			  		if (var = "") then
			  			failwith ("Error on position " ^ (string_of_int !pos));
			  		if (str.[!pos] <> '.') then
			  			failwith ("Error on position " ^ (string_of_int !pos));
	  				shift_and_next();
	  				let res = parse_therm null in
		  			Abs (var, res)
			  | _   ->
			  		let res = get_var_name() in
			  		if (res = "") then
			  			failwith ("Error on position " ^ (string_of_int !pos))
			  		else
				  		Var res
		in
		let res = 
			if (prev_atom = null) then
				lok_res
			else
				App (prev_atom, lok_res)
		in
		match str.[!pos] with
			';' -> res
		  | ')' -> res
		  | _   -> parse_therm res
	in
	parse_therm null
;;
