open Hw1;;

print_int (int_of_peano (S(S(S Z))) );;
print_string "\n";;

assert ((div (peano_of_int 11) (peano_of_int 3)) = (peano_of_int 3));;

let print_list l = 
	let printer c = print_string ((string_of_int c) ^ " ") in
	List.iter printer l;
	print_string "\n"
;;
print_list (merge_sort [1; 4; 8; 4; 100; -2; 1; 2; 5]);;
