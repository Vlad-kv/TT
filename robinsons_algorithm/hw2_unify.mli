type algebraic_term = Var of string | Fun of string * (algebraic_term list)

val string_of_algebraic_term: algebraic_term -> string

(* По списку уравнений вернуть одно уравнение *)
val system_to_equation: (algebraic_term * algebraic_term) list -> (algebraic_term * algebraic_term)

(* Применить подстановку к уравнению *)
val apply_substitution: (string * algebraic_term) list -> algebraic_term -> algebraic_term

(* Проверить решение *)
val check_solution: (string * algebraic_term) list -> (algebraic_term * algebraic_term) list -> bool

(* Решить систему; если решения нет -- вернуть None *)
val solve_system: (algebraic_term * algebraic_term) list -> (string * algebraic_term) list option

val solve_system_with_comparator: (algebraic_term * algebraic_term) list -> (string -> string -> bool) -> (string * algebraic_term) list option
