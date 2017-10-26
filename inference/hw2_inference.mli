open Hw1;;
open Hw2_unify;;

type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type
val infer_simp_type : lambda -> ((string * simp_type) list * simp_type) option

val string_of_simp_type : simp_type -> string
val simp_type_of_algebraic_term : algebraic_term -> simp_type

val get_reused_name_in_lambda : lambda -> string option
val make_system : lambda -> (algebraic_term * algebraic_term) list * string

type hm_lambda = HM_Var of string | HM_Abs of string * hm_lambda | HM_App of hm_lambda * hm_lambda | HM_Let of string * hm_lambda * hm_lambda
type hm_type = HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type

val substitute : hm_type -> hm_type Map.Make(String).t -> hm_type
val make_composition_of_substitutions : hm_type Map.Make(String).t -> hm_type Map.Make(String).t -> hm_type Map.Make(String).t

val string_of_hm_type : hm_type -> string
val string_of_hm_lambda : hm_lambda -> string

val hm_lambda_of_string : string -> hm_lambda
val hm_type_of_string : string -> hm_type

val algebraic_term_of_hm_type : hm_type -> algebraic_term

val algorithm_w : hm_lambda -> ((string * hm_type) list * hm_type) option
val algorithm_w_with_context : hm_lambda -> (string * hm_type) list -> ((string * hm_type) list * hm_type) option
