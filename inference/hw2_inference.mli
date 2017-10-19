open Hw1;;
open Hw2_unify;;

type simp_type = S_Elem of string | S_Arrow of simp_type * simp_type
val infer_simp_type : lambda -> ((string * simp_type) list * simp_type) option

val string_of_simp_type : simp_type -> string
val simp_type_of_algebraic_term : algebraic_term -> simp_type

val get_reused_name_in_lambda : lambda -> string option
val make_system : lambda -> (algebraic_term * algebraic_term) list * string

type hm_lambda = HM_Var of string | HM_Abs of string * lambda | HM_App of lambda * lambda | HM_Let of string * lambda * lambda
type hm_type = HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type
val algorithm_w : hm_lambda -> ((string * hm_type list) * hm_type) option
