type var = int				(* propositional variables *)
type rel = int 				(* relational variables *)
type atom = (var*bool) list		(* propositional atoms *)

type pred				(* predicates *)
type gregex				(* KAT predessions *)

val p_bot: pred
val p_top: pred
val p_var: var -> pred
val p_neg: pred -> pred
val p_cup: pred -> pred -> pred
val p_cap: pred -> pred -> pred

val g_zer: gregex
val g_one: gregex
val g_rel: rel -> gregex
val g_prd: pred -> gregex
val g_itr: gregex -> gregex
val g_str: gregex -> gregex
val g_pls: gregex -> gregex -> gregex
val g_dot: gregex -> gregex -> gregex

val kat_weq: gregex -> gregex -> ((atom * rel) list * atom) option
val kat_leq: gregex -> gregex -> ((atom * rel) list * atom) option
