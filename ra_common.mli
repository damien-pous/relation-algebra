(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

val hashtbl_pick : ('a, 'b) Hashtbl.t -> ('a * 'b) option
val time : ('a -> 'b) -> 'a -> 'b
val error : ('a, unit, string, string, string, 'b) format6 -> 'a
val ra_path : string list
val tc_find :
  Goal.goal Evd.sigma -> EConstr.types -> Evd.evar_map * EConstr.constr
val new_evar :
  ?filter:Evd.Filter.t ->
  ?abstract_arguments:Evd.Abstraction.t ->
  ?candidates:EConstr.constr list ->
  ?naming:Namegen.intro_pattern_naming_expr ->
  ?typeclass_candidate:bool ->
  ?principal:bool ->
  ?hypnaming:Evarutil.naming_mode ->
  Environ.env -> Evd.evar_map -> EConstr.types -> Evd.evar_map * EConstr.t
val push :
  Names.Name.t Context.binder_annot ->
  EConstr.types -> Environ.env -> Environ.env
val convertible' :
  Environ.env * Evd.evar_map -> EConstr.constr -> EConstr.constr -> bool
val convertible :
  Goal.goal Evd.sigma -> EConstr.constr -> EConstr.constr -> bool
val fresh_name :
  string ->
  Goal.goal Evd.sigma -> Names.Id.t Context.binder_annot * EConstr.t
val get_const : string list -> string -> EConstr.t lazy_t
val force_app : EConstr.t Lazy.t -> EConstr.t array -> EConstr.t
val partial_app : int -> EConstr.t -> EConstr.t array -> EConstr.t
val get_fun_1 : string list -> string -> EConstr.t -> EConstr.t
val get_fun_2 : string list -> string -> EConstr.t -> EConstr.t -> EConstr.t
val get_fun_3 :
  string list -> string -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
val get_fun_4 :
  string list ->
  string -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
val get_fun_5 :
  string list ->
  string ->
  EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
val get_fun_6 :
  string list ->
  string ->
  EConstr.t ->
  EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
val get_fun_7 :
  string list ->
  string ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
val get_fun_8 :
  string list ->
  string ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
val get_fun_9 :
  string list ->
  string ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
val get_fun_10 :
  string list ->
  string ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
val get_fun_11 :
  string list ->
  string ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
val get_fun_12 :
  string list ->
  string ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
val get_fun_13 :
  string list ->
  string ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
val get_fun_14 :
  string list ->
  string ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
val ltac_apply :
  Geninterp.interp_sign ->
  Ltac_plugin.Tacinterp.value -> EConstr.constr -> unit Proofview.tactic
module Coq : sig val path : string list val true_ : EConstr.t lazy_t end
module Pos :
  sig
    val t : EConstr.t lazy_t
    val xH : EConstr.t lazy_t
    val xI : EConstr.t -> EConstr.t
    val xO : EConstr.t -> EConstr.t
    val of_int : int -> EConstr.t
    val path : string list
    val sigma : EConstr.t -> EConstr.t
    val sigma_empty : EConstr.t -> EConstr.t
    val sigma_add :
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val sigma_get : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
  end
module Level :
  sig
    val path : string list
    val t : EConstr.t lazy_t
    val has_bot : EConstr.t -> EConstr.t
    val has_top : EConstr.t -> EConstr.t
    val has_cup : EConstr.t -> EConstr.t
    val has_cap : EConstr.t -> EConstr.t
    val has_neg : EConstr.t -> EConstr.t
    val has_str : EConstr.t -> EConstr.t
    val has_cnv : EConstr.t -> EConstr.t
    val has_div : EConstr.t -> EConstr.t
  end
type level = {
  has_cup : bool;
  has_bot : bool;
  has_cap : bool;
  has_top : bool;
  has_neg : bool;
  has_str : bool;
  has_cnv : bool;
  has_div : bool;
}
val read_level : Goal.goal Evd.sigma -> EConstr.t -> level
val max_level : level
module Lattice :
  sig
    val path : string list
    val leq_or_weq : EConstr.t lazy_t
    val leq1 : EConstr.t -> EConstr.t
    val leq : EConstr.t lazy_t
    val weq1 : EConstr.t -> EConstr.t
    val weq : EConstr.t lazy_t
    val car : EConstr.t -> EConstr.t
    val cup1 : EConstr.t -> EConstr.t
    val cap1 : EConstr.t -> EConstr.t
    val neg1 : EConstr.t -> EConstr.t
    val cup : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val cap : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val neg : EConstr.t -> EConstr.t -> EConstr.t
    val bot : EConstr.t -> EConstr.t
    val top : EConstr.t -> EConstr.t
  end
module Monoid :
  sig
    val path : string list
    val laws : EConstr.t -> EConstr.t -> EConstr.t
    val ops : EConstr.t lazy_t
    val ob : EConstr.t -> EConstr.t
    val mor0 : EConstr.t lazy_t
    val mor : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val dot4 : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val dot1 : EConstr.t -> EConstr.t
    val dot0 : EConstr.t lazy_t
    val dot :
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val one : EConstr.t -> EConstr.t -> EConstr.t
    val itr2 : EConstr.t -> EConstr.t -> EConstr.t
    val itr : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val str2 : EConstr.t -> EConstr.t -> EConstr.t
    val str : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val cnv3 : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val cnv : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val ldv1 : EConstr.t -> EConstr.t
    val ldv4 : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val ldv :
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val rdv1 : EConstr.t -> EConstr.t
    val rdv4 : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val rdv :
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
  end
module LSyntax :
  sig
    val path : string list
    val pp : ('a -> 'b -> EConstr.t -> 'c -> 'd) -> 'a -> 'b -> 'c -> 'd
    val pp' : ('a -> 'b -> EConstr.t -> 'c) -> 'a -> 'b -> 'c lazy_t
    val bot : EConstr.t lazy_t
    val top : EConstr.t lazy_t
    val cup : EConstr.t -> EConstr.t -> EConstr.t
    val cap : EConstr.t -> EConstr.t -> EConstr.t
    val neg : EConstr.t -> EConstr.t
  end
module Make_Syntax :
  functor (M : sig val typ : EConstr.constr Lazy.t end) ->
    sig
      val path : string list
      val pack_type : EConstr.t -> EConstr.t -> EConstr.t
      val pack :
        EConstr.t ->
        EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val src_ : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val tgt_ : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val pp :
        ('a -> 'b -> EConstr.constr -> 'c -> 'd) -> 'a -> 'b -> 'c -> 'd
      val expr :
        EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val zer : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val top : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val one : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val pls :
        EConstr.t ->
        EConstr.t ->
        EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val cap :
        EConstr.t ->
        EConstr.t ->
        EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val neg :
        EConstr.t ->
        EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val dot :
        EConstr.t ->
        EConstr.t ->
        EConstr.t ->
        EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val itr : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val str : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val cnv :
        EConstr.t ->
        EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val ldv :
        EConstr.t ->
        EConstr.t ->
        EConstr.t ->
        EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val rdv :
        EConstr.t ->
        EConstr.t ->
        EConstr.t ->
        EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val var : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
      val eval :
        EConstr.t ->
        EConstr.t ->
        EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    end
val is_cup :
  Environ.env * Evd.evar_map ->
  level ->
  EConstr.t ->
  (EConstr.t -> EConstr.t -> 'a) ->
  (EConstr.t * EConstr.t array * int -> 'a) ->
  EConstr.t * EConstr.t array * int -> 'a
val is_cap :
  Environ.env * Evd.evar_map ->
  level ->
  EConstr.t ->
  (EConstr.t -> EConstr.t -> 'a) ->
  (EConstr.t * EConstr.t array * int -> 'a) ->
  EConstr.t * EConstr.t array * int -> 'a
val is_neg :
  Environ.env * Evd.evar_map ->
  level ->
  EConstr.t ->
  (EConstr.t -> 'a) ->
  (EConstr.t * EConstr.t array * int -> 'a) ->
  EConstr.t * EConstr.t array * int -> 'a
val is_itr :
  Environ.env * Evd.evar_map ->
  level ->
  EConstr.t ->
  EConstr.t ->
  (EConstr.t -> 'a) ->
  (EConstr.t * EConstr.t array * int -> 'a) ->
  EConstr.t * EConstr.t array * int -> 'a
val is_str :
  Environ.env * Evd.evar_map ->
  level ->
  EConstr.t ->
  EConstr.t ->
  (EConstr.t -> 'a) ->
  (EConstr.t * EConstr.t array * int -> 'a) ->
  EConstr.t * EConstr.t array * int -> 'a
val is_cnv :
  Environ.env * Evd.evar_map ->
  level ->
  EConstr.t ->
  EConstr.t ->
  EConstr.t ->
  (EConstr.t -> 'a) ->
  (EConstr.t * EConstr.t array * int -> 'a) ->
  EConstr.t * EConstr.t array * int -> 'a
val is_dot :
  Environ.env * Evd.evar_map ->
  EConstr.t ->
  (EConstr.t -> 'a) ->
  'a ->
  EConstr.t ->
  (EConstr.t -> 'a -> EConstr.t -> EConstr.t -> 'b) ->
  (EConstr.t * EConstr.t array * int -> 'b) ->
  EConstr.t * EConstr.t array * int -> 'b
val is_ldv :
  Environ.env * Evd.evar_map ->
  level ->
  EConstr.t ->
  (EConstr.t -> 'a) ->
  'a ->
  EConstr.t ->
  (EConstr.t -> 'a -> EConstr.t -> EConstr.t -> 'b) ->
  (EConstr.t * EConstr.t array * int -> 'b) ->
  EConstr.t * EConstr.t array * int -> 'b
val is_rdv :
  Environ.env * Evd.evar_map ->
  level ->
  EConstr.t ->
  (EConstr.t -> 'a) ->
  'a ->
  EConstr.t ->
  (EConstr.t -> 'a -> EConstr.t -> EConstr.t -> 'b) ->
  (EConstr.t * EConstr.t array * int -> 'b) ->
  EConstr.t * EConstr.t array * int -> 'b
