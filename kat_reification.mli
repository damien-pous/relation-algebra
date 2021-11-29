(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

module KAT :
  sig
    val path : string list
    val kar : EConstr.t lazy_t
    val tst : EConstr.t -> EConstr.t -> EConstr.t
    val inj2 : EConstr.t -> EConstr.t -> EConstr.t
    val inj : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
  end
module Pack :
  sig
    val path : string list
    val var : EConstr.t lazy_t
    val expr :
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val eval :
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val v_get : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val v_add :
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val v_L : EConstr.t -> EConstr.t -> EConstr.t
    val inj :
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val e_var : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val p_var : EConstr.t -> EConstr.t
    val s' : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val t' : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
  end
module Syntax :
  sig
    val path : string list
    val pack_type : EConstr.t -> EConstr.t -> EConstr.t
    val pack :
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val src_ : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val tgt_ : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val pp : ('a -> 'b -> EConstr.constr -> 'c -> 'd) -> 'a -> 'b -> 'c -> 'd
    val expr : EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
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
module Tbl :
  sig
    type 'a t
    val create : unit -> 'a t
    val insert :
      Goal.goal Evd.sigma ->
      'a t -> EConstr.constr -> EConstr.constr -> 'a -> int
    val to_env : 'a t -> EConstr.constr -> EConstr.constr -> EConstr.constr
    val get : 'a t -> int -> EConstr.constr * 'a
  end
module AST :
  sig
    type idx = int
    type t = Bot | Top | Tst of int | Neg of t | Cap of t * t | Cup of t * t
    type e =
        Zer of idx * idx
      | One of idx
      | Var of int
      | Prd of idx * t
      | Pls of idx * idx * e * e
      | Dot of idx * idx * idx * e * e
      | Itr of idx * e
      | Str of idx * e
    val tread : t -> EConstr.t
    val read :
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> e -> EConstr.t
    val topt : t -> Kat_dec.pred
    val opt : e -> Kat_dec.gregex
    val equiv :
      e -> e -> ((Kat_dec.atom * Kat_dec.rel) list * Kat_dec.atom) option
    val parse_trace :
      EConstr.t ->
      EConstr.t ->
      (EConstr.t -> EConstr.t) ->
      (('a * EConstr.t) * ('b * EConstr.t)) Tbl.t ->
      ('a, 'c Tbl.t * 'd) Hashtbl.t ->
      'e * EConstr.t ->
      'a * EConstr.t ->
      ((int * bool) list * int) list * (int * bool) list -> EConstr.t
  end
val reify_kat_goal : ?kat:EConstr.t -> bool -> unit Proofview.tactic
val get_kat_alphabet : unit Proofview.tactic
