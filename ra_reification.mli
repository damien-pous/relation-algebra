(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

val retype :
  EConstr.constr -> Goal.goal Evd.sigma -> Goal.goal list Evd.sigma
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
    type t
    val create : unit -> t
    val insert :
      Goal.goal Evd.sigma ->
      t -> EConstr.constr -> EConstr.constr -> EConstr.constr
    val to_env : t -> EConstr.constr -> EConstr.constr -> EConstr.constr
  end
val reify_goal : EConstr.t -> Goal.goal Evd.sigma -> Goal.goal list Evd.sigma
