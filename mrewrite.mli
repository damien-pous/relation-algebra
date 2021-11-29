(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

module Ext :
  sig
    val path : string list
    val leq_2 :
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val leq_3 :
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val leq_4 :
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val weq_2 :
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val weq_3 :
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val weq_4 :
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val leq_2' :
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val leq_3' :
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val leq_4' :
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val weq_2' :
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val weq_3' :
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
    val weq_4' :
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t ->
      EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t -> EConstr.t
  end
val length : Evd.evar_map -> EConstr.constr -> int
val extend :
  Geninterp.interp_sign ->
  Ltac_plugin.Tacinterp.value ->
  [< `LR | `RL ] -> EConstr.constr -> unit Proofview.tactic
