(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

val extend :
  Geninterp.interp_sign ->
  Ltac_plugin.Tacinterp.value ->
  [< `LR | `RL ] -> EConstr.constr -> unit Proofview.tactic
