(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

val ra_fold_concl :
  EConstr.constr -> EConstr.t option -> unit Proofview.tactic
val ra_fold_hyps :
  EConstr.constr ->
  EConstr.t option -> Names.Id.t list -> unit Proofview.tactic
val ra_fold_all : EConstr.constr -> EConstr.t option -> unit Proofview.tactic
