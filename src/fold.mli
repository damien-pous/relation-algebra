val ra_fold_concl :
  EConstr.constr -> EConstr.t option -> unit Proofview.tactic
val ra_fold_hyps :
  EConstr.constr ->
  EConstr.t option -> Names.Id.t list -> unit Proofview.tactic
val ra_fold_all : EConstr.constr -> EConstr.t option -> unit Proofview.tactic
