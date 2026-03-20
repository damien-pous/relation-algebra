val extend :
  (EConstr.constr -> unit Proofview.tactic) ->
  [< `LR | `RL ] -> EConstr.constr -> unit Proofview.tactic
