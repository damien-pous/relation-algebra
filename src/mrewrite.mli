val extend :
  Ltac_plugin.Tacinterp.interp_sign ->
  Ltac_plugin.Tacinterp.value ->
  [< `LR | `RL ] -> EConstr.constr -> unit Proofview.tactic
