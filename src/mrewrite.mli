val extend :
  Geninterp.interp_sign ->
  Ltac_plugin.Tacinterp.value ->
  [< `LR | `RL ] -> EConstr.constr -> unit Proofview.tactic
