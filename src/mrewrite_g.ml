let __coq_plugin_name = "coq-relation-algebra.mrewrite"
let _ = Mltop.add_known_module __coq_plugin_name

# 11 "src/mrewrite_g.mlg"
 
  open Ltac_plugin
  open Stdarg
  open Tacarg
  open Mrewrite


let () = Tacentries.tactic_extend __coq_plugin_name "ra_extend_lr" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("ra_extend", Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                             Tacentries.TyIdent ("->", 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                             Tacentries.TyNil)))), 
           (fun k h ist -> 
# 19 "src/mrewrite_g.mlg"
                                                  extend ist k `LR h 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ra_extend_rl" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("ra_extend", Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_tactic), 
                                                             Tacentries.TyIdent ("<-", 
                                                             Tacentries.TyArg (
                                                             Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                             Tacentries.TyNil)))), 
           (fun k h ist -> 
# 21 "src/mrewrite_g.mlg"
                                                  extend ist k `RL h 
           )))]

