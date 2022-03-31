let __coq_plugin_name = "ra_plugin_fold"
let _ = Mltop.add_known_module __coq_plugin_name

# 11 "src/fold_g.mlg"
 
  open Ltac_plugin
  open Stdarg
  open Fold


let () = Tacentries.tactic_extend __coq_plugin_name "ra_fold" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("ra_fold", Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                           Tacentries.TyNil)), 
           (fun ops ist -> 
# 19 "src/fold_g.mlg"
                                   ra_fold_concl ops None 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("ra_fold", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyNil))), 
          (fun ops ob ist -> 
# 20 "src/fold_g.mlg"
                                             ra_fold_concl ops (Some ob) 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("ra_fold", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyIdent ("in", 
                                                          Tacentries.TyArg (
                                                          Extend.TUlist0 (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_var)), 
                                                          Tacentries.TyNil)))), 
          (fun ops l ist -> 
# 21 "src/fold_g.mlg"
                                                   ra_fold_hyps ops None l 
          )));
         (Tacentries.TyML (Tacentries.TyIdent ("ra_fold", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyIdent ("in", 
                                                          Tacentries.TyArg (
                                                          Extend.TUlist0 (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_var)), 
                                                          Tacentries.TyNil))))), 
          (fun ops ob l ist -> 
# 22 "src/fold_g.mlg"
                                                              ra_fold_hyps ops (Some ob) l 
          )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ra_fold_in_star" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("ra_fold", Tacentries.TyArg (
                                                           Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                           Tacentries.TyIdent ("in", 
                                                           Tacentries.TyIdent ("*", 
                                                           Tacentries.TyNil)))), 
           (fun ops ist -> 
# 26 "src/fold_g.mlg"
                                           ra_fold_all ops None 
           )));
         (Tacentries.TyML (Tacentries.TyIdent ("ra_fold", Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyArg (
                                                          Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                          Tacentries.TyIdent ("in", 
                                                          Tacentries.TyIdent ("*", 
                                                          Tacentries.TyNil))))), 
          (fun ops ob ist -> 
# 27 "src/fold_g.mlg"
                                                      ra_fold_all ops (Some ob) 
          )))]

