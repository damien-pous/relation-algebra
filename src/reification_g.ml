let __coq_plugin_name = "coq-relation-algebra.reification"
let _ = Mltop.add_known_module __coq_plugin_name

# 11 "src/reification_g.mlg"
 

open Stdarg
open Ltac_plugin
open Reification



let () = Tacentries.tactic_extend __coq_plugin_name "ra_reify" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("ra_reify", Tacentries.TyArg (
                                                            Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                            Tacentries.TyNil)), 
           (fun level ist -> 
# 21 "src/reification_g.mlg"
                                      reify_goal level 
           )))]

