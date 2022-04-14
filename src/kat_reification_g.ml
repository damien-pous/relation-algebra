let __coq_plugin_name = "coq-relation-algebra.kat"
let _ = Mltop.add_known_module __coq_plugin_name

# 11 "src/kat_reification_g.mlg"
 

open Stdarg
open Ltac_plugin
open Kat_reification



let () = Tacentries.tactic_extend __coq_plugin_name "ra_kat_reify_nocheck" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("ra_kat_reify_nocheck", 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                            Tacentries.TyNil)), (fun kat ist -> 
# 21 "src/kat_reification_g.mlg"
                                                reify_kat_goal ~kat false 
                                                )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ra_kat_reify_check" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("ra_kat_reify", Tacentries.TyArg (
                                                                Extend.TUentry (Genarg.get_arg_tag wit_constr), 
                                                                Tacentries.TyNil)), 
           (fun kat ist -> 
# 23 "src/kat_reification_g.mlg"
                                        reify_kat_goal ~kat true 
           )))]

let () = Tacentries.tactic_extend __coq_plugin_name "ra_get_kat_alphabet" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("ra_get_kat_alphabet", 
                            Tacentries.TyNil), (fun ist -> 
# 25 "src/kat_reification_g.mlg"
                                   get_kat_alphabet 
                                               )))]

