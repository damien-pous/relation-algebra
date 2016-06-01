(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** Definition of the [ra_fold] tactic, used to fold concrete 
    Relation algebra expressions *)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

open Ra_common
open Term
open Names
open Proof_type
open Sigma.Notations
open Context.Named.Declaration
open Constrarg

DECLARE PLUGIN "ra_fold"

let new_evar env sigma t =
  let sigma = Sigma.Unsafe.of_evar_map sigma in
  let Sigma (r, sigma, _) = new_evar env sigma t in
  (Sigma.to_evar_map sigma, r)

let ra_fold_term ops ob t goal =
  let env = Tacmach.pf_env goal in
  let tops = Tacmach.pf_unsafe_type_of goal ops in
  let sigma,gl = Refiner.unpackage goal in
  let rec fill ops tops = 
    if Constr.equal tops (Lazy.force Monoid.ops) then ops 
    else match kind_of_term (strip_outer_cast tops) with
      | Prod(_,s,t) -> 
	let x = e_new_evar env sigma s in
	fill (mkApp(ops,[|x|])) t
      | _ -> error "provided argument is not a monoid operation"
  in
  let ops = fill ops tops in
  let obt = Monoid.ob ops in
  let goal = Refiner.repackage sigma gl in
  let goal = ref goal in
  let unifiable sg env x y =
    try sigma := Unification.w_unify env sg Reduction.CONV x y; 
	goal := Refiner.repackage sigma gl; true
    with _ -> false
  in

  let is_pls env s' t' = is_cup (env,!sigma) max_level (Monoid.mor ops s' t') in
  let is_cap env s' t' = is_cap (env,!sigma) max_level (Monoid.mor ops s' t') in
  let is_neg env s' t' = is_neg (env,!sigma) max_level (Monoid.mor ops s' t') in
  let is_dot env = is_dot (env,!sigma) ops (fun _ -> ()) () in
  let is_itr env = is_itr (env,!sigma) max_level ops in
  let is_str env = is_str (env,!sigma) max_level ops in
  let is_cnv env = is_cnv (env,!sigma) max_level ops in
  let is_ldv env = is_ldv (env,!sigma) max_level ops (fun _ -> ()) () in
  let is_rdv env = is_rdv (env,!sigma) max_level ops (fun _ -> ()) () in

  (* folding a relation algebra term [e], with domain [s'] and codomain [t'] *)
  let rec ra_fold env s' t' e = 
    let k' _ = 
      let x = Monoid.one ops s' in 
      if convertible' (env,!sigma) e x then x else
      let x = Lattice.bot (Monoid.mor ops s' t') in 
      if convertible' (env,!sigma) e x then x else
      let x = Lattice.top (Monoid.mor ops s' t') in 
      if convertible' (env,!sigma) e x then x else
      gen_fold env e
    in
    match kind_of_term (strip_outer_cast e) with App(c,ca) -> 
      (* note that we give priority to dot/one over cap/top 
         (they coincide on flat structures) *)
      is_dot env s' (fun x () r' y -> Monoid.dot ops s' r' t' (ra_fold env s' r' x) (ra_fold env r' t' y)) (
      is_pls env s' t' (fun x y -> Lattice.cup (Monoid.mor ops s' t') (ra_fold env s' t' x) (ra_fold env s' t' y)) (
      is_cap env s' t' (fun x y -> Lattice.cap (Monoid.mor ops s' t') (ra_fold env s' t' x) (ra_fold env s' t' y)) (
      is_neg env s' t' (fun x -> Lattice.neg (Monoid.mor ops s' t') (ra_fold env s' t' x)) (
      is_itr env s' (fun x -> Monoid.itr ops s' (ra_fold env s' s' x)) (
      is_str env s' (fun x -> Monoid.str ops s' (ra_fold env s' s' x)) (
      is_cnv env s' t' (fun x -> Monoid.cnv ops t' s' (ra_fold env t' s' x)) (
      is_ldv env s' (fun x () r' y -> Monoid.ldv ops r' s' t' (ra_fold env r' s' x) (ra_fold env r' t' y)) (
      is_rdv env s' (fun x () r' y -> Monoid.rdv ops r' t' s' (ra_fold env t' r' x) (ra_fold env s' r' y)) (
      k'))))))))) (c,ca,Array.length ca)
      | _ -> k' ()

  and gen_fold env e =
    match kind_of_term (strip_outer_cast e) with 
      | App(c,ca) -> mkApp(c,Array.map (fold env) ca)
      | Prod(x,e,f) -> mkProd(x, fold env e, fold (push x e env) f)
      | Lambda(x,t,e) -> mkLambda(x, t, fold (push x t env) e)
      | LetIn(x,e,t,f) -> mkLetIn(x, fold env e, t, fold (push x t env )f)
      | Case(i,t,e,f) -> mkCase(i, t, fold env e, Array.map (fold env) f)
      | _ -> e

  and fold env e =
    let t = Typing.unsafe_type_of env !sigma e in
    match ob with
      | Some o when convertible' (env,!sigma) t (Lattice.car (Monoid.mor ops o o)) -> ra_fold env o o e
      | Some o when Constr.equal t mkProp ->
	(match kind_of_term (strip_outer_cast e) with
	  | App(c,ca) when 2 <= Array.length ca ->
	    let n = Array.length ca in 
	    let rel = (partial_app (n-2) c ca) in
	    let lops = Monoid.mor ops o o in
	    let leq = Lattice.leq1 lops in
	    let weq = Lattice.weq1 lops in
	    if unifiable !sigma env rel weq then
	      mkApp(weq,[|ra_fold env o o ca.(n-2);ra_fold env o o ca.(n-1)|]) else
	    if unifiable !sigma env rel leq then
	      mkApp(leq,[|ra_fold env o o ca.(n-2);ra_fold env o o ca.(n-1)|]) else
	    gen_fold env e
	  | _ -> gen_fold env e)
      | _ when Constr.equal t mkProp ->
	(match kind_of_term (strip_outer_cast e) with
	  | App(c,ca) when 2 <= Array.length ca ->
	    let n = Array.length ca in 
	    let rel = (partial_app (n-2) c ca) in
	    let sg,s = new_evar env !sigma obt in
	    let sg,t = new_evar env sg obt in
	    let lops = Monoid.mor ops s t in
	    let leq = Lattice.leq1 lops in
	    let weq = Lattice.weq1 lops in
	    if unifiable sg env rel weq 
	    then mkApp(weq,[|ra_fold env s t ca.(n-2);ra_fold env s t ca.(n-1)|]) 
	    else if unifiable sg env rel leq 
	    then mkApp(leq,[|ra_fold env s t ca.(n-2);ra_fold env s t ca.(n-1)|]) 
	    else gen_fold env e
	  | _ -> gen_fold env e)
      | _ ->
	let sg,s' = new_evar env !sigma obt in
	let sg,t' = new_evar env sg obt in
	if unifiable sg env t (Lattice.car (Monoid.mor ops s' t')) 
	then ra_fold env s' t' e
	else gen_fold env e
  in 
  let t = fold env t in
  t,!goal
    
let ra_fold_concl ops ob goal =
  let f,goal = ra_fold_term ops ob (Tacmach.pf_concl goal) goal in
  (try Proofview.V82.of_tactic (Tactics.convert_concl f DEFAULTcast) goal
   with e -> Feedback.msg_warning (Printer.pr_lconstr f); raise e)

let ra_fold_hyp' ops ob decl goal =
  let typ,goal = ra_fold_term ops ob (get_type decl) goal in
  (try Proofview.V82.of_tactic (Tactics.convert_hyp ~check:false decl) goal
   with e -> Feedback.msg_warning (Printer.pr_lconstr typ); raise e)

let ra_fold_hyp ops ob hyp goal =
  ra_fold_hyp' ops ob (Tacmach.pf_get_hyp goal hyp) goal

let ra_fold_hyps ops ob = 
  List.fold_left (fun acc hyp -> Tacticals.tclTHEN (ra_fold_hyp ops ob hyp) acc) 
    Tacticals.tclIDTAC 

let ra_fold_all ops ob goal =
  let hyps = Tacmach.pf_hyps goal in
  List.fold_left (fun acc hyp -> Tacticals.tclTHEN (ra_fold_hyp' ops ob hyp) acc) 
    (ra_fold_concl ops ob) hyps goal

(* tactic grammar entries *)
TACTIC EXTEND ra_fold
  | [ "ra_fold" constr(ops) ] -> [ Proofview.V82.tactic (ra_fold_concl ops None) ]
  | [ "ra_fold" constr(ops) constr(ob)] -> [ Proofview.V82.tactic (ra_fold_concl ops (Some ob)) ]
  | [ "ra_fold" constr(ops) "in" hyp_list(l)] -> [ Proofview.V82.tactic (ra_fold_hyps ops None l) ]
  | [ "ra_fold" constr(ops) constr(ob) "in" hyp_list(l)] -> [ Proofview.V82.tactic (ra_fold_hyps ops (Some ob) l) ]
END

TACTIC EXTEND ra_fold_in_star
  | [ "ra_fold" constr(ops) "in" "*"] -> [ Proofview.V82.tactic (ra_fold_all ops None) ]
  | [ "ra_fold" constr(ops) constr(ob) "in" "*"] -> [ Proofview.V82.tactic (ra_fold_all ops (Some ob)) ]
END
