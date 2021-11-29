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
open Constr
open EConstr
open Context.Named.Declaration
open Proofview

let ra_fold_term ops ob t goal =
  let env = Tacmach.Old.pf_env goal in
  let _,tops = Tacmach.Old.pf_type_of goal ops in
  let rec fill sigma ops tops =
    if EConstr.eq_constr sigma tops (Lazy.force Monoid.ops) then (sigma,ops)
    else
      match kind sigma (Termops.strip_outer_cast sigma tops) with
      | Prod(_,s,t) -> 
	let sigma,x = new_evar env sigma s in
	fill sigma (mkApp(ops,[|x|])) t
      | _ -> error "provided argument is not a monoid operation"
  in
  let sigma,ops = fill (Tacmach.Old.project goal) ops tops in  
  let sigma = ref sigma in
  let obt = Monoid.ob ops in
  (* TOTKINK: Use  Evarconv.conv ? *)
  let unifiable sg env x y =
    try sigma := Unification.w_unify env sg Reduction.CONV x y; true
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
    match kind !sigma (Termops.strip_outer_cast !sigma e) with App(c,ca) -> 
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
    match kind !sigma (Termops.strip_outer_cast !sigma e) with 
      | App(c,ca) -> mkApp(c,Array.map (fold env) ca)
      | Prod(x,e,f) -> mkProd(x, fold env e, fold (push x e env) f)
      | Lambda(x,t,e) -> mkLambda(x, t, fold (push x t env) e)
      | LetIn(x,e,t,f) -> mkLetIn(x, fold env e, t, fold (push x t env )f)
      | Case(ci,u,pms,t,iv,e,f) ->
        let map i (nas, c as br) =
          let ctx = expand_branch env !sigma u pms (ci.ci_ind, i + 1) br in
          (nas, fold (push_rel_context ctx env) c)
        in
        mkCase(ci, u, pms, t, iv, fold env e, Array.mapi map f)
      | _ -> e

  and fold env e =
    let _,t = Typing.type_of env !sigma e in
    match ob with
      | Some o when convertible' (env,!sigma) t (Lattice.car (Monoid.mor ops o o)) -> ra_fold env o o e
      | Some o when EConstr.eq_constr !sigma t mkProp ->
	(match kind !sigma (Termops.strip_outer_cast !sigma e) with
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
      | _ when EConstr.eq_constr !sigma t mkProp ->
	(match kind !sigma (Termops.strip_outer_cast !sigma e) with
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
  t,!sigma
    
let ra_fold_concl ops ob = Goal.enter (fun goal ->
  (* get legacy goal *)
  let goal = Goal.print goal in
  let env = Tacmach.Old.pf_env goal in
  let f,sigma = ra_fold_term ops ob (Tacmach.Old.pf_concl goal) goal in
  (try tclTHEN (Unsafe.tclEVARS sigma) (Tactics.convert_concl ~cast:false ~check:true f DEFAULTcast)
   with e -> Feedback.msg_warning (Printer.pr_leconstr_env env sigma f); raise e))

let ra_fold_hyp' ops ob decl goal =
  let id,ddef,dtyp = to_tuple decl in
  let decl,sigma = 
    match ddef with
    | Some def ->
       (* try to fold both the body and the type of local definitions *)
       let def,sg = ra_fold_term ops ob def goal in
       let typ,sigma = ra_fold_term ops ob dtyp { goal with Evd.sigma = sg } in
       LocalDef(id,def,typ),sigma
    | None ->
       (* only fold the type of local assumptions *)
       let typ,sigma = ra_fold_term ops ob dtyp goal in
       LocalAssum(id,typ),sigma
  in
  tclTHEN (Unsafe.tclEVARS sigma) (Tactics.convert_hyp ~check:true ~reorder:true decl)

let ra_fold_hyp ops ob hyp = Goal.enter (fun goal ->
  (* get legacy goal *)
  let goal = Goal.print goal in
  ra_fold_hyp' ops ob (Tacmach.Old.pf_get_hyp goal hyp) goal)

let ra_fold_hyps ops ob = 
  List.fold_left (fun acc hyp -> tclTHEN (ra_fold_hyp ops ob hyp) acc) (tclUNIT()) 

let ra_fold_all ops ob = Goal.enter (fun goal ->
  let hyps = Goal.hyps goal in
  List.fold_left (fun acc hyp -> tclTHEN (ra_fold_hyp ops ob (get_id hyp)) acc) 
    (ra_fold_concl ops ob) hyps)
