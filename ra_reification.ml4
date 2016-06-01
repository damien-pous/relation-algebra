(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

(** reification plugin, for the [ra_normalise], [ra_simpl], and
    [ra] tactics: we reify [monoid] and [lattice]
    operations into [syntax.expr] expressions *)

open Ra_common
open Term
open Names
open Proof_type

DECLARE PLUGIN "ra_reification"

(* RelationAlgebra.mono Coq module *)
(* module Mono = struct *)
(*   let path = ra_path@["mono"] *)
(*   let mono = get_fun_3 path "mono" *)
(* end *)

let retype c gl =
  let sigma, _ = Tacmach.pf_apply Typing.type_of gl c in
    Refiner.tclEVARS sigma gl

module Syntax = Make_Syntax(struct let typ = Pos.t end)

module Tbl : sig
  type t
  (* create an empty table *)
  val create: unit -> t
  (* [insert gl t x y] adds the association [x->y] to [t] and returns 
     the corresponding (coq) index ; [gl] is the current goal, used 
     to compare terms *)
  val insert: goal Evd.sigma -> t -> constr -> constr -> constr
  (* [to_env t typ def] returns (coq) environment corresponding to [t], 
     yielding elements of type [typ], with [def] as default value *)
  val to_env: t -> constr -> constr -> constr
end = struct
  type t = ref ((constr*constr*constr) list * int)

  let create () = ref([],1)

  let rec find gl x = function
    | [] -> raise Not_found
    | (x',i,_)::q -> if convertible gl x x' then i else find gl x q

  let insert gl t x y =
    let l,i = !t in
      try find gl x l
      with Not_found -> 
	let j = Pos.of_int i in
	  t := ((x,j,y)::l,i+1); j
    
  let to_env t typ def = match fst !t with
    | [] -> mkLambda (Anonymous,Lazy.force Pos.t,def)
    | [_,_,x] -> mkLambda (Anonymous,Lazy.force Pos.t,x)
    | (_,_,x)::q ->
	Pos.sigma_get typ x
	  (List.fold_left
	     (fun acc (_,i,x) -> Pos.sigma_add typ i x acc
	     ) (Pos.sigma_empty typ) q
	  )
end



(** main entry point: reification of the current goal.
    [l] is the level at which reification should be performed;
    this tactic simply converts the goal into a sequence of "let ... in", 
    so that we can later get all reification ingredients from Ltac, 
    just by doing "intros ..." *)

let reify_goal l goal =
  (* getting the level *)
  let l = read_level goal l in

  (* variables for referring to the environments *)
  let tenv_n,tenv_ref = fresh_name "tenv" goal in
  let env_n,env_ref = fresh_name "env" goal in 

  (* table associating indices to encountered types *)
  let tenv = Tbl.create() in 			
  let insert_type t = Tbl.insert goal tenv t t in

  (* table associating indices to encountered atoms *)
  let env = Tbl.create() in
  let insert_atom ops x s s' t = 
    Tbl.insert goal env x ((* lazy *) (
      (* let m =  *)
      (* 	try if s<>t then raise Not_found else *)
      (* 	  let h = resolve_one_typeclass goal (Mono.mono ops s' x) in *)
      (* 	  Syntax.im_true ops tenv_ref s x h *)
      (* 	with Not_found -> Syntax.im_false ops tenv_ref s t x *)
      (* in *)
      Syntax.pack ops tenv_ref s t x (* m *)
    ))
  in

  (* get the (in)equation *)
  let rel,lops,lhs,rhs = 
    match kind_of_term (strip_outer_cast (Tacmach.pf_concl goal)) with
      | App(c,ca) when Constr.equal c (Lazy.force Lattice.leq_or_weq)
		  -> mkApp (c,[|ca.(0);ca.(1)|]), ca.(1), ca.(2), ca.(3)
      | App(c,ca) when Constr.equal c (Lazy.force Lattice.leq) || Constr.equal c (Lazy.force Lattice.weq)
		  -> mkApp (c,[|ca.(0)|]), ca.(0), ca.(1), ca.(2)
      | _ -> error "unrecognised goal"
  in

  (* get the monoid.ops and the domain/codomain types *)
  let ops,src',tgt' = 
    match kind_of_term (strip_outer_cast lops) with
      | App(c,ca) when Constr.equal c (Lazy.force Monoid.mor0) -> ca.(0),ca.(1),ca.(2)
      | _ -> error "could not find monoid operations"
  in
  let src = insert_type src' in	
  let tgt = insert_type tgt' in
  let pck = Syntax.pack_type ops tenv_ref in (* type of packed elements *)
  let typ = Monoid.ob ops in	           (* type of types *)
  let src_v,(src_n,src_) = Syntax.src_ ops tenv_ref env_ref, fresh_name "src" goal in
  let tgt_v,(tgt_n,tgt_) = Syntax.tgt_ ops tenv_ref env_ref, fresh_name "tgt" goal in

  let es = Tacmach.pf_env goal, Tacmach.project goal in
  let is_pls s' t' = is_cup es l (Monoid.mor ops s' t') in
  let is_cap s' t' = is_cap es l (Monoid.mor ops s' t') in
  let is_neg s' t' = is_neg es l (Monoid.mor ops s' t') in
  let is_dot = is_dot es ops insert_type in
  let is_itr = is_itr es l ops in
  let is_str = is_str es l ops in
  let is_cnv = is_cnv es l ops in
  let is_ldv = is_ldv es l ops insert_type in
  let is_rdv = is_rdv es l ops insert_type in

  (* reification of a term [e], with domain [s] and codomain [t] *)
  let rec reify (s,s' as ss) (t,t' as tt) e = 
    let k' _ = 
      if convertible goal e (Monoid.one ops s') then 
        Syntax.one src_ tgt_ s
      else if l.has_bot && convertible goal e (Lattice.bot (Monoid.mor ops s' t')) then
        Syntax.zer src_ tgt_ s t
      else if l.has_top && convertible goal e (Lattice.top (Monoid.mor ops s' t')) then
        Syntax.top src_ tgt_ s t
      else
        Syntax.var src_ tgt_ (insert_atom ops e s s' t)
    in
    match kind_of_term (strip_outer_cast e) with App(c,ca) -> 
      (* note that we give priority to dot/one over cap/top 
         (they coincide on flat structures) *)
      is_dot s s' (fun x r r' y -> 
        Syntax.dot src_ tgt_ s r t (reify ss (r,r') x) (reify (r,r') tt y)) (
      is_pls s' t' (fun x y -> Syntax.pls src_ tgt_ s t (reify ss tt x) (reify ss tt y)) (
      is_cap s' t' (fun x y -> Syntax.cap src_ tgt_ s t (reify ss tt x) (reify ss tt y)) (
      is_neg s' t' (fun x -> Syntax.neg src_ tgt_ s t (reify ss tt x)) (
      is_itr s' (fun x -> Syntax.itr src_ tgt_ s (reify ss ss x)) (
      is_str s' (fun x -> Syntax.str src_ tgt_ s (reify ss ss x)) (
      is_cnv s' t' (fun x -> Syntax.cnv src_ tgt_ t s (reify tt ss x)) (
      is_ldv s s' (fun x r r' y -> 
        Syntax.ldv src_ tgt_ r s t (reify (r,r') ss x) (reify (r,r') tt y)) (
      is_rdv s s' (fun x r r' y -> 
        Syntax.rdv src_ tgt_ r t s (reify tt (r,r') x) (reify ss (r,r') y)) (
      k'))))))))) (c,ca,Array.length ca)
      | _ -> k' ()
  in

  (* reification of left and right members *)
  let lhs_v,(lhs_n,lhs) = reify (src,src') (tgt,tgt') lhs, fresh_name "lhs" goal in
  let rhs_v,(rhs_n,rhs) = reify (src,src') (tgt,tgt') rhs, fresh_name "rhs" goal in
    
  (* apply "eval" around the reified terms *)
  let lhs = Syntax.eval ops tenv_ref env_ref src tgt lhs in
  let rhs = Syntax.eval ops tenv_ref env_ref src tgt rhs in
  let x = Syntax.expr src_ tgt_ src tgt in
    
  (* construction of coq' types index *)
  let tenv = Tbl.to_env tenv typ src' in
    
  (* construction of coq' reification environment *)
  let env = 
    let def = 
      let one = Monoid.one ops src' in
      Syntax.pack ops tenv_ref src src one 
        (* (Syntax.im_false ops tenv_ref src src one) *)
    in
    Tbl.to_env env pck def 
  in

  (* reified goal conclusion: add the relation over the two evaluated members *)
  let reified = 
    mkNamedLetIn tenv_n tenv (mkArrow (Lazy.force Pos.t) typ) (
    mkNamedLetIn env_n env (mkArrow (Lazy.force Pos.t) pck) (
    mkNamedLetIn src_n src_v (mkArrow (Lazy.force Pos.t) (Lazy.force Pos.t)) (
    mkNamedLetIn tgt_n tgt_v (mkArrow (Lazy.force Pos.t) (Lazy.force Pos.t)) (
    mkNamedLetIn lhs_n lhs_v x (
    mkNamedLetIn rhs_n rhs_v x (
    (mkApp (rel, [|lhs;rhs|]))))))))
  in	  
    (try Tacticals.tclTHEN (retype reified) (Proofview.V82.of_tactic (Tactics.convert_concl reified DEFAULTcast)) goal
     with e -> Feedback.msg_warning (Printer.pr_lconstr reified); raise e)

	
(* tactic grammar entries *)
TACTIC EXTEND ra_reify [ "ra_reify" constr(level) ] -> [ Proofview.V82.tactic (reify_goal level) ] END
