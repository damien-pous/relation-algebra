(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

(** Simple helper to define basic rewriting modulo A (associativity) tactics:
    (see the comments in [rewriting.v]) *)

open Ra_common
open Term
open Names
open Proof_type
open Proofview.Notations
open Constrarg

DECLARE PLUGIN "mrewrite"

module Ext = struct
  let path = ra_path@["rewriting"]
  let leq_2  = get_fun_10 path "ext_leq_2"
  let leq_3  = get_fun_12 path "ext_leq_3"
  let leq_4  = get_fun_14 path "ext_leq_4"
  let weq_2  = get_fun_10 path "ext_weq_2"
  let weq_3  = get_fun_12 path "ext_weq_3"
  let weq_4  = get_fun_14 path "ext_weq_4"
  let leq_2' = get_fun_10 path "ext_leq_2'"
  let leq_3' = get_fun_12 path "ext_leq_3'"
  let leq_4' = get_fun_14 path "ext_leq_4'"
  let weq_2' = get_fun_10 path "ext_weq_2'"
  let weq_3' = get_fun_12 path "ext_weq_3'"
  let weq_4' = get_fun_14 path "ext_weq_4'"
end


let rec lenght t = 
  match kind_of_term (strip_outer_cast t) with
    | Prod(_,_,t) -> 1+lenght t
    | _ -> 0

let extend ist k dir h =
  Proofview.Goal.nf_enter { enter = begin fun goal ->
  let fst,snd = match dir with `LR -> 2,1 | `RL -> 1,2 in
  let ext_2 rel = match dir,rel with 
    | `LR,`Weq -> Ext.weq_2
    | `RL,`Weq -> Ext.weq_2'
    | `LR,`Leq -> Ext.leq_2
    | `RL,`Leq -> Ext.leq_2'
  in
  let ext_3 rel = match dir,rel with 
    | `LR,`Weq -> Ext.weq_3
    | `RL,`Weq -> Ext.weq_3'
    | `LR,`Leq -> Ext.leq_3
    | `RL,`Leq -> Ext.leq_3'
  in
  let ext_4 rel = match dir,rel with 
    | `LR,`Weq -> Ext.weq_4
    | `RL,`Weq -> Ext.weq_4'
    | `LR,`Leq -> Ext.leq_4
    | `RL,`Leq -> Ext.leq_4'
  in
  let sigma = ref (Tacmach.New.project goal) in
  let rec dots env t =
    match kind_of_term (strip_outer_cast t) with
      | App(c,ca) when Constr.equal c (Lazy.force Monoid.dot0) ->
	(match dots env ca.(4) with
	  | None -> 
  	    let ops = ca.(0) in
	    let l = e_new_evar env sigma (Lazy.force Level.t) in
	    let sg,laws = 
	      try Typeclasses.resolve_one_typeclass env !sigma (Monoid.laws l ops) 
	      with Not_found -> error "could not find monoid laws"
	    in
	    let l = Evarutil.nf_evar sg l in
	    sigma := sg;
	    Some(l,ops,laws,ca.(3), [ca.(1),ca.(4); ca.(2),ca.(5)])
	      
	  | Some(l,ops,laws,r,q) -> Some(l,ops,laws,ca.(3), q@[ca.(2),ca.(5)]))
      | _ -> None
  in
  let rec ext env i h t =
    match kind_of_term (strip_outer_cast t) with
      | App(c,ca) ->
	(match 
	    if Constr.equal c (Lazy.force Lattice.weq) then Some `Weq
	    else if Constr.equal c (Lazy.force Lattice.leq) then Some `Leq
	    else None
	 with
	   | None -> error "the provided term does not end with a relation algebra (in)equation"
	   | Some rel -> 
	     let n = Array.length ca in
	     match dots env (ca.(n-fst)), ca.(n-snd) with
	       | Some(l,ops,laws,p,[n,x;m,y]),v -> ext_2 rel l ops laws n m p x y v h
	       | Some(l,ops,laws,q,[n,x;m,y;p,z]),v -> ext_3 rel l ops laws n m p q x y z v h
	       | Some(l,ops,laws,r,[n,x;m,y;p,z;q,t]),v -> ext_4 rel l ops laws n m p q r x y z t v h
	       | Some(_,_,_,_,_),_ -> error "pattern to large, please submit a feature wish"
	       | None,_ -> h 		(* no need for modulo A rewriting *)
	)
      | Prod(x,s,t) -> mkLambda(x,s,ext (push x s env) (i-1) (mkApp(h,[|mkRel i|])) t)
      | _ -> error "the provided term does not end with a relation algebra (in)equation"
  in
  let t = Tacmach.New.pf_unsafe_type_of goal h in
  let h = ext (Proofview.Goal.env goal) (lenght t) h t in
  Tacticals.New.tclTHEN (Proofview.Unsafe.tclEVARS !sigma)
  (ltac_apply ist k h)
  end }

TACTIC EXTEND ra_extend_lr [ "ra_extend" tactic(k) "->" constr(h) ] -> [ extend ist k `LR h ] END
TACTIC EXTEND ra_extend_rl [ "ra_extend" tactic(k) "<-" constr(h) ] -> [ extend ist k `RL h ] END
