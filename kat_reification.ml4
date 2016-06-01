(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

(** KAT reification plugin:
    - a tactic to perform KAT reification, 
      possibly checking that the corresponding equation holds, and
      displaying a counter-example in case it doesn't

    - a tactic to compute the universal KAT expression corresponding
      to a given goal, to ease elimination of Hoare hypotheses in the
      [hkat] tactic. *)

open Ra_common
open Term
open Names
open Proof_type

DECLARE PLUGIN "kat_reification"

(* RelationAlgebra.kat Coq module *)
module KAT = struct
  let path = ra_path@["kat"]
  let kar      = get_const path "kar"
  let tst      = get_fun_2 path "tst"
  let inj2     = get_fun_2 path "inj"
  let inj      = get_fun_3 path "inj"
end 

(* RelationAlgebra.kat_reification module *)
module Pack = struct
  let path = ra_path@["kat_reification"]
  let var = get_const path "var"
  let expr = get_fun_5 path "kat_expr"
  let eval = get_fun_7 path "eval"
  let v_get = get_fun_3 path "v_get"
  let v_add = get_fun_5 path "v_add"
  let v_L = get_fun_2 path "v_L"
  let inj = get_fun_5 path "e_inj"
  let e_var = get_fun_4 path "e_var"
  let p_var = get_fun_1 path "p_var"
  let s' = get_fun_3 path "s'"
  let t' = get_fun_3 path "t'"
end

module Syntax = Make_Syntax(struct let typ = Pack.var end)

(* association tables *)
module Tbl : sig
  type 'a t
  (* create an empty table *)
  val create: unit -> 'a t
  (* [insert gl t x y z] adds the association [x->(y,z)] 
     to [t] and returns the corresponding (Ocaml) index ; 
     [z] is an arbitrary information, to store with [x]
     [gl] is the current goal, used to compare terms *)
  val insert: goal Evd.sigma -> 'a t -> constr -> constr -> 'a -> int
  (* [to_env t typ def] returns (coq) environment corresponding to [t], 
     yielding elements of type [typ], with [def] as default value *)
  val to_env: 'a t -> constr -> constr -> constr
  (* [get t i] returns the (coq) value of the i-th element, 
     together with the associated information *)
  val get: 'a t -> int -> constr*'a
end = struct
  type 'a t = ref ((constr*constr*'a) list)

  let create () = ref []

  let rec find gl x = function
    | [] -> raise Not_found
    | (x',_,_)::q -> if convertible gl x x' then 1+List.length q else find gl x q

  let get t i = 
    let l = !t in 
    let (x,_,z) = List.nth l (List.length l-i) in
    (x,z)

  let insert gl t x y z =
    let l = !t in
      try find gl x l
      with Not_found -> 
	t := (x,y,z)::l; 1+List.length l
    
  let to_env t typ def = match !t with
    | [] -> mkLambda (Anonymous,Lazy.force Pos.t,def)
    | [_,x,_] -> mkLambda (Anonymous,Lazy.force Pos.t,x)
    | (_,x,_)::q ->
	Pos.sigma_get typ x
	  (snd (List.fold_left
	     (fun (i,acc) (_,x,_) -> (i-1,
	       Pos.sigma_add typ (Pos.of_int i) x acc)
	     ) (List.length q,Pos.sigma_empty typ) q
	  ))
end

(* AST for KAT expressions *)
module AST = struct
  type idx = int
  type t = 
    | Bot 
    | Top 
    | Tst of int 
    | Neg of t
    | Cap of t*t
    | Cup of t*t
  type e = 
    | Zer of idx*idx 
    | One of idx
    | Var of int
    | Prd of idx*t
    | Pls of idx*idx*e*e
    | Dot of idx*idx*idx*e*e
    | Itr of idx*e
    | Str of idx*e

  (* constructing reified Coq terms out of the AST *)
  let rec tread = function
    | Bot -> Lazy.force LSyntax.bot
    | Top -> Lazy.force LSyntax.top
    | Tst(i) -> Pack.p_var (Pos.of_int i)
    | Neg(e) -> LSyntax.neg (tread e)
    | Cap(e,f) -> LSyntax.cap (tread e) (tread f)
    | Cup(e,f) -> LSyntax.cup (tread e) (tread f)
  let read kops tenv_ref env_ref src_ tgt_ = 
    let rec read = function
      | Zer(s,t) -> Syntax.zer src_ tgt_ (Pos.of_int s) (Pos.of_int t)
      | One(s) -> Syntax.one src_ tgt_ (Pos.of_int s)
      | Var(i) -> Pack.e_var kops tenv_ref env_ref (Pos.of_int i)
      | Prd(s,e) -> Pack.inj kops tenv_ref env_ref (Pos.of_int s) (tread e)
      | Pls(s,t,e,f) -> Syntax.pls src_ tgt_ (Pos.of_int s) (Pos.of_int t) (read e) (read f)
      | Dot(r,s,t,e,f) -> Syntax.dot src_ tgt_ (Pos.of_int r) (Pos.of_int s) (Pos.of_int t) (read e) (read f)
      | Itr(s,e) -> Syntax.itr src_ tgt_ (Pos.of_int s) (read e)
      | Str(s,e) -> Syntax.str src_ tgt_ (Pos.of_int s) (read e)
    in read

  (* OCaml decision procedure *)
  open Kat_dec
  let rec topt = function
    | Bot -> p_bot
    | Top -> p_top
    | Tst(i) -> p_var i
    | Neg(e) -> p_neg (topt e)
    | Cap(e,f) -> p_cap (topt e) (topt f)
    | Cup(e,f) -> p_cup (topt e) (topt f)
  let rec opt = function
    | Zer(_,_) -> g_zer
    | One(_) -> g_one
    | Var(i) -> g_rel i
    | Prd(_,e) -> g_prd (topt e)
    | Pls(_,_,e,f) -> g_pls (opt e) (opt f)
    | Dot(_,_,_,e,f) -> g_dot (opt e) (opt f)
    | Itr(_,e) -> g_itr (opt e)
    | Str(_,e) -> g_str (opt e)
  let equiv e f = kat_weq (opt e) (opt f) 

  (* parsing back witnesses in case of failure *)
  let parse_trace kops mops lops env penv (_,p') (_,q' as qq) (w,a) =
    let parse_literal (n,n') (i,b) = 
      try 
	let i,_ = Tbl.get (fst (Hashtbl.find penv n)) i in
	`V (if b then i else Lattice.neg (lops n') i)
      with Not_found -> `One n'		(* not needed once we have typed counter-examples *)
    in
    let rec parse_witness (_,n' as nn) = function
      | [] -> `One n'
      | [x] -> parse_literal nn x
      | x::q -> match parse_literal nn x with
	  | `One _ -> parse_witness nn q
	  | x -> `Cap (n', parse_witness nn q, x)
    in
    let inj n = function
      | `One m -> `One m
      | x -> `Inj (n,x)
    in
    let dot n m p x y = 
      match x,y with
	| `One _,z | z,`One _ -> z
	| _ -> `Dot(n,m,p,x,y)
    in
    let ddot x y i = 
      let i,((_,n' as nn),(_,m')) = Tbl.get env i in
      dot p' n' m' (dot p' n' n' x (inj n' (parse_witness nn y))) (`V i)
    in
    let rec parse x = function
      | [] -> x
      | (y,i)::q -> parse (ddot x y i) q
    in 
    let rec to_constr = function
    | `V i -> i
    | `One n -> Monoid.one mops n
    | `Inj(n,e) -> KAT.inj kops n (to_constr e)
    | `Cap(n,e,f) -> Lattice.cap (lops n) (to_constr e) (to_constr f)
    | `Dot(n,m,p,e,f) -> Monoid.dot mops n m p (to_constr e) (to_constr f)
    in
    let t = dot p' q' q' (parse (`One p') w) (inj q' (parse_witness qq a))  in
    to_constr t

end


(** KAT reification tactic
   - [kat] indicates whether failure messages should mention KA or KAT
     (since the tactic fo KA is built on top of that for KAT)
   - [check] indicates whether we should run the OCaml algorithm first, 
     and display a counter-example in case of failure. 

    like for ra_reification, this tactic simply converts the goal into
    a sequence of "let ... in", so that we can later get all
    reification ingredients from Ltac, just by doing "intros ..." *)

let reify_kat_goal ?kat check =
  Proofview.V82.tactic begin fun goal ->
  let msg = 
    match kat with 
      | Some b when Constr.equal b (Lazy.force Coq.true_) -> "KAT"
      | _ -> "KA"
  in

  (* variables for referring to the environments *)
  let tenv_n,tenv_ref = fresh_name "tenv" goal in
  let env_n,env_ref = fresh_name "env" goal in 
  let penv_n,penv_ref = fresh_name "penv" goal in 

  (* table associating indices to encountered types *)
  let tenv = Tbl.create() in 			
  let insert_type t = Tbl.insert goal tenv t t () in

  (* table associating indices to encountered atoms *)
  let env = Tbl.create() in
  let insert_atom mops x (s,_ as ss) (t,_ as tt) = 
    Tbl.insert goal env x
      (Syntax.pack mops tenv_ref (Pos.of_int s) (Pos.of_int t) x) (ss,tt)
  in

  (* table associating tables for predicates, for each type *)
  let penv = Hashtbl.create 7 in
  let insert_pred x s s' = 
    let t = 
      try fst (Hashtbl.find penv s)
      with Not_found -> let t = Tbl.create() in Hashtbl.add penv s (t,s'); t
    in Tbl.insert goal t x x ()
  in

  (* get the (in)equation *)
  let rel,ca = 
    match kind_of_term (strip_outer_cast (Tacmach.pf_concl goal)) with
      | App(c,ca) ->
	if Constr.equal c (Lazy.force Lattice.weq) then mkApp (c,[|ca.(0)|]), ca
	else if Constr.equal c (Lazy.force Lattice.leq) then mkApp (c,[|ca.(0)|]), ca
	else error "unrecognised goal"
      | _ -> error "unrecognised goal"
  in

  (* get the monoid operations and the domain/codomain types *)
  let mops,src',tgt' = 
    match kind_of_term (strip_outer_cast ca.(0)) with
      | App(c,ca) when Constr.equal c (Lazy.force Monoid.mor0) -> ca.(0),ca.(1),ca.(2)
      | _ -> error "could not find monoid operations"
  in
  (* get the kat operations *)
  let kops = 
    match kind_of_term (strip_outer_cast mops) with
      | App(c,ca) when Constr.equal c (Lazy.force KAT.kar) -> ca.(0)
      | _ -> error "could not find KAT operations"
  in
  let lops = KAT.tst kops in
  	let src = insert_type src' in	
  	let tgt = insert_type tgt' in
  	let pck = Syntax.pack_type mops tenv_ref in (* type of packed elements *)
  	let typ = Monoid.ob mops in		  (* type of types *)
  let src_v,(src_n,src_) = Pack.s' kops tenv_ref env_ref, fresh_name "src" goal in
  let tgt_v,(tgt_n,tgt_) = Pack.t' kops tenv_ref env_ref, fresh_name "tgt" goal in

  let es = Tacmach.pf_env goal, Tacmach.project goal in
  let is_pls s' t' = is_cup es max_level (Monoid.mor mops s' t') in
  let is_dot = is_dot es mops insert_type in
  let is_itr = is_itr es max_level mops in
  let is_str = is_str es max_level mops in
  let is_cup s' = is_cup es max_level (lops s') in
  let is_cap s' = is_cap es max_level (lops s') in
  let is_neg s' = is_neg es max_level (lops s') in
  let is_inj s' k k' (c,ca,n as x) =
    if n >= 1 && convertible goal (partial_app (n-1) c ca) (KAT.inj2 kops s') 
    then k ca.(n-1) else k' x
  in

  (* reification of a lattice term [e], with domain [s] 
     (s: index of the domain, s': actual domain) *)
  let rec lreify (s,s' as ss) e = 
    let k' _ = 
      if convertible goal e (Lattice.top (lops s')) then AST.Top
      else if convertible goal e (Lattice.bot (lops s')) then AST.Bot
      else AST.Tst (insert_pred e s s')
    in
    match kind_of_term (strip_outer_cast e) with App(c,ca) -> 
      is_cup s' (fun x y -> AST.Cup (lreify ss x, lreify ss y)) (
      is_cap s' (fun x y -> AST.Cap (lreify ss x, lreify ss y)) (
      is_neg s' (fun x -> AST.Neg (lreify ss x)) (
      k'))) (c,ca,Array.length ca)
      | _ -> k' ()
  in

  (* reification of a term [e], with domain [s] and codomain [t] 
     (s: index of the domain, s': actual domain -- same for t) *)
  let rec reify (s,s' as ss) (t,t' as tt) e = 
    let k' _ = 
      if convertible goal e (Monoid.one mops s') then AST.One(s)
      else if convertible goal e (Lattice.bot (Monoid.mor mops s' t')) then AST.Zer(s,t)
      else AST.Var (insert_atom mops e ss tt)
    in
    match kind_of_term (strip_outer_cast e) with App(c,ca) -> 
      is_dot s s' (fun x r r' y -> 
	AST.Dot (s, r, t, reify ss (r,r') x, reify (r,r') tt y)) (
      is_pls s' t' (fun x y -> AST.Pls(s, t, reify ss tt x, reify ss tt y)) (
      is_itr s' (fun x -> AST.Itr(s, reify ss ss x)) (
      is_str s' (fun x -> AST.Str(s, reify ss ss x)) (
      is_inj s' (fun x -> AST.Prd(s, lreify ss x)) (
      k'))))) (c,ca,Array.length ca)
      | _ -> k' ()
  in

  (* reification of left and right members *)
  let lhs_v,(lhs_n,lhs) = reify (src,src') (tgt,tgt') ca.(1), fresh_name "lhs" goal in
  let rhs_v,(rhs_n,rhs) = reify (src,src') (tgt,tgt') ca.(2), fresh_name "rhs" goal in

  (* checking the equivalence in OCaml, and displaying potential counter-examples *)
  (match if check then AST.equiv lhs_v rhs_v else None with Some t -> 
    let t = AST.parse_trace kops mops lops env penv (src,src') (tgt,tgt') t in
    Tacticals.tclFAIL 0 (Pp.(++) (Pp.str (" not a "^msg^" theorem:\n"))
  			   (Printer.pr_lconstr t)) goal
    | None -> 
  	 
  (* turning the ast in to coq constr *)
  let lhs_v = AST.read kops tenv_ref env_ref src_ tgt_ lhs_v in
  let rhs_v = AST.read kops tenv_ref env_ref src_ tgt_ rhs_v in
  let src = Pos.of_int src in
  let tgt = Pos.of_int tgt in

  (* apply "eval" around the reified terms *)
  let lhs = Pack.eval kops tenv_ref env_ref penv_ref src tgt lhs in
  let rhs = Pack.eval kops tenv_ref env_ref penv_ref src tgt rhs in
  let x = Pack.expr kops tenv_ref env_ref src tgt in
    
  (* construction of coq' types index *)
  let tenv = Tbl.to_env tenv typ src' in
    
  (* construction of coq' reification environment for atoms *)
  let env = 
    let def = 
      let one = Monoid.one mops src' in
      Syntax.pack mops tenv_ref src src one 
    in
    Tbl.to_env env pck def 
  in
  
  (* construction of coq' reification environment for predicates *)
  let penv = 
    Pack.v_get kops tenv_ref
      (Hashtbl.fold (fun s (t,s') acc ->
  	Pack.v_add kops tenv_ref acc (Pos.of_int s)
  	  (Tbl.to_env t (Lattice.car (lops s')) (Lattice.top (lops s')))
       ) penv (Pack.v_L kops tenv_ref))
  in

  (* reified goal conclusion: add the relation over the two evaluated members *)
  let reified = 
    mkNamedLetIn tenv_n tenv (mkArrow (Lazy.force Pos.t) typ) (
    mkNamedLetIn env_n env (mkArrow (Lazy.force Pos.t) pck) (
    mkNamedLetIn penv_n penv 
      (mkProd (Anonymous,Lazy.force Pos.t,
  	       mkArrow (Lazy.force Pos.t) 
  		 (Lattice.car (lops (mkApp (tenv_ref,[|mkRel 2|])))))) (
    mkNamedLetIn src_n src_v (mkArrow (Lazy.force Pack.var) (Lazy.force Pos.t)) (
    mkNamedLetIn tgt_n tgt_v (mkArrow (Lazy.force Pack.var) (Lazy.force Pos.t)) (
    mkNamedLetIn lhs_n lhs_v x (
    mkNamedLetIn rhs_n rhs_v x (
      (mkApp (rel, [|lhs;rhs|])))))))))
  in	  
  (try Proofview.V82.of_tactic (Tactics.convert_concl reified DEFAULTcast) goal
   with e -> Feedback.msg_warning (Printer.pr_lconstr reified); raise e))
  end


(** tactic to precompute the alphabet and the universal expression,
    for Hoare hypotheses elimination ([hkat]) *)
let get_kat_alphabet =
  Proofview.V82.tactic begin fun goal ->

  let rec insert x = function
    | [] -> [x]
    | x'::q as l -> if convertible goal x x' then l else x'::insert x q
  in

  (* get the (in)equation *)
  let ca = 
    match kind_of_term (strip_outer_cast (Tacmach.pf_concl goal)) with
      | App(c,ca) ->
	if Constr.equal c (Lazy.force Lattice.weq) then ca
	else if Constr.equal c (Lazy.force Lattice.leq) then ca
	else error "unrecognised goal"
      | _ -> error "unrecognised goal"
  in

  (* get the monoid operations and the domain/codomain types *)
  let mops,src',tgt' = 
    match kind_of_term (strip_outer_cast ca.(0)) with
      | App(c,ca) when Constr.equal c (Lazy.force Monoid.mor0) -> ca.(0),ca.(1),ca.(2)
      | _ -> error "could not find monoid operations"
  in
  (* get the kat operations *)
  let kops = 
    match kind_of_term (strip_outer_cast mops) with
      | App(c,ca) when Constr.equal c (Lazy.force KAT.kar) -> ca.(0)
      | _ -> error "could not find KAT operations"
  in

  let es = Tacmach.pf_env goal, Tacmach.project goal in
  let is_pls s' t' = is_cup es max_level (Monoid.mor mops s' t') in
  let is_dot = is_dot es mops ignore () in
  let is_itr = is_itr es max_level mops in
  let is_str = is_str es max_level mops in
  let is_inj s' k k' (c,ca,n as x) =
    if n >= 1 && convertible goal (partial_app (n-1) c ca) (KAT.inj2 kops s') 
    then k ca.(n-1) else k' x
  in

  (* alphabet of a term [e], with domain [s] and codomain [t] 
     (s: index of the domain, s': actual domain -- same for t) *)
  let rec alphabet acc s' t' e = 
    let k' _ = 
      if convertible goal e (Monoid.one mops s') then acc
      else if convertible goal e (Lattice.bot (Monoid.mor mops s' t')) then acc
      else insert e acc
    in
    match kind_of_term (strip_outer_cast e) with App(c,ca) -> 
      is_dot s' (fun x () r' y -> alphabet (alphabet acc s' r' x) r' t' y) (
      is_pls s' t' (fun x y -> alphabet (alphabet acc s' t' x) s' t' y) (
      is_itr s' (alphabet acc s' s') (
      is_str s' (alphabet acc s' s') (
      is_inj s' (fun x -> acc) (
      k'))))) (c,ca,Array.length ca)
      | _ -> k' ()
  in

  (* getting the letters from the left and right members *)
  let alph = alphabet (alphabet [] src' tgt' ca.(2)) src' tgt' ca.(1) in
  let (alph_n,_) = fresh_name "u" goal in
  let alph_v = 
    List.fold_left (Lattice.cup (Monoid.mor mops src' tgt'))
      (Lattice.bot (Monoid.mor mops src' tgt')) alph 
  in

  (* add the alphabet with a let-in *)
  let reified = 
    mkNamedLetIn alph_n alph_v (Lattice.car (Monoid.mor mops src' tgt'))
      (Tacmach.pf_concl goal)
  in	  
    (try Proofview.V82.of_tactic (Tactics.convert_concl reified DEFAULTcast) goal
     with e -> (* Feedback.msg_warning (Printer.pr_lconstr reified); *) raise e)
  end

(* tactic grammar entries *)
TACTIC EXTEND ra_kat_reify_nocheck [ "ra_kat_reify_nocheck" constr(kat) ] -> [ reify_kat_goal ~kat false ] END
TACTIC EXTEND ra_kat_reify_check [ "ra_kat_reify" constr(kat) ] -> [ reify_kat_goal ~kat true ] END
TACTIC EXTEND ra_get_kat_alphabet [ "ra_get_kat_alphabet" ] -> [ get_kat_alphabet ] END
