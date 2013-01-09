(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * A simple algorithm for deciding KAT (in)equivalence
    (providing counter-examples in case of failure) 

    Computing counter-examples in OCaml has three advantages:
    - it's faster so that failures are detected earlier;
    - the Coq algorithm don't need to compute them;
    - the proof of correctness of the Coq algorithm is not polluted 
      by the corresponding additional computations.

    There are two inconvenients:
    - the code is duplicated, and the OCaml one could be wrong;
    - in case of success we do the computations twice (in OCaml, then
      in Coq).

*)

(** ** KAT expressions *)

type var = int				(* propositional variables *)
type rel = int 				(* relational variables *)

(* predicates *)
type pred =
| P_bot
| P_top
| P_cup of pred * pred
| P_cap of pred * pred
| P_neg of pred
| P_var of var

let p_bot = P_bot
let p_top = P_top
let p_cup x y = P_cup(x,y)
let p_cap x y = P_cap(x,y)
let p_neg x = P_neg x
let p_var x = P_var x

(* propositional atoms *)
type atom = (var*bool) list

(* KAT expresions *)
type gregex =
| G_rel of rel
| G_prd of pred
| G_pls of gregex * gregex
| G_dot of gregex * gregex
| G_itr of gregex

let g_rel x = G_rel x
let g_prd x = G_prd x
let g_zer = G_prd P_bot
let g_one = G_prd P_top
let g_pls x y = G_pls(x,y)
let g_dot x y = G_dot(x,y)
let g_itr e = G_itr e
let g_str e = G_pls (g_one,(G_itr e))


(** ** very basic algorithm for deciding KAT (in)equations, through partial derivatives *)
(** (actually extracted from the formalised one in Coq, and then
    reworked manually to include counter-example generation) *)


(* sorted list membership *)
let rec mem x = function
  | [] -> false
  | y::q -> match compare x y with
      | 1 -> mem x q
      | 0 -> true
      | _ -> false

(* sorted list insertion *)
let rec insert x = function
  | [] -> [x]
  | y::q as l -> match compare x y with
      | 1 -> y::insert x q
      | 0 -> l
      | _ -> x::l

(* sorted union of sorted lists *)
let rec union h k = match h,k with
  | l,[] | [],l -> l
  | x::h', y::k' -> match compare x y with
      | 1 -> y::union h k'
      | 0 -> y::union h' k'
      | _ -> x::union h' k

let rec epsilon_pred a = function
  | P_bot -> false
  | P_top -> true
  | P_cup (e,f) -> epsilon_pred a e || epsilon_pred a f
  | P_cap (e,f) -> epsilon_pred a e && epsilon_pred a f
  | P_neg e -> not (epsilon_pred a e)
  | P_var i -> mem i a

let rec epsilon a = function
  | G_rel i -> false
  | G_prd p -> epsilon_pred a p
  | G_pls (e,f) -> epsilon a e || epsilon a f
  | G_dot (e,f) -> epsilon a e && epsilon a f
  | G_itr e -> epsilon a e

let rec pderiv a i = function
  | G_rel j -> if i=j then [g_one] else []
  | G_prd p -> []
  | G_pls (e,f) -> union (pderiv a i e) (pderiv a i f)
  | G_dot (e,f) -> 
    let l = List.map (fun e' -> G_dot(e',f)) (pderiv a i e) in
    if epsilon a e then union l (pderiv a i f)
    else l
  | G_itr e as ei -> 
    let es = G_pls(g_one,ei) in 
    List.map (fun e' -> G_dot (e',es)) (pderiv a i e)

let epsilon' a = List.exists (epsilon a) 

let pderiv' a i l = 
  List.fold_right (fun e -> union (pderiv a i e)) l []

let rec vars = function
  | G_rel i -> [i]
  | G_prd p -> []
  | G_pls (e,f) | G_dot(e,f)-> union (vars e) (vars f)
  | G_itr e -> vars e

let rec vars_pred = function
  | P_bot | P_top -> []
  | P_cup (e,f) | P_cap (e,f) -> union (vars_pred e) (vars_pred f)
  | P_neg e -> vars_pred e
  | P_var i -> [i]

let rec pvars = function
  | G_rel i -> []
  | G_prd p -> vars_pred p
  | G_pls (e,f) | G_dot(e,f)-> union (pvars e) (pvars f)
  | G_itr e -> pvars e

let obind f = function
| `Some x -> f x
| `Err a -> `Err a

let rec ofold f l y =
  match l with
  | [] -> `Some y
  | x::q -> obind (f x) (ofold f q y)

let loop_aux vars w e f a todo =
  if epsilon' a e = epsilon' a f then
    `Some (List.fold_right
	     (fun i x -> ((a,i)::w, pderiv' a i e, pderiv' a i f)::x) vars todo)
  else `Err a 

let rec loop vars atoms rel = function
  | [] -> None
  | (w,e,f)::todo -> 
    if mem (e,f) rel then loop vars atoms rel todo
    else match ofold (loop_aux vars w e f) atoms todo with
      | `Some todo -> loop vars atoms (insert (e,f) rel) todo
      | `Err a -> Some (List.rev w,a)

let rec atoms = function
  | [] -> [[]]
  | x::q -> 
    let f = atoms q in
    f @ List.map (fun q -> x::q) f

let rec ext w pvars = 
  match w,pvars with
    | [],_ -> List.map (fun x -> (x,false)) pvars
    | _,[] -> failwith "ext: w not in pvars"
    | x::w',y::pvars' -> match compare x y with
	| 1 -> (y,false)::ext w pvars'
	| 0 -> (x,true)::ext w' pvars'
	| _ -> failwith "ext: w not in pvars"

let kat_weq' pvars vars e f =
  let atoms = atoms pvars in
  match loop vars atoms [] [([],e,f)] with
    | Some (w,a) -> Some (List.map (fun (a,i) -> (ext a pvars,i)) w, ext a pvars)
    | None -> None

let kat_weq e f = kat_weq' (pvars (G_pls(e,f))) (vars (G_pls(e,f))) [e] [f]
let kat_leq e f = kat_weq' (pvars (G_pls(e,f))) (vars (G_pls(e,f))) (union [e] [f]) [f]
