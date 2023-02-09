(** Small library used by all ML plugins we define in the library *)

open Ltac_plugin
open Tacexpr
open EConstr
open Names

(* pick an element in an hashtbl *)
let hashtbl_pick t = Hashtbl.fold (fun i x -> function None -> Some (i,x) | acc -> acc) t None

(* recursive memoizer *)
let memoize ff =
  let t = Hashtbl.create 27 in
  let rec f x =
    try Hashtbl.find t x 
    with Not_found -> let y = ff f x in Hashtbl.add t x y; y
  in f

(* timing a function call *)
let time f x =
  let t0 = Sys.time() in
  let r = f x in
  Printf.printf "%f\n" (Sys.time()-.t0);
  r

(* path to RelationAlgebra modules *)
let ra_path = ["RelationAlgebra"]

(* raise an error in Coq *)
let error s = Printf.kprintf (fun s -> CErrors.user_err (Pp.str s)) ("[RelationAlgebra] "^^s)

(* resolving a typeclass [cls] in a goal [gl] *)
let tc_find env sigma cls = Typeclasses.resolve_one_typeclass env sigma cls

(* creating new evars *)
let new_evar env sigma ty =
  Evarutil.new_evar ~src:(None,Evar_kinds.GoalEvar) env sigma ty

(* push a variable on the environment *)
let push x t env = Termops.push_rel_assum (x,t) env

(* are two terms convertible *)
let convertible env sigma  c1 c2 = Reductionops.is_conv env sigma c1 c2
let convertible' (env,sigma) = Reductionops.is_conv env sigma

(* creating a name and a reference to that name *)
let fresh_name env n =
  let vname = Tactics.fresh_id_in_env Id.Set.empty (Id.of_string n) env in
    Context.annotR vname, mkVar vname

(* access to Coq constants *)
let get_const dir s = 
  lazy (EConstr.of_constr (UnivGen.constr_of_monomorphic_global (Global.env ()) (Coqlib.find_reference "RelationAlgebra.reification" dir s)))

(* make an application using a lazy value *)
let force_app f = fun x -> mkApp (Lazy.force f,x)

(* build a partial application *)
let partial_app n c ca = if n=0 then c else mkApp(c,Array.sub ca 0 n)

(* creating OCaml functions from Coq ones *)
let get_fun_1 d s = let v = get_const d s in fun x -> force_app v [|x|]
let get_fun_2 d s = let v = get_const d s in fun x y -> force_app v [|x;y|]
let get_fun_3 d s = let v = get_const d s in fun x y z -> force_app v [|x;y;z|]
let get_fun_4 d s = let v = get_const d s in fun x y z t -> force_app v [|x;y;z;t|]
let get_fun_5 d s = let v = get_const d s in fun x y z t u -> force_app v [|x;y;z;t;u|]
let get_fun_6 d s = let v = get_const d s in fun x y z t u r -> force_app v [|x;y;z;t;u;r|]
let get_fun_7 d s = let v = get_const d s in fun x y z t u r w -> force_app v [|x;y;z;t;u;r;w|]
let get_fun_8 d s = let v = get_const d s in fun x y z t u r w p -> force_app v [|x;y;z;t;u;r;w;p|]
let get_fun_9 d s = let v = get_const d s in fun x y z t u r w p q -> force_app v [|x;y;z;t;u;r;w;p;q|]
let get_fun_10 d s = let v = get_const d s in fun x y z t u r w p q q1 -> force_app v [|x;y;z;t;u;r;w;p;q;q1|]
let get_fun_11 d s = let v = get_const d s in fun x y z t u r w p q q1 q2 -> force_app v [|x;y;z;t;u;r;w;p;q;q1;q2|]
let get_fun_12 d s = let v = get_const d s in fun x y z t u r w p q q1 q2 q3 -> force_app v [|x;y;z;t;u;r;w;p;q;q1;q2;q3|]
let get_fun_13 d s = let v = get_const d s in fun x y z t u r w p q q1 q2 q3 q4 -> force_app v [|x;y;z;t;u;r;w;p;q;q1;q2;q3;q4|]
let get_fun_14 d s = let v = get_const d s in fun x y z t u r w p q q1 q2 q3 q4 q5 -> force_app v [|x;y;z;t;u;r;w;p;q;q1;q2;q3;q4;q5|]

let ltac_apply ist (f: Tacinterp.value) (arg : constr) =
  let open Geninterp in
  let f_ = Id.of_string "f" in
  let x_ = Id.of_string "x" in
  let arg = Tacinterp.Value.of_constr arg in
  let mkvar id = Locus.ArgVar (CAst.make id) in
  let ist = { ist with lfun = Id.Map.add f_ f (Id.Map.add x_ arg ist.lfun) } in
  Tacinterp.eval_tactic_ist ist (CAst.make (TacArg (TacCall (CAst.make (mkvar f_, [Reference (mkvar x_)])))))

(* Coq constants *)
module Coq = struct
  let path = ["Coq"; "Init"; "Datatypes"]
  let true_ = get_const path "true"
end

(* RelationAlgebra.positives Coq module (plus standard positive numbers) *)
module Pos = struct
  (* binary positive numbers *)
  let path = ["Coq" ; "Numbers"; "BinNums"]
  let t = get_const path "positive"
  let xH = get_const path "xH"
  let xI = get_fun_1 path "xI"
  let xO = get_fun_1 path "xO"
  
  (* a coq positive from an ocaml int *)
  let of_int = memoize 
    (fun of_int -> function
      | 0 -> failwith "[RelationAlgebra] Pos.of_int applied to 0"
      | 1 -> Lazy.force xH 
      | n -> (if n mod 2 = 0 then xO else xI) (of_int (n/2)))

  (* positive maps *)
  let path = ra_path@["positives"]
  let sigma       = get_fun_1 path "sigma"
  let sigma_empty = get_fun_1 path "sigma_empty"
  let sigma_add   = get_fun_4 path "sigma_add"
  let sigma_get   = get_fun_3 path "sigma_get"
end

(* RelationAlgebra.level Coq module *)
module Level = struct
  let path = ra_path@["level"]
  let t        = get_const path "level"
  let has_bot  = get_fun_1 path "has_bot"
  let has_top  = get_fun_1 path "has_top"
  let has_cup  = get_fun_1 path "has_cup"
  let has_cap  = get_fun_1 path "has_cap"
  let has_neg  = get_fun_1 path "has_neg"
  let has_str  = get_fun_1 path "has_str"
  let has_cnv  = get_fun_1 path "has_cnv"
  let has_div  = get_fun_1 path "has_div"
end 

type level = {
  has_cup: bool;
  has_bot: bool;
  has_cap: bool;
  has_top: bool;
  has_neg: bool;
  has_str: bool;
  has_cnv: bool;
  has_div: bool }

let read_level env sigma l = 
  let true_ = Lazy.force Coq.true_ in { 
    has_cup = convertible env sigma true_ (Level.has_cup l);
    has_bot = convertible env sigma true_ (Level.has_bot l);
    has_cap = convertible env sigma true_ (Level.has_cap l);
    has_top = convertible env sigma true_ (Level.has_top l);
    has_neg = convertible env sigma true_ (Level.has_neg l);
    has_str = convertible env sigma true_ (Level.has_str l);
    has_cnv = convertible env sigma true_ (Level.has_cnv l);
    has_div = convertible env sigma true_ (Level.has_div l) }
let max_level = {
  has_cup = true;
  has_bot = true;
  has_cap = true;
  has_top = true;
  has_neg = true;
  has_str = true;
  has_cnv = true;
  has_div = true }


(* RelationAlgebra.lattice Coq module *)
module Lattice = struct
  let path = ra_path@["lattice"]
  let leq_or_weq = get_const path "leq_or_weq"
  let leq1     = get_fun_1 path "leq"
  let leq      = get_const path "leq"
  let weq1     = get_fun_1 path "weq"
  let weq      = get_const path "weq"
  let car      = get_fun_1 path "car"
  let cup1     = get_fun_1 path "cup"
  let cap1     = get_fun_1 path "cap"
  let neg1     = get_fun_1 path "neg"
  let cup      = get_fun_3 path "cup"
  let cap      = get_fun_3 path "cap"
  let neg      = get_fun_2 path "neg"
  let bot      = get_fun_1 path "bot"
  let top      = get_fun_1 path "top"
end 

(* RelationAlgebra.monoid Coq module *)
module Monoid = struct
  let path = ra_path@["monoid"]
  let laws     = get_fun_2 path "laws"
  let ops      = get_const path "ops"
  let ob       = get_fun_1 path "ob"
  let mor0     = get_const path "mor"
  let mor      = get_fun_3 path "mor"
  let dot4     = get_fun_4 path "dot"
  let dot1     = get_fun_1 path "dot"
  let dot0     = get_const path "dot"
  let dot      = get_fun_6 path "dot"
  let one      = get_fun_2 path "one"
  let itr2     = get_fun_2 path "itr"
  let itr      = get_fun_3 path "itr"
  let str2     = get_fun_2 path "str"
  let str      = get_fun_3 path "str"
  let cnv3     = get_fun_3 path "cnv"
  let cnv      = get_fun_4 path "cnv"
  let ldv1     = get_fun_1 path "ldv"
  let ldv4     = get_fun_4 path "ldv"
  let ldv      = get_fun_6 path "ldv"
  let rdv1     = get_fun_1 path "rdv"
  let rdv4     = get_fun_4 path "rdv"
  let rdv      = get_fun_6 path "rdv"
end 

(* RelationAlgebra.lsyntax Coq module *)
module LSyntax = struct
  let path = ra_path@["lsyntax"]
  let pp f p s = (* f p s *)
    let c = f p s in
    fun x -> c (Lazy.force Pos.t) x
  let pp' f p s = (* f p s *)
    let c = f p s in
    lazy (c (Lazy.force Pos.t))
  let bot  = pp' get_fun_1 path "e_bot"
  let top  = pp' get_fun_1 path "e_top"
  let cup  = pp get_fun_3 path "e_cup"
  let cap  = pp get_fun_3 path "e_cap"
  let neg  = pp get_fun_2 path "e_neg"
end 

(* RelationAlgebra.syntax Coq module *)
module Make_Syntax(M: sig val typ: constr Lazy.t end) = struct
  let path = ra_path@["syntax"]
  let pack_type   = get_fun_2 path "Pack"
  let pack        = get_fun_5 path "pack"
  let src_        = get_fun_3 path "src_"
  let tgt_        = get_fun_3 path "tgt_"

  (* let im_true     = get_fun_5 path "im_true" *)
  (* let im_false    = get_fun_5 path "im_false" *)

  let pp f p s = (* f p s *)
    let c = f p s in
    fun x -> c (Lazy.force M.typ) x

  let expr = pp get_fun_5 path "expr"
  let zer  = pp get_fun_5 path "e_zer"
  let top  = pp get_fun_5 path "e_top"
  let one  = pp get_fun_4 path "e_one"
  let pls  = pp get_fun_7 path "e_pls"
  let cap  = pp get_fun_7 path "e_cap"
  let neg  = pp get_fun_6 path "e_neg"
  let dot  = pp get_fun_8 path "e_dot"
  let itr  = pp get_fun_5 path "e_itr"
  let str  = pp get_fun_5 path "e_str"
  let cnv  = pp get_fun_6 path "e_cnv"
  let ldv  = pp get_fun_8 path "e_ldv"
  let rdv  = pp get_fun_8 path "e_rdv"
  let var  = pp get_fun_4 path "e_var"

  let eval = get_fun_6 path "packed_eval"
end 

(** recognising various operations, in continuation passing style
    
    [is_cup goal l lops k k' (c,ca,n)] calls
    - [k a b] if "c(ca)" is of the shape "@cup lops a b", and cup is allowed in [l]
    - [k'] otherwise
    [n] should be the length of the array [ca]
    [lops] should be the lattice operations
  *)
let is_cup goal l lops k k' (c,ca,n as x) =
  if l.has_cup && n >= 2 && 
    convertible' goal (partial_app (n-2) c ca) (Lattice.cup1 lops) 
  then k ca.(n-2) ca.(n-1) else k' x

let is_cap goal l lops k k' (c,ca,n as x) =
  if l.has_cap && n >= 2 && 
    convertible' goal (partial_app (n-2) c ca) (Lattice.cap1 lops) 
  then k ca.(n-2) ca.(n-1) else k' x

let is_neg goal l lops k k' (c,ca,n as x) =
  if l.has_neg && n >= 1 &&
    convertible' goal (partial_app (n-1) c ca) (Lattice.neg1 lops) 
  then k ca.(n-1) else k' x

(** for iterations and converse, we need to specify the type [s'] at
    which they are expected to operate.
    [mops] should be the monoid operations *)

let is_itr goal l mops s' k k' (c,ca,n as x) =
  if l.has_str && n >= 1 && convertible' goal (partial_app (n-1) c ca) (Monoid.itr2 mops s') 
  then k ca.(n-1) else k' x

let is_str goal l mops s' k k' (c,ca,n as x) =
  if l.has_str && n >= 1 && convertible' goal (partial_app (n-1) c ca) (Monoid.str2 mops s') 
  then k ca.(n-1) else k' x

let is_cnv goal l mops s' t' k k' (c,ca,n as x) =
  if l.has_cnv && n >= 1 && convertible' goal (partial_app (n-1) c ca) (Monoid.cnv3 mops t' s') 
  then k ca.(n-1) else k' x

(** this is slightly more complicated with compositions and residuals
    since the middle type has to be read from the terms:
    [is_dot goal mops ins s s' k k' (c,ca,n)] calls
    - [k a (ins m) m b] if "c(ca)" is of the shape "@dot mops _ m _ a b"
    - [k a s s' b] if "c(ca)" is of the shape "@dot mops s' s' s' a b"
    - [k'] otherwise
    the second case is needed for flat (untyped structures), where the
    types cannot be inferred by unification.
    the [ins] function is useful to process newly encountered types on-the-fly
*)
let is_dot goal mops insert_type s s' k k' (c,ca,n as x) =
  if n >= 5 && convertible' goal (partial_app (n-5) c ca) (Monoid.dot1 mops)
  then k ca.(n-2) (insert_type ca.(n-4)) ca.(n-4) ca.(n-1)
  (* the second branch below is there for untyped products *)
  else if n >= 2 && convertible' goal (partial_app (n-2) c ca) (Monoid.dot4 mops s' s' s')
  then k ca.(n-2) s s' ca.(n-1) else k' x

let is_ldv goal l mops insert_type s s' k k' (c,ca,n as x) =
  if l.has_div && n >= 5 && convertible' goal (partial_app (n-5) c ca) (Monoid.ldv1 mops)
  then k ca.(n-2) (insert_type ca.(n-5)) ca.(n-5) ca.(n-1)
  (* the second branch below is there for untyped products *)
  else if n >= 2 && convertible' goal (partial_app (n-2) c ca) (Monoid.ldv4 mops s' s' s')
  then k ca.(n-2) s s' ca.(n-1) else k' x

let is_rdv goal l mops insert_type s s' k k' (c,ca,n as x) =
  if l.has_div && n >= 5 && convertible' goal (partial_app (n-5) c ca) (Monoid.rdv1 mops)
  then k ca.(n-2) (insert_type ca.(n-5)) ca.(n-5) ca.(n-1)
  (* the second branch below is there for untyped products *)
  else if n >= 2 && convertible' goal (partial_app (n-2) c ca) (Monoid.rdv4 mops s' s' s')
  then k ca.(n-2) s s' ca.(n-1) else k' x
