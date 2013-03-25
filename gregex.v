(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * gregex: generalised typed regular expressions, for KAT *)

(** we define a typed syntax for KAT expressions:
   - typed because we have to prove KAT completeness at the typed level
   - generalised w.r.t. regular expressions since it has to embeds 
     Boolean expressions, for tests *)

Require Import lsyntax glang kat boolean atoms sups.
Set Implicit Arguments.


(** * Generalised regular expressions *)

Section s.

(** [I] is the set of objects of the category (or types, or indices) *)
Notation I := positive.
(** [Sigma] is the set of (Kleene) variables, those interpreted as relations, for instance *)
Notation Sigma := positive.
(** [pred] is the number of predicate variables (elementary tests), so
   that tests are just expressions with variables in [ord pred] *)
Variable pred: nat.
(** [src] and [tgt] assign a type to each Kleene variable *)
Variables src tgt: Sigma -> I.
(** Note that we do not type elementary tests: we shall actually prove
   a specific untyping theorem about KAT which makes this possible *)

(** generalised regular expressions are just typed regular
   expressions, with an additional constructor, [g_prd], for embedding
   Boolean expressions *)
Inductive gregex: I -> I -> Set :=
| g_zer: forall {n m}, gregex n m
| g_prd: forall {n} (a: expr (ord pred)), gregex n n
| g_var: forall (i: Sigma), gregex (src i) (tgt i)
| g_pls: forall n m (e f: gregex n m), gregex n m
| g_dot: forall n m p (e: gregex n m) (f: gregex m p), gregex n p
| g_itr: forall n (e: gregex n n), gregex n n.

(** [1] is derived, as the injection of the [top] expression *)
Definition g_one {n} := @g_prd n e_top.

(** Also note that [g_itr] is chosen as primitive, rather than [g_str] *)
Definition g_str n (e: gregex n n) := g_pls g_one (g_itr e).



(** * Interpretation into an arbitrary Kleene algebra with tests *)

Section e.

(** to interpret an expressions, we need:
   - a KAT [X], 
   - an interpretation [fo] of syntactic types ([I])
   - a properly typed interpretation [fs] of each Kleene variable
   - an interpretation [fp] of each predicate variable into the tests of X, at each type n
   (consider for instance, the expression [p]*a*[q], with [a: X n m, p: tst n, q: tst m],
   which can be represented by the term [@g_prd 1 (e_var 1) * g_var 1 * @g_prd 2 (e_var 1)],
   with the environments [fo(1)=n], [fo(2)=m], [fs(1)=1], [fp(1)(1)=p], [fp(2)(1)=q]). *)
Context {X: kat.ops}.
Variable fo: I -> ob X.
Variable fp: forall n, ord pred -> tst (fo n).
Variable fs: forall i, X (fo (src i)) (fo (tgt i)).

Fixpoint eval n m (e: gregex n m): X (fo n) (fo m) := 
  match e with
    | g_zer => 0
    | @g_prd n p => [lsyntax.eval (fp n) p]
    | g_pls e f => eval e + eval f
    | g_dot e f => eval e * eval f
    | g_itr e => eval e ^+
    | g_var i => fs i
  end.

End e.

(** * generalised regular expressions form a model of KAT *)

(** (in)equalitiy on [gregex] is defined as a smallest fixed-point, impredicatevely *)
Definition g_leq n m (x y: gregex n m) :=
  forall X (L: kat.laws X) fo fp fa, @eval X fo fp fa n m x <== @eval X fo fp fa n m y.
Definition g_weq n m (x y: gregex n m) :=
  forall X (L: kat.laws X) fo fp fa, @eval X fo fp fa n m x == @eval X fo fp fa n m y.

(** packing all operations using canonical structures *)
Canonical Structure gregex_lattice_ops n m := {|
  car := gregex n m;
  leq := @g_leq n m;
  weq := @g_weq n m;
  cup := @g_pls n m;
  bot := @g_zer n m;
  cap := assert_false (@g_pls n m);
  top := assert_false (@g_zer n m);
  neg := assert_false id
|}.

Canonical Structure gregex_monoid_ops := {|
  ob  := I;
  mor := gregex_lattice_ops;
  dot := g_dot;
  one := @g_one;
  itr := g_itr;
  str := g_str;
  cnv n m := assert_false (fun _ => bot);
  ldv n m p := assert_false (fun _ _ => bot);
  rdv n m p := assert_false (fun _ _ => bot)
|}.

Canonical Structure gregex_kat_ops := 
  kat.mk_ops gregex_monoid_ops (fun n => expr_ops _ BL) (@g_prd).

(** lattice laws *)
Global Instance gregex_lattice_laws n m: lattice.laws BKA (gregex_lattice_ops n m). 
Proof.
  constructor; try right; try discriminate. constructor.
   intros x X L fo fa fs. reflexivity.
   intros x y z H H' X L fo fa fs. transitivity (eval fo fa fs y); auto.
   intros x y. split. 
    intro H. split; intros X L fo fa fs. now apply weq_leq, H. now apply weq_geq, H.
    intros [H H'] X L fo fa fs. apply antisym; auto.
   intros Hl x y z. split. 
    intro H. split; intros X L fo fa fs; specialize (H X L fo fa fs); simpl in H; hlattice. 
    intros [H H'] X L fo fa fs. simpl. apply cup_spec; auto.
   intros x X L fo fa fs. apply leq_bx.
Qed.

(** kleene algebra laws *)
Global Instance gregex_monoid_laws: monoid.laws BKA gregex_monoid_ops.
Proof.
  constructor; (try discriminate); repeat right; repeat intro; simpl.
   apply gregex_lattice_laws.
   apply dotA.
   rewrite inj_top. apply dot1x.
   rewrite inj_top. apply dotx1.
   apply dot_leq; auto.
   now rewrite dotplsx.
   now rewrite dotxpls.
   now rewrite dot0x.
   now rewrite dotx0.
   lattice.
   rewrite inj_top, <-str_itr. apply str_cons.
   rewrite inj_top, <-str_itr. apply str_ind_l. now refine (H0 _ _ _ _ _).
   rewrite inj_top, <-str_itr. apply str_ind_r. now refine (H0 _ _ _ _ _).
   rewrite inj_top, <-str_itr. apply itr_str_l.
Qed.

(** KAT laws  *)
Global Instance gregex_kat_laws: kat.laws gregex_kat_ops.
Proof.
  constructor. apply gregex_monoid_laws. intro. apply lower_lattice_laws.
  constructor; try discriminate; repeat intro.
  apply inj_leq, H, tst_BL.
  apply inj_weq, H, tst_BL.
  apply inj_cup.
  apply inj_bot.
  reflexivity.
  repeat intro. apply inj_cap.
Qed.

(** additional properties of the injection ([g_prd]) *)
Definition inj_cup := @inj_cup _ gregex_kat_laws.
Definition inj_bot := @inj_bot _ gregex_kat_laws.
Definition inj_cap := @inj_cap _ gregex_kat_laws.
Definition inj_top := @inj_top _ gregex_kat_laws.
Definition inj_weq := @inj_weq _ gregex_kat_laws.
Definition inj_leq := @inj_leq _ gregex_kat_laws.

Lemma inj_sup n I J (f: I -> expr_ BL): @g_prd n (sup f J) == \sup_(i\in J) g_prd (f i).
Proof. apply f_sup_weq. apply inj_bot. apply inj_cup. Qed.


(** * Interpretation in the guarded strings model *)

(** atoms are functions from predicate variables to [bool] *)
Notation Atom := (ord (pow2 pred)).
(** guarded string languages, typed according to the [src] and [tgt] functions *)
Notation glang n m := (tglang_kat_ops pred src tgt n m). 

(** injection of atoms *)
Notation g_atom n a := (@g_prd n (atom a)).

(** (guarded string) language of a generalised regular expression.
   unlike for regular expressions, we define it inductively *)
Definition lang: forall n m, gregex_kat_ops n m -> glang n m := 
  eval id (fun _ => @e_var _) ttsingle.

(** this interpretation function is a KA morphism, by definition *)

Global Instance lang_leq n m: Proper (leq ==> leq) (@lang n m).
Proof. intros e f H. apply H. apply tglang_kat_laws. Qed.
Global Instance lang_weq n m: Proper (weq ==> weq) (@lang n m) := op_leq_weq_1.

Lemma lang_0 n m: @lang n m 0 = 0.
Proof. reflexivity. Qed.

Lemma lang_1 n: @lang n n 1 == 1.
Proof. intros [|]; simpl; intuition. Qed.

Lemma lang_pls n m (e f: gregex n m): lang (e+f) = lang e + lang f.
Proof. reflexivity. Qed.

Lemma lang_dot n m p (e: gregex n m) (f: gregex m p): lang (e*f) = lang e * lang f.
Proof. reflexivity. Qed.

Lemma lang_itr n (e: gregex n n): lang (e^+) = lang e^+.
Proof. reflexivity. Qed.

Lemma lang_sup n m I J (f: I -> _): @lang n m (sup f J) = \sup_(i\in J) lang (f i).
Proof. apply f_sup_eq; now f_equal. Qed.


(** languages of atoms *)

Lemma lang_atom n a: lang (g_atom n a) == tatom n a.
Proof.
  (* TODO: voir si on peut faire mieux *)
  intros [b|]. 2: intros; compute; intuition discriminate.
  simpl. setoid_rewrite eval_var. 
  split. intros H. now apply eval_atom in H as <-. 
  intro E. injection E. clear E. intros <-. 
  unfold atom. rewrite eval_inf. 
  rewrite is_true_inf. intros i _. 
  case_eq (set.mem a i); simpl; intros ->; reflexivity.
Qed.

End s.
Arguments g_var {pred src tgt} i.
