(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * ugregex: untyped generalised regular expressions *)

(** we define here the syntax for untyped generalised regular expressions
   which we will actually use in computations *)

Require Import kat lsyntax positives sups glang comparisons boolean.
Set Implicit Arguments.


Section l.
Variable Pred: nat.
Notation Sigma := positive.
Notation Atom := (ord (pow2 Pred)).
Notation uglang := (traces_monoid_ops Atom traces_tt traces_tt).

(** * Syntax *)

(** we declare strict iteration as primitive for efficiency reasons:
   Kleene star is derived from strict iteration in a linear way,
   while deriving strict iteration out of Kleene star requires duplication. *)
Inductive ugregex :=
| u_var(i: Sigma)
| u_prd(p: expr (ord Pred)) 
| u_pls(e f: ugregex)
| u_dot(e f: ugregex)
| u_itr(e: ugregex).

(** [zer] and [one] are also derived operations *)
Definition u_zer := u_prd e_bot.
Definition u_one := u_prd e_top.
Definition u_str e := u_pls u_one (u_itr e).


(** * Language *)

(** we define the untyped guarded string language of an expression
   algebraically (by induction on the expression) ; below we
   characterise it coalgebraically *)

Fixpoint lang (e: ugregex): uglang := 
  match e with
    | u_var a => tsingle a
    | u_prd p => tinj (fun i => eval (set.mem i) p)
    | u_pls e f => lang e + lang f
    | u_dot e f => lang e * lang f
    | u_itr e => lang e ^+
  end.

(** we get a KA structure, by interpretation into languages *)

Definition u_leq e f := lang e <== lang f.
Definition u_weq e f := lang e == lang f.

Canonical Structure ugregex_lattice_ops := 
  lattice.mk_ops _ u_leq u_weq u_pls u_pls id u_zer u_zer. 

CoInductive ugregex_unit := ugregex_tt.

Canonical Structure ugregex_monoid_ops := 
  monoid.mk_ops ugregex_unit _
  (fun _ _ _ => u_dot) (fun _ => u_one) (fun _ => u_itr) (fun _ => u_str)
  (fun _ _ _ => u_zer) (fun _ _ _ _ _ => u_zer) (fun _ _ _ _ _ => u_zer). 

(* Canonical Structure ugregex_kat_ops :=  *)
(*   kat.mk_ops ugregex_monoid_ops (fun _ => lsyntax.expr_ops _ BL) (fun _ => u_prd). *)

Notation tt := ugregex_tt. 
Notation ugregex' := (ugregex_monoid_ops tt tt).

Global Instance ugregex_monoid_laws: monoid.laws BKA ugregex_monoid_ops.
Proof.
  apply (laws_of_faithful_functor (f:=fun _ _: ugregex_unit => lang)). 
  constructor; simpl ob. intros ? ?. constructor.
   now intros ? ? ?.
   now intros ? ? ?.
   now intros _ ? ?.
   discriminate. 
   intros _ [a|]; simpl; intuition; discriminate. 
   discriminate. 
   discriminate.
   reflexivity. 
   intros ? [a|]; simpl; intuition. 
   reflexivity. 
   intros _ ? x. rewrite str_itr. simpl (lang _). apply cup_weq. 2: reflexivity. 
   intros [|]; simpl. intuition. tauto. 
   discriminate.
   discriminate.
   discriminate.
  now intros ? ? ?.
  now intros ? ? ?.
Qed.

Global Instance ugregex_lattice_laws: lattice.laws BKA ugregex_lattice_ops.
Proof. apply (@lattice_laws _ _ ugregex_monoid_laws tt tt). Qed.

(** Note that [ugregex] actually comes with a KAT structure, but we do not need it *)
(* Global Instance ugregex_kat_laws: kat.laws ugregex_kat_ops. *)

(** folding expressions *)
Ltac fold_ugregex := ra_fold ugregex_monoid_ops tt.



(** * Coalgebraic characterisation of the language recognised by an expression *)

(** epsilon (optimised since it's quite simple) *)

Fixpoint epsilon_pred a (e: expr_ops (ord Pred) BL) :=
  match e with
    | e_bot => false
    | e_top => true
    | e_var i => a i
    | e_cup e f => epsilon_pred a e ||| epsilon_pred a f
    | e_cap e f => epsilon_pred a e &&& epsilon_pred a f
    | e_neg e => negb (epsilon_pred a e)
  end.

Fixpoint epsilon a (e: ugregex) :=
  match e with
    | u_var _ => false
    | u_prd p => epsilon_pred a p
    | u_pls e f => epsilon a e ||| epsilon a f
    | u_dot e f => epsilon a e &&& epsilon a f
    | u_itr e => epsilon a e
  end.

(** derivatives (specification, unoptimised)  *)

Fixpoint deriv a i (e: ugregex'): ugregex' :=
  match e with
    | u_prd _ => 0
    | u_var j => ofbool (eqb_pos i j)
    | u_pls e f => deriv a i e + deriv a i f
    | u_dot e f => deriv a i e * f + ofbool (epsilon (set.mem a) e) * deriv a i f
    | u_itr e => deriv a i e * (e: ugregex')^*
  end.

(** corresponding coalgebraic notion of language *)

Fixpoint lang' (e: ugregex') (w: trace Atom) :=
  match w with
    | tnil a => is_true (epsilon (set.mem a) e)
    | tcons a i w => lang' (deriv a i e) w
  end.

(** characterisation of [epsilon] through languages  *)

Lemma epsilon_iff_lang_nil a e: epsilon (set.mem a) e <-> (lang e) (tnil a). 
Proof. 
 induction e; simpl.  
  intuition discriminate.
   apply eq_bool_iff. simpl epsilon. induction p; simpl. 
    reflexivity. 
    reflexivity. 
    rewrite <-Bool.orb_lazy_alt. congruence. 
    rewrite <-Bool.andb_lazy_alt. congruence. 
    congruence.
    reflexivity. 
  setoid_rewrite Bool.orb_true_iff. now apply cup_weq.
  setoid_rewrite Bool.andb_true_iff. setoid_rewrite traces_dot_nil. now apply cap_weq.
  split. exists O. simpl. tauto.
  intros [i Hi]. rewrite IHe. clear IHe. induction i. assumption.
  apply IHi. setoid_rewrite traces_dot_nil in Hi. apply Hi. 
Qed.

Lemma lang_0: lang u_zer == 0.
Proof. intros [?|???]; simpl; intuition; discriminate. Qed.

Lemma lang_1: lang u_one == 1.
Proof. intros [a|???]; simpl. intuition. reflexivity. Qed.

Lemma lang_ofbool b: lang (ofbool b: ugregex') == ofbool b.
Proof. case b. apply lang_1. apply lang_0. Qed.

Global Instance lang_leq: Proper (leq ==> leq) lang.
Proof. now intros ? ?. Qed.
Global Instance lang_weq: Proper (weq ==> weq) lang. 
Proof. now intros ? ?. Qed.

Lemma lang_sup J: lang (sup id J) == sup lang J.
Proof. apply f_sup_weq. apply lang_0. reflexivity. Qed.

Lemma deriv_sup a i J: deriv a i (sup id J) = sup (deriv a i) J.
Proof. apply f_sup_eq; now f_equal. Qed.

(** characterisation of derivatives through languages *)

Lemma deriv_traces a i e: lang (deriv a i e) == traces_deriv a i (lang e).
Proof.
  symmetry. induction e; simpl deriv. simpl lang. 
   rewrite lang_ofbool. apply traces_deriv_single. 
   rewrite lang_0. apply traces_deriv_inj. 
   setoid_rewrite traces_deriv_pls. now apply cup_weq. 
   generalize (epsilon_iff_lang_nil a e1). case epsilon; intro He1. 
    fold_ugregex. setoid_rewrite dot1x. simpl lang. 
    setoid_rewrite traces_deriv_dot_1. now rewrite IHe1, IHe2. 
     now rewrite <-He1. 
    fold_ugregex. setoid_rewrite dot0x. rewrite cupxb. simpl lang. 
    setoid_rewrite traces_deriv_dot_2. now rewrite IHe1.
     rewrite <-He1. discriminate. 
   simpl lang. 
    setoid_rewrite traces_deriv_itr. now rewrite IHe, str_itr, <-inj_top. 
Qed.

(** the two definitions of languages (algebraic and coalgebraic) coincide,
   by unicity of the coalgebra morphism from expressions to languages *)

Theorem lang_lang' e: lang e == lang' e. 
Proof.
  symmetry. intro w. revert e. induction w as [a|a i w IH]; simpl lang'; intro e. 
  - apply epsilon_iff_lang_nil. 
  - rewrite IH. apply deriv_traces. 
Qed.

(** as a consequence, [lang'] preserves equality *)
Corollary lang'_weq: Proper (weq ==> weq) lang'.
Proof. intros ? ? H. apply lang_weq in H. now rewrite 2 lang_lang' in H. Qed.


(** * Comparing expressions *)

Fixpoint ugregex_compare (x y: ugregex) :=
  match x,y with
    | u_prd a, u_prd b 
    | u_var a, u_var b       => cmp a b
    | u_pls x x', u_pls y y' 
    | u_dot x x', u_dot y y' => lex (ugregex_compare x y) (ugregex_compare x' y')
    | u_itr x, u_itr y       => ugregex_compare x y
    | u_var _, _             => Lt
    | _, u_var _             => Gt
    | u_prd _, _             => Lt
    | _, u_prd _             => Gt
    | u_itr _ , _            => Lt
    | _, u_itr _             => Gt
    | u_pls _ _ , _          => Lt
    | _, u_pls _ _           => Gt
  end.


Lemma ugregex_compare_spec x y: compare_spec (x=y) (ugregex_compare x y).
Proof.
  revert y; induction x; destruct y; try (constructor; congruence); simpl.
  case cmp_spec; constructor; congruence.
  case cmp_spec; constructor; congruence.
  eapply lex_spec; eauto. intuition congruence. 
  eapply lex_spec; eauto. intuition congruence. 
  case IHx; constructor; congruence. 
Qed.

Canonical Structure ugregex_cmp := mk_simple_cmp _ ugregex_compare_spec.

End l. 
