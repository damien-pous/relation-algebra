(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * traces: the model of finite traces *)

(** A trace is a word in where each letter is preceded and followed by
   a "state".  Two traces compose iff the first one ends in the state
   where the second one starts.

   The traces model just consists in considering sets of traces.

   It encompasses the model of languages by taking the set of states
   to be a singleton set. When the set of states are the atoms of a
   Boolean algebra, we get so called "guarded strings", w.r.t. which
   KAT is complete.

   We define both the flat model of untyped traces, and a typed
   version of it, where we restrict to "well-typed" traces. Indeed, we
   shall prove KAT completeness for typed models, and then reduce the
   problem to untyped traces for computations. *)

Require Export prop.
Require Import monoid positives comparisons.

Set Implicit Arguments.

Section l.

Variable State: Type.
Notation Sigma := positive.

(** * Untyped traces *)

(** a trace alternates between letters and states; it starts and it
   ends with a state *)
Inductive trace := 
| tnil (a: State)
| tcons (a: State) (i: Sigma) (w: trace). 

(** starting/ending state of a trace *)
Definition thead w := match w with tnil a | tcons a _ _ => a end.
Fixpoint ttail w := match w with tnil a => a | tcons _ _ w => ttail w end.

(** predicate for trace concatenation: 
   [tapp u v w] holds iff traces [u] and [v] can be concatenated into [w] *)
Inductive tapp: trace -> trace -> trace -> Prop := 
| tapp_nil_nil: forall a, tapp (tnil a) (tnil a) (tnil a)
| tapp_nil_cons: forall a i u, tapp (tnil a) (tcons a i u) (tcons a i u)
| tapp_cons_x: forall a i u v w, tapp u v w -> tapp (tcons a i u) v (tcons a i w).

(** appending a letter and a state to a trace (not used) *)
Fixpoint tsnoc u i b :=
  match u with
    | tnil a => tcons a i (tnil b)
    | tcons a j u => tcons a j (tsnoc u i b)
  end.

(** reversing a trace (not used) *)
Fixpoint rev u :=
  match u with
    | tnil a => tnil a
    | tcons a j u => tsnoc (rev u) j a
  end.

(** we consider sets of traces *)
Definition traces := trace -> Prop.


(** ** Untyped traces as a lattice *)

(** lattice operations and laws are obtained for free, by pointwise
   lifting of the [Prop] lattice *)

Canonical Structure traces_lattice_ops := 
  lattice.mk_ops traces leq weq cup cap neg bot top.

Global Instance traces_lattice_laws: 
  lattice.laws (BDL+STR+DIV) traces_lattice_ops := lower_lattice_laws (H:=pw_laws _). 


(** * Untyped traces a residuated Kleene lattice *)

(** singleton type for the objects of this flat structure *)
CoInductive traces_unit := traces_tt.
Notation tt := traces_tt.

(** ** traces operations *)

(** concatenation *)
Definition traces_dot (n m p: traces_unit) (x y: traces): traces := 
  fun w => exists2 u, x u & exists2 v, y v & tapp u v w.

(** left and right residuals *)
Definition traces_ldv (n m p: traces_unit) (x y: traces): traces := 
  fun w => forall u uw, x u -> tapp u w uw -> y uw.

Definition traces_rdv (n m p: traces_unit) (x y: traces): traces := 
  fun w => forall u wu, x u -> tapp w u wu -> y wu.

(** unit: the set of "empty" traces, those consisting of just one state *)
Definition traces_one (n: traces_unit): traces := 
  fun w => match w with tnil _ => True | _ => False end.

(** reversed traces *)
Definition traces_cnv (n m: traces_unit) (x: traces): traces := 
  fun w => x (rev w).

(** finite iterations (with a slight generalisation: [y*x^n]) *)
Fixpoint traces_iter (y x: traces) i := 
  match i with O => y | S i => traces_dot tt tt tt x (traces_iter y x i) end.

(** strict iteration: union of finite iterations, starting with [x]  *)
Definition traces_itr (n: traces_unit) (x: traces): traces := 
  fun w => exists i, traces_iter x x i w.

(** Kleene star: union of finite iterations, starting with [1]  *)
Definition traces_str (n: traces_unit) (x: traces): traces := 
  fun w => exists i, traces_iter (traces_one n) x i w.

(** packing all operations in a canonical structure *)
Canonical Structure traces_monoid_ops := 
  monoid.mk_ops _ (fun _ _ => traces_lattice_ops)
  traces_dot traces_one traces_itr traces_str traces_cnv traces_ldv traces_rdv.

(** shorthand for [traces], when a morphism is expected *)
Notation traces' := (traces_monoid_ops tt tt).


(** ** traces form a residuated Kleene lattice *)

(** associativity of single traces concatenations *)
Lemma tapp_ass u v w uv uvw: tapp u v uv -> tapp uv w uvw -> 
  exists vw, tapp v w vw /\ tapp u vw uvw. 
Proof.
  intro H. revert uvw. induction H. 
  inversion_clear 1; eexists; split; constructor. 
  inversion_clear 1. eexists; split; constructor; assumption. 
  inversion_clear 1. edestruct IHtapp as (?&?&?). eassumption. 
   eexists; split. eassumption. constructor. assumption.
Qed.

Lemma tapp_ass' u v w vw uvw: tapp v w vw -> tapp u vw uvw -> 
  exists uv, tapp u v uv /\ tapp uv w uvw. 
Proof.
  intros H' H. induction H. 
  inversion_clear H'; eexists; split; constructor. 
  inversion_clear H'. eexists; split; constructor. eexists; split; constructor; eassumption. 
  destruct (IHtapp H') as (?&?&?). eexists (tcons _ _ _). split; constructor; eassumption. 
Qed.

(** administrative lemmas (to be reworked) *)
(* TODO: rework these lemmas *)
Lemma tapp_bounds u v w: tapp u v w -> 
  ttail u = thead v /\ 
  thead w = thead u /\
  ttail w = ttail v.
Proof. induction 1; simpl; intuition. Qed.

Lemma tapp_tail_head u v w: tapp u v w -> ttail u = thead v. 
Proof. now induction 1. Qed.

Lemma tapp_head u v w: tapp u v w -> thead u = thead w. 
Proof. now destruct 1. Qed.

Lemma tapp_tail u v w: tapp u v w -> ttail v = ttail w. 
Proof. now induction 1. Qed.

Lemma tapp_nil_x u: tapp (tnil (thead u)) u u.
Proof. destruct u; constructor. Qed.

Lemma tapp_x_nil u: tapp u (tnil (ttail u)) u.
Proof. induction u; constructor. assumption. Qed.

Lemma tapp_cat u v: ttail u = thead v -> exists w, tapp u v w. 
Proof.
  induction u; simpl; intros Hu.
   rewrite Hu. eexists. apply tapp_nil_x.
   destruct IHu as [w ?]; trivial. eexists. constructor. eassumption. 
Qed.

Lemma tapp_nil_x_eq a u v: tapp (tnil a) u v -> a = thead u /\ v = u.
Proof. now inversion_clear 1. Qed.

Lemma tapp_x_nil_eq a u v: tapp u (tnil a) v -> a = ttail u /\ v = u.
Proof.
  revert v; induction u. inversion_clear 1. now idtac. 
  inversion_clear 1. edestruct IHu as (?&?). eassumption. subst. now idtac.
Qed.

(*
Lemma rev_tsnoc u i a: rev (tsnoc u i a) = tcons a i (rev u).
Proof. induction u; simpl. reflexivity. now rewrite IHu. Qed.

Lemma rev_invol u: rev (rev u) = u.
Proof.
  induction u; simpl. reflexivity. 
  now rewrite rev_tsnoc, IHu. 
Qed.
*)  

(** auxiliary lemmas, to establish that traces form a residuated Kleene lattice *)

Lemma traces_dotA n m p q x y z: 
  traces_dot n m q x (traces_dot m p q y z) == traces_dot n p q (traces_dot n m p x y) z.
Proof.
  intro w. simpl. split. 
  intros [? ? [? [? ? [? ? E]] E']]. 
   destruct (tapp_ass' E E') as (?&?&?). repeat eexists; eassumption.
  intros [? [? ? [? ? E]] [? ? E']]. 
   destruct (tapp_ass E E') as (?&?&?). repeat eexists; eassumption.
Qed.

Lemma traces_dot_leq n m p: Proper (leq ==> leq ==> leq) (@traces_dot n m p).
Proof.
  intros x y H x' y' H' w [u Hu [v Hv Hw]]. 
  exists u. apply H, Hu. exists v. apply H', Hv. assumption.
Qed.

Lemma traces_dotx1 x: traces_dot tt tt tt x (traces_one tt) == x.
Proof.
  intro w. split. 
    intros [u Hu [[|] Hv E]]. 2: elim Hv. now apply tapp_x_nil_eq in E as [? ->].
    intro Hw. exists w. assumption. exists (tnil (ttail w)). reflexivity. 
    apply tapp_x_nil.
Qed.

Lemma traces_dot1x x: traces_dot tt tt tt (traces_one tt) x == x.
Proof.
  intro w. split.
   intros [u Hu [v Hv E]]. destruct u as [?|]. 2: elim Hu. inversion E; subst; assumption.
   intro Hw. exists (tnil (thead w)). reflexivity. exists w. assumption.
   apply tapp_nil_x.
Qed.

Lemma traces_iter_S i x: traces_iter x x i == traces_iter (traces_one tt) x (S i).
Proof. 
  induction i; simpl traces_iter. symmetry. apply traces_dotx1. 
  now apply (op_leq_weq_2 (Hf:=@traces_dot_leq _ _ _)).
Qed.

(** traces form a residuated Kleene lattice 
   (we do not have an allegory, since the converse operation does not
   satisfy the law [x<==x*x`*x]) *)
(* TODO: include a weak converse? *)
Global Instance traces_monoid_laws: monoid.laws (BDL+STR+DIV) traces_monoid_ops.
Proof.
  constructor; try (intro; discriminate); try now left. 
   intros. apply traces_lattice_laws. 
   exact traces_dotA.
   intros. apply traces_dot1x.
   right. intros. apply traces_dotx1.
   intros. intros w Hw. now exists O. 
   intros. intros w [u Hu [v [i Hv] Hw]]. exists (S i). repeat eexists; eassumption.
   intros _ ? ? x z H w [u [i Hu] [v Hv Hw]]. 
   revert u v w Hu Hv Hw; induction i; intros u v w Hu Hv Hw. 
    destruct u. 2: elim Hu. now apply tapp_nil_x_eq in Hw as [_ <-].
    destruct Hu as [u1 Hu1 [u2 Hu2 Hu]]. destruct (tapp_ass Hu Hw) as (?&?&?). 
    apply H. repeat eexists. eassumption. eapply IHi; eauto. eassumption. 
   intros _ ? x w. split. 
    intros [i H]. apply traces_iter_S in H as [? ? [? ? ?]]. repeat eexists; eauto.
    intros [? ? [? [i H] ?]]. exists i. apply traces_iter_S. repeat eexists; eauto.
   intros _ n m p x y z. split. 
    intros Hz w [u Hu [v Hv E]]. eapply Hz; eauto. 
    intros Hy v Hv u uv Hu Huv. apply Hy. repeat eexists; eauto. 
   intros _ n m p x y z. split. 
    intros Hz w [u Hu [v Hv E]]. eapply Hz; eauto. 
    intros Hy v Hv u uv Hu Huv. apply Hy. repeat eexists; eauto. 
Qed.


(** empty trace property for concatenated languages of traces *)

Lemma traces_dot_nil (L L': traces') a: (L*L')%ra (tnil a) <-> L (tnil a) /\ L' (tnil a).
Proof. 
  split. intros [h H [k K E]]. inversion E. subst. clear E. now split.
  intros [H H']. repeat eexists; eauto using tapp_nil_nil. 
Qed.


(** ** untyped traces derivatives *)

Definition traces_deriv a i (L: traces'): traces' := 
  fun w => L (tcons a i w). 

Lemma traces_deriv_0 a i: traces_deriv a i 0 == 0. 
Proof. firstorder. Qed.

Lemma traces_deriv_1 a i: traces_deriv a i 1 == 0. 
Proof. compute. intuition discriminate. Qed.

Lemma traces_deriv_pls a i (H K: traces'): 
  traces_deriv a i (H+K) == traces_deriv a i H + traces_deriv a i K.
Proof. intro. now apply cup_weq. Qed.

Lemma traces_deriv_dot_1 a i (H K: traces'): H (tnil a) ->
  traces_deriv a i (H*K) == traces_deriv a i H * K + traces_deriv a i K.
Proof.
  intros Hnil w; simpl; unfold traces_deriv, traces_dot, pw2.
   split. 
    intros [[b|b j u] Hu [v Kv E]].
     right. now apply tapp_nil_x_eq in E as [-> ->].
     inversion E. subst. clear E. left. repeat eexists; eauto. 
    intros [[u Hu [v Kv E]]|Ka]; repeat eexists; eauto using tapp_cons_x, tapp_nil_cons. 
Qed.

Lemma traces_deriv_dot_2 a i (H K: traces'): ~ (H (tnil a)) ->
  traces_deriv a i (H*K) == traces_deriv a i H * K.
Proof.
  intros Hnil w; simpl; unfold traces_deriv, traces_dot, pw2.
   split. 
    intros [[b|b j u] Hu [v Kv E]].
     apply tapp_nil_x_eq in E as [-> <-]. now elim Hnil. 
     inversion E. subst. clear E. repeat eexists; eauto. 
    intros [u Hu [v Kv E]]; repeat eexists; eauto using tapp_cons_x. 
Qed.

Lemma traces_deriv_itr a i (H: traces'): 
  traces_deriv a i (H^+) == traces_deriv a i H * H^*.
Proof.
  rewrite str_itr. apply antisym. 
  - intro w.
    intros [n Hn]. induction n in a, i, w, Hn; simpl in Hn.
     repeat eexists; eauto. 2: apply tapp_x_nil. now left.
     destruct Hn as [[b|b j v] Hv [u Hu Hw]].
      apply tapp_nil_x_eq in Hw as [-> <-]. apply IHn, Hu. 
      inversion Hw. subst. clear Hw. repeat eexists; eauto. right. eexists; eauto.
  - intros w [u Hu [v [Hv|[n Hv]] Hw]]. 
     destruct v as [b|]. 2: elim Hv. apply tapp_x_nil_eq in Hw as [-> <-]. now exists O. 
     exists (S n). repeat eexists; eauto using tapp_cons_x.
Qed.


(** ** particular elements *)

(** sub-identities *)
Definition tinj (p: State -> Prop): traces :=
  fun w => match w with tnil a => p a | _ => False end.

(** all traces consisting of the single letter [i] *)
Definition tsingle (i: Sigma): traces := 
  fun w => match w with tcons _ j (tnil _) => i=j | _ => False end.

Lemma traces_deriv_inj a i p: traces_deriv a i (tinj p) == 0. 
Proof. now intro. Qed.

Lemma traces_deriv_single a i j: traces_deriv a i (tsingle j) == ofbool (eqb i j).
Proof.
  intros [b|???]. 
    unfold traces_deriv. simpl. case eqb_spec; simpl; intuition; discriminate.
    unfold traces_deriv. simpl. case eqb_spec; reflexivity. 
Qed.



(** * Typed traces *)

(** we assume two functions [src] (source) and [tgt] (target), to type letters *)
Variables src tgt: Sigma -> positive.

(** a trace is well typed if consecutive letters can be composed
   according to their types (states are completely ignored) *)
Inductive typed: positive -> positive -> trace -> Prop :=
| ttnil: forall n a, typed n n (tnil a)
| ttcons: forall a i m w, typed (tgt i) m w -> typed (src i) m (tcons a i w).

(** a set of traces is well typed if all its elements are *)
Definition typed' n m (L: trace -> Prop) := forall u, L u -> typed n m u.


(** administrative lemmas for constructing well-typed sets of traces *)
Lemma typed'_bot n m: typed' n m bot.
Proof. intros ? []. Qed.

Lemma typed'_cup n m (x y: traces): typed' n m x -> typed' n m y -> typed' n m (x \cup y).
Proof. intros ? ? ? [|]; eauto. Qed.

Lemma typed'_cap n m (x y: traces): typed' n m x -> typed' n m y -> typed' n m (x \cap y).
Proof. intros ? ? ? []; eauto. Qed.

Lemma tapp_typed (u v w: trace): tapp u v w -> 
  forall n m p, typed n m u -> typed m p v -> typed n p w.
Proof.
  induction 1; intros n m p Hu Hv. 
   now inversion_clear Hu. 
   now inversion_clear Hu. 
   inversion_clear Hu. constructor. eapply IHtapp; eassumption.
Qed.

Lemma typed'_dot n m p (x y: traces'): typed' n m x -> typed' m p y -> typed' n p (x*y).
Proof. intros Hx Hy w [u Hu [v Hv H]]. eapply tapp_typed; eauto. Qed.

Lemma typed'_one n: typed' n n (one tt).
Proof. intros [|] []. constructor. Qed.

Lemma typed'_inj n p: typed' n n (tinj p).
Proof. intros [|? ? ?]. constructor. intros []. Qed.

Lemma typed'_iter n (x y: traces') i: typed' n n x -> typed' n n y -> typed' n n (traces_iter y x i).
Proof. intros Hx Hy. induction i. assumption. eapply typed'_dot; eassumption. Qed.

Lemma typed'_itr n (x: traces'): typed' n n x -> typed' n n (x^+).
Proof. intros Hx w [i Hw]. eapply typed'_iter; eassumption. Qed.

Lemma typed'_str n (x: traces'): typed' n n x -> typed' n n (x^*).
Proof. intros Hx w [i Hw]. eapply typed'_iter in Hw; eauto using typed'_one. Qed.

Lemma typed'_single i: typed' (src i) (tgt i) (tsingle i).
Proof. red.
intros [?|? ? [|]] [].
do 2 constructor.
Qed.

(** ** packing typed traces as a residuated Kleene lattice *)

(** we encapsulate traces into well-typed ones using a sig-type *)
Definition ttraces n m := sig (typed' n m). 

(** restriction of an arbitrary set of traces to those that are well-typed *)
Program Definition restrict n m (x: traces): ttraces n m := fun w => typed n m w /\ x w. 
Next Obligation. now intros w [? _]. Qed.

Lemma is_typed n m (x: ttraces n m) w: proj1_sig x w -> typed n m w.
Proof. destruct x as [x Hx]. apply Hx. Qed.

Section l.
Variables n m: positive. 
Implicit Types x y: ttraces n m.


(** we directly embed all operations from untyped traces, except for
   top elements and residuals, which have to be restricted. (So that
   typed traces are not entirely a sub-algebra of traces.) *)


(** *** lattice structure *)

Definition ttraces_leq x y := proj1_sig x <== proj1_sig y.
Definition ttraces_weq x y := proj1_sig x == proj1_sig y.
Program Definition ttraces_cup x y: ttraces n m := proj1_sig x \cup proj1_sig y. 
Next Obligation. apply typed'_cup; apply proj2_sig. Qed. 
Program Definition ttraces_cap x y: ttraces n m := proj1_sig x \cap proj1_sig y. 
Next Obligation. apply typed'_cap; apply proj2_sig. Qed. 
Program Definition ttraces_neg x: ttraces n m := restrict n m (! proj1_sig x). 
Program Definition ttraces_bot: ttraces n m := fun _ => False.
Next Obligation. apply typed'_bot. Qed.
Program Definition ttraces_top: ttraces n m := typed n m.
Next Obligation. now intros ? ?. Qed. 

Canonical Structure ttraces_lattice_ops := 
  lattice.mk_ops (ttraces n m) ttraces_leq ttraces_weq 
  ttraces_cup ttraces_cap ttraces_neg ttraces_bot ttraces_top.

Global Instance ttraces_lattice_laws: lattice.laws (BDL+STR+DIV) ttraces_lattice_ops.
Proof.
  constructor; simpl; unfold ttraces_leq, ttraces_weq; intros.
   constructor. 
    intro. apply pw_laws.
    intros x y z. apply pw_laws. 
   apply weq_spec.
   apply cup_spec.
   apply cap_spec.
   right. intros ? ? []. 
   right. intros x u. refine (is_typed _ _). 
   apply cupcap_. 
   discriminate.
   discriminate.
Qed.

End l.

(** *** monoid structure *)

Program Definition ttraces_dot n m p (x: ttraces n m) (y: ttraces m p): ttraces n p := 
  traces_dot tt tt tt x y. 
Next Obligation. eapply typed'_dot; eapply proj2_sig. Qed.

Program Definition ttraces_ldv n m p (x: ttraces n m) (y: ttraces n p): ttraces m p := 
  restrict m p (traces_ldv tt tt tt x y).

Program Definition ttraces_rdv n m p (x: ttraces m n) (y: ttraces p n): ttraces p m := 
  restrict p m (traces_rdv tt tt tt x y).

Program Definition ttraces_one n: ttraces n n := traces_one tt.
Next Obligation. apply typed'_one. Qed.

Program Definition ttraces_cnv n m (x: ttraces n m): ttraces m n := fun w => False.
Next Obligation. intros ? []. Qed.

Program Definition ttraces_iter n (y x: ttraces n n) i: ttraces n n := traces_iter y x i.
Next Obligation. apply typed'_iter; apply proj2_sig. Qed.

Program Definition ttraces_itr n (x: ttraces n n): ttraces n n := traces_itr tt x.
Next Obligation. apply typed'_itr, proj2_sig. Qed.

Program Definition ttraces_str n (x: ttraces n n): ttraces n n := traces_str tt x.
Next Obligation. apply typed'_str, proj2_sig. Qed.

Canonical Structure ttraces_monoid_ops := 
  monoid.mk_ops _ ttraces_lattice_ops 
  ttraces_dot ttraces_one ttraces_itr ttraces_str ttraces_cnv ttraces_ldv ttraces_rdv.

Notation ttraces' n m := (ttraces_monoid_ops n m).

Global Instance ttraces_monoid_laws: monoid.laws (BDL+STR+DIV) ttraces_monoid_ops.
Proof.
  assert(H: monoid.laws (DL+STR) ttraces_monoid_ops).
   apply (laws_of_faithful_functor (f':=fun _ => tt) 
     (f:=fun n m => @proj1_sig _ _: ttraces' n m -> traces)); trivial.
    constructor; try (discriminate || reflexivity).
    constructor; trivial; try discriminate; now intros ? ? ?. 
  constructor; try (intro; discriminate); (try now left); intros. 
   apply ttraces_lattice_laws. 
   apply dotA. 
   apply dot1x.
   right. apply dotx1. 
   apply str_refl.
   apply str_cons.
   now apply str_ind_l. 
   apply itr_str_l. 
  simpl. 
   setoid_rewrite <-(ldv_spec (n:=tt) (m:=tt) (p:=tt)).
   split. intros H' w Hw. apply H', Hw. 
   intros H' w Hw. split. eapply is_typed, Hw. apply H', Hw.
  simpl. 
   setoid_rewrite <-(rdv_spec (n:=tt) (m:=tt) (p:=tt)).
   split. intros H' w Hw. apply H', Hw. 
   intros H' w Hw. split. eapply is_typed, Hw. apply H', Hw.
Qed.

(** ** particular elements *)

Program Definition ttinj n p: ttraces n n := tinj p.
Next Obligation. apply typed'_inj. Qed.

Program Definition tatom n a: ttraces n n := eq (tnil a).
Next Obligation. intros ? <-. constructor. Qed.

Program Definition ttsingle (i: Sigma): ttraces (src i) (tgt i) := tsingle i. 
Next Obligation. apply typed'_single. Qed.

Program Definition tsingle' a i b: ttraces (src i) (tgt i) := eq (tcons a i (tnil b)).
Next Obligation. intros ? <-. do 2 constructor. Qed.

Lemma atom_single_atom a i b: tatom _ a * ttsingle i * tatom _ b == tsingle' a i b.
Proof.
  intro x. split. 
  - intros [uv [u <- [v Hv Huvw]] [w <- Huvw']]. destruct v as [|c j [d|]]; try elim Hv. 
    destruct Hv. inversion Huvw. simpl. subst. setoid_rewrite <- (tapp_tail_head Huvw').
    now apply tapp_x_nil_eq in Huvw' as [-> ->].  
  - intros <-. exists (tcons a i (tnil b)). eexists. reflexivity. 
    exists (tcons a i (tnil b)). now idtac. constructor. 
    eexists. reflexivity. constructor; constructor. 
Qed.

(** ** properties of the embedding of untyped sets of traces into
   typed ones, through restriction *)

Global Instance restrict_leq n m: Proper (leq ==> leq) (restrict n m).
Proof. intros x y H w [? ?]. split. assumption. now apply H. Qed.
Global Instance restrict_weq n m: Proper (weq ==> weq) (restrict n m) := op_leq_weq_1.

Lemma restrict_0 n m: restrict n m (zer tt tt) == 0. 
Proof. intros [|]; simpl; tauto. Qed.

Lemma restrict_1 n: restrict n n (one tt) == 1. 
Proof. intros [b|]; simpl. 2: tauto. intuition constructor. Qed.

Lemma restrict_pls n m (x y: traces'): restrict n m (x + y) == restrict n m x + restrict n m y. 
Proof. intros w; simpl; unfold pw2. tauto. Qed.

Lemma restrict_dot n m p (x y: traces'):
  typed' n m x -> typed' m p y -> 
  restrict n p (x * y) == restrict n m x * restrict m p y. 
Proof. 
  intros Hx Hy w; simpl. split. 
   intros [Hw [u Hu [v Hv H]]]. repeat eexists; eauto. 
   intros [u [Hu Hu'] [v [Hv Hv'] H]]. split. 
    eapply tapp_typed; eassumption. 
    repeat eexists; eassumption.
Qed.

Lemma restrict_iter n (x y: traces') i: typed' n n x -> typed' n n y ->
  restrict n n (traces_iter y x i) == ttraces_iter (restrict n n y) (restrict n n x) i.
Proof.
  intros Hx Hy. induction i. simpl. now unfold ttraces_weq.
  simpl. setoid_rewrite restrict_dot. now setoid_rewrite IHi.
  assumption. now apply typed'_iter.
Qed.

Lemma restrict_itr n (x: traces'): typed' n n x -> restrict n n (x^+) == restrict n n x^+. 
Proof.
  intros Hx w. simpl. split.
   intros [H [i Hw]]. exists i. apply restrict_iter; trivial. now split. 
   intros [i Hw]. split. eapply typed'_iter. 3: eassumption. now intros ? []. now intros ? [].
   exists i. eapply restrict_iter; eassumption. 
Qed.

Lemma restrict_inj n p: restrict n n (tinj p) == ttinj n p.
Proof.
  intros [b|b i w]; simpl. 2: simpl; lattice.
   split. now intros [_ H]. 
   intros ?. split. constructor. assumption.
Qed.

Lemma restrict_single i: restrict _ _ (tsingle i) == ttsingle i.
Proof.
  intros [a|a j [b|???]]; simpl; try lattice.
   split. now intros [_ H]. 
   intros <-. repeat constructor. 
Qed.


End l.

Arguments tnil {State} a.
Arguments tcons {State} a i w.
Arguments tsingle {State} i _.
Arguments tatom {State src tgt} n a.
Arguments ttsingle {State src tgt} i.
Arguments tsingle' {State src tgt} a i b.

Notation traces' State := (traces_monoid_ops State traces_tt traces_tt).


