(** * boolean: Booleans as a lattice, and as a monoid *)

Require Import monoid prop sups.

(** * Booleans as a lattice *)

Canonical Structure bool_lattice_ops: lattice.ops := {|
  leq := le_bool;
  weq := eq;
  cup := orb;
  cap := andb;
  neg := negb;
  bot := false;
  top := true
|}.

(** [is_true] is a bounded distributive lattice homomorphism from [bool] to [Prop].
   (Actually a Boolean lattice homomorphism, but we don't need it here.) *)
#[export] Instance mm_bool_Prop: morphism BDL is_true.
Proof.
  constructor; simpl.
  now auto.
  intros ? ?. now rewrite eq_bool_iff. 
  intros _ [|] [|]; firstorder. 
  intros _ [|] [|]; firstorder. 
  intros _. easy.
  tauto.
  intros _ [|]. firstorder auto with bool. easy.
Qed.

(* #[export] Instance mm_negb l: morphism l bool_lops (dual_ops bool_ops) negb. *)

(** we get most lattice laws by the faithful embedding into [Prop]  *)
#[export] Instance bool_lattice_laws: lattice.laws (BL+STR+CNV+DIV) bool_lattice_ops.
Proof. 
  assert(H: lattice.laws BDL bool_lattice_ops).
   apply (laws_of_injective_morphism is_true mm_bool_Prop).
   auto. 
   intros x y. apply eq_bool_iff.
  constructor; try apply H; (try now left); intros _ [|]; reflexivity. 
Qed.

(** simple characterisation of finite sups and infs in [bool] *)

Lemma is_true_sup I J (f: I -> bool): \sup_(i\in J) f i <-> (exists i, List.In i J /\ f i).
Proof. 
  unfold is_true. induction J; simpl. firstorder; discriminate. 
  rewrite Bool.orb_true_iff. firstorder congruence. 
Qed.

Lemma is_true_inf I J (f: I -> bool): \inf_(i\in J) f i <-> (forall i, List.In i J -> f i).
Proof. 
  unfold is_true. induction J; simpl. firstorder.
  rewrite Bool.andb_true_iff. firstorder congruence. 
Qed.




(** * Boolean as a (flat) monoid
   this is useful:
   - to construct boolean matrices, 
   - to consider regex.epsilon as a functor) *)

(** this monoid is flat: this is a one object category. 
   We use the following singleton type to avoid confusion with the
   singleton types of other flat structures *)
CoInductive bool_unit := bool_tt.

(** note that the trivial type information is simply ignored *)
Canonical Structure bool_ops: monoid.ops := {|
  ob := bool_unit;
  mor n m := bool_lattice_ops;
  dot n m p := andb;
  one n := true;
  itr n x := x;
  str n x := true;
  cnv n m x := x;
  ldv n m p x y := !x ⊔ y;
  rdv n m p x y := !x ⊔ y
|}.

(** shorthand for [bool], when a morphism is expected *)
Notation bool' := (bool_ops bool_tt bool_tt).

(** we actually have all laws on [bool] *)
#[export] Instance bool_laws: laws (BL+STR+CNV+DIV) bool_ops.
Proof.
  constructor; (try now left);repeat right; intros.
   apply bool_lattice_laws.
   apply capA.
   apply captx.
   apply weq_leq. simpl. apply capC.
   reflexivity.
   now intros ? ? ?.
   reflexivity.
   all: try setoid_rewrite <- le_bool_spec.
   all: try case x; try case y; try case z; reflexivity.
Qed.



(** * properties of the [ofbool] injection *)

Section ofbool.

Open Scope bool_scope.
Implicit Types a b c: bool.
Context {X: ops} {l} {L: laws l X} {n: ob X}.
Notation ofbool := (@ofbool X n).

Lemma andb_dot `{BOT ≪ l} a b: ofbool (a&&b) ≡ ofbool a ⋅ ofbool b.
Proof. 
  symmetry. case a. apply dot1x. 
  apply antisym. now apply weq_leq, dot0x. apply leq_bx. 
Qed.

Lemma orb_pls `{CUP+BOT ≪ l} a b: ofbool (a||b) ≡ ofbool a + ofbool b.
Proof. symmetry. case a; simpl. case b; simpl; lattice. lattice. Qed.

#[export] Instance ofbool_leq `{BOT ≪ l}: Proper (leq ==> leq) ofbool.
Proof. intros [|] b E; simpl. now rewrite E. apply leq_bx. Qed.

Lemma dot_ofboolx `{BOT ≪ l} b (x: X n n): ofbool b⋅x ≡ x⋅ofbool b.
Proof. case b; simpl. now rewrite dot1x, dotx1. now rewrite dot0x, dotx0. Qed.

End ofbool.

(** [is_true] is also monotone *)
#[export] Instance is_true_leq: Proper (leq ==> leq) is_true. 
Proof. intros [|] b E; simpl. now rewrite E. discriminate. Qed.
