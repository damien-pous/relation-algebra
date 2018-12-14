(************************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the        *)
(*    terms of the GNU Lesser General Public License version 3          *)
(*              (see file LICENSE for more details)                     *)
(*                                                                      *)
(*  Copyright 2018: Christian Doczkal. (CNRS, LIP - ENS Lyon, UMR 5668) *)
(************************************************************************)

Require Import Setoid Morphisms.
Require Import kat normalisation rewriting kat_tac comparisons rel relalg boolean.

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Unset Strict Implicit.
Set Bullet Behavior "Strict Subproofs".

(** * fhrel: The model of finite heterogeneous relations *)

(** Tactic for eliminating boolean logical connectives. Usually
followed by [firstoder]. This needs explicit calls to setoid_rewrite
do work under binders *)

Instance: Proper (iff ==> iff ==> iff ==> iff) and3. firstorder. Qed.
Instance: Proper (iff ==> iff ==> iff ==> iff ==> iff) and4. firstorder. Qed.
Instance: Proper (iff ==> iff ==> iff ==> iff ==> iff ==> iff) and5. firstorder. Qed.
Instance: Proper (iff ==> iff ==> iff ==> iff) or3. firstorder. Qed.
Instance: Proper (iff ==> iff ==> iff ==> iff ==> iff) or4. firstorder. Qed.

Ltac to_prop := 
  repeat first 
         [ setoid_rewrite <- (rwP andP)
         | setoid_rewrite <- (rwP orP)
         | setoid_rewrite <- (rwP and3P)
         | setoid_rewrite <- (rwP existsP)
         | setoid_rewrite <- (rwP forallP) 
         | setoid_rewrite <- (rwP eqP)
         | (* last because implyP also matches [exists _,_] *)
           setoid_rewrite <- (rwP implyP)]. 

(** Use phantom types to trigger inference of finType structures *)
Section FHRelType.
  Variables A B : finType.
  Definition fhrel_type := A -> B -> bool.
  Definition fhrel_of of phant A & phant B := fhrel_type.
End FHRelType.

Notation "{ 'fhrel' A & B }" := (fhrel_of (Phant A) (Phant B))
  (at level 0, format "{ 'fhrel'  A  &  B }") : type_scope.

(** Heterogeneous binary relations [hrel X Y] (i.e., [X -> Y -> Prop]) are
already declared as a model of relation algebra in the module
[rel]. Thus, we only need to provide the model for finite and
decidable relations between finite types [{fhrel A & B}] *)

Section FHRel.
Implicit Types A B C : finType.

(** ** Lattice Operations *)

(** The relations [e1 ≦ e2] and [e1 ≡ e2] and the lattice operations
are not declared but derived (up to conversion) via the powerset
construction on the lattice of booleans 
<<
Section LatticeOps.
Variables (A B : finType) (e1 e2 : {fhrel A & B}).
Implicit Types (x : A) (y : B).

Definition fhrel_weq := e1 =2 e2.
Definition fhrel_leq := forall x y, e1 x y -> e2 x y.
Definition fhrel_cup := fun x y => e1 x y || e2 x y.
Definition fhrel_cap := fun x y => e1 x y && e2 x y.
Definition fhrel_neg := fun x y => ~~ (e1 x y).
Definition fhrel_top := fun x y => true.
Definition fhrel_bot := fun x y => false.
End LatticeOps.
>>
*)

Canonical Structure fhrel_lattice_ops A B := 
  lattice.mk_ops {fhrel A & B} lattice.leq weq cup cap neg bot top.

Arguments lattice.leq : simpl never.
Arguments lattice.weq : simpl never.

(** Obtain the lattice laws using the standard powerset construction *)
Global Instance fhrel_lattice_laws A B: 
  lattice.laws (BL+STR+CNV+DIV) (fhrel_lattice_ops A B) := pw_laws _.

Lemma fhrel_leq_dec A B (e1 e2 : {fhrel A & B}) : decidable (e1 ≦ e2).
Proof. 
  apply: (@decP _ [forall x, forall y, e1 x y ==> e2 x y]).
  apply: (equivP idP); to_prop; reflexivity.
Qed.

Lemma fhrel_weq_dec A B (e1 e2 : {fhrel A & B}) : decidable (e1 ≡ e2).
Proof. 
  apply: (@decP _ [forall x, forall y, e1 x y == e2 x y]).
  apply: (equivP idP); to_prop; reflexivity.
Qed.

(** Enable rewriting of [lattice.leq] and [weq] using Ssreflect's rewrite tactic *)
Global Instance leq_rewrite_relation ops : RewriteRelation (@lattice.leq ops).
Global Instance weq_rewrite_relation ops : RewriteRelation (@weq ops).

(** ** Monoid Operations

We implement the monoid operations using Ssreflect's boolean
quantifiers and the transitive closure operation provided by the path
library *)

Section MonoidOps.
Variables (A B C : finType).

Definition fhrel_dot (e1 : {fhrel A & B}) (e2 : {fhrel B & C}) : {fhrel A & C} := 
  fun x y => [exists z, e1 x z && e2 z y].
Definition fhrel_cnv (e : {fhrel A & B}) : {fhrel B & A} := 
  fun x y => e y x.
Definition fhrel_str (e : {fhrel A & A}) : {fhrel A & A} := 
  connect e.
Definition fhrel_one : {fhrel A & A} := 
  @eq_op A.
Definition fhrel_rdv (e1 : {fhrel B & A}) (e2 : {fhrel C & A}) : {fhrel C & B} := 
  fun j i => [forall k, e1 i k ==> e2 j k].
Definition fhrel_ldv (e1 : {fhrel A & B}) (e2 : {fhrel A & C}) : {fhrel B & C} := 
  fun i j => [forall k, e1 k i ==> e2 k j].
Definition fhrel_inj (p : pred A) := 
  fun x y => (x == y) && p x.
End MonoidOps.

Definition fhrel_itr A (e : {fhrel A & A}) : {fhrel A & A} := 
  fhrel_dot e (connect e).

Canonical fhrel_monoid_ops := 
  monoid.mk_ops finType fhrel_lattice_ops
                fhrel_dot
                fhrel_one
                fhrel_itr 
                fhrel_str 
                fhrel_cnv 
                fhrel_ldv 
                fhrel_rdv.

(** Ensure that the [fhrel_*] definitions simplify, given enough arguments. *)
Arguments fhrel_dot {_ _ _} _ _ /.
Arguments fhrel_cnv {_ _} _ _ /.
Arguments fhrel_one {_} _ _ /.
Arguments fhrel_str {_} _ _ /.
Arguments fhrel_ldv {_} _ _ /.
Arguments fhrel_rdv {_} _ _ /.
Arguments fhrel_inj {_} _ _ _ /.

Lemma connect_iter (A : ob fhrel_monoid_ops) (e : fhrel_monoid_ops A A) (x y : A): 
    connect e x y <-> (exists u : nat, rel.iter A e u x y).
Proof.
  split.
  - case/connectP => p pth_p lst_p. exists (size p).
    elim: p x pth_p lst_p => /= [x _ -> // | z p IHp x /andP [xz pth_p] lst_p].
    exists z => //. exact: IHp.
  - case => n. elim: n x => /= [x <- // |n IHn x [z xz H]]. 
    exact: connect_trans (connect1 xz) (IHn _ _).
Qed.

(** We obtain the monoid laws using a faithful functor to the hrel model *)
Definition hrel_of (A B : finType) (e : {fhrel A & B}) : hrel A B := fun x y => e x y.
Ltac hrel_prop := do ! move => ?; rewrite /hrel_of /=; to_prop; by firstorder.

Lemma hrel_of_morphism (A B : finType) : morphism (BDL+STR+CNV+DIV) (@hrel_of A B).
Proof.
  split; try done; try hrel_prop.
  move => e1 e2 H x y. apply/eq_bool_iff. exact: H.
Qed.

Lemma hrel_of_functor : functor (BDL+STR+CNV+DIV) hrel_of.
Proof.
  apply (@Build_functor (BDL+STR+CNV+DIV) fhrel_monoid_ops hrel_monoid_ops id hrel_of).
  all: try done. all: try hrel_prop.
  - apply: hrel_of_morphism.
  - move => _ A e x y. rewrite /hrel_of/= /fhrel_itr /hrel_itr /=. to_prop. 
    setoid_rewrite connect_iter. by firstorder.
  - move => _ A e x y. exact: connect_iter.
Qed.

Lemma fhrel_monoid_laws_BDL: monoid.laws (BDL+STR+CNV+DIV) fhrel_monoid_ops.
Proof.
  eapply (laws_of_faithful_functor hrel_of_functor) => //.
  move => A B e1 e2 H x y. apply/eq_bool_iff. exact: H.
Qed.

Global Instance hrel_monoid_laws: monoid.laws (BL+STR+CNV+DIV) fhrel_monoid_ops.
Proof.
  case fhrel_monoid_laws_BDL => *.
  split; try assumption. exact: fhrel_lattice_laws.
Qed.

(** In ssreflect /= is used pervasively, so we block the
simplification of relation operators. Unfold selectively by using
[rewrite /dot/=] *)
Arguments dot : simpl never.
Arguments cnv : simpl never.
Arguments str : simpl never.
Arguments itr : simpl never.
Arguments lattice.leq : simpl never.
Arguments lattice.weq : simpl never.
Arguments monoid.one : simpl never.
Hint Unfold monoid.one.

(** Lemmas to eliminate [1 n m] *)
Lemma hrel_oneE (n : Set) a b : (1 : hrel n n) a b <-> a = b.
Proof. reflexivity. Qed.
Lemma fhrel_oneE A a b : (1 : {fhrel A & A}) a b = (a == b).
Proof. reflexivity. Qed.
Definition oneE := (hrel_oneE,fhrel_oneE).

(** The following is required since [top' x y] tries to infer an
[hrel] instance and then fails with a universe inconsistency as finite
types to not necessarily live in [Set] *)
Definition ftop_def (A B : finType) of phant A & phant B := 
  (@top (@mor fhrel_monoid_ops A B)).
Notation ftop A B := (ftop_def (Phant A) (Phant B)).

Definition fzero_def (A B : finType) of phant A & phant B := 
  (@bot (@mor fhrel_monoid_ops A B)).
Notation fzero A B := (fzero_def (Phant A) (Phant B)).

Definition fone_def (A : finType) of phant A := 
  (@one fhrel_monoid_ops A).
Notation fone A := (fone_def (Phant A)).

Arguments ftop_def A B /.
Arguments fzero_def A B /.
Arguments fone_def A /.

(** ** KAT Operations *)

(** "decidable" sets or predicates: Boolean functions *)
Definition fdset: ob fhrel_monoid_ops -> lattice.ops := pw_ops bool_lattice_ops.

Canonical Structure fhrel_kat_ops := 
  kat.mk_ops fhrel_monoid_ops fdset (@fhrel_inj).

Global Instance fhrel_kat_laws: kat.laws fhrel_kat_ops.
Proof.
  split.
  - by eapply lower_laws. 
  - move => A. by eapply lower_lattice_laws.
  - move => A.
    have H : Proper (lattice.leq ==> lattice.leq) (@fhrel_inj A).
    { move => e1 e2 H x y /=. by case: (_ == _) => //=. }
    split => //=.
    + move => x y. rewrite !weq_spec. by intuition.
    + move => _ f g x y /=. by case: (_ == _); case (f x); case (g x).
    + move => _ x y /=. by rewrite andbF.
  - move => A x y /=. by rewrite andbT.
  - move => A p q x y /=. rewrite /dot/=.
    apply/eq_bool_iff. to_prop. by firstorder;subst.
Qed.

(** ** Cardinality 
For finite relations we obtain cardinality operation by coercing
heterogeneous relations to prediactes on pairs *)

Definition fhrel_pred (aT rT: finType) (e : {fhrel aT & rT}) := 
  [pred x : aT * rT | e x.1 x.2].

Canonical fhrelPredType (aT rT: finType) := 
  @mkPredType (aT * rT) ({fhrel aT & rT}) (@fhrel_pred _ _).
Coercion fhrel_pred : fhrel_of >-> simpl_pred.

(* TOTHINK: Instanciate the cardinality development with this? *)
(* Definition fhrel_card (aT rT: finType) (e : {fhrel aT & rT}) := #|e|. *)

Section CardinalityBase.
Variables (aT rT : finType).
Implicit Types (e : {fhrel aT & rT}).

Lemma leq_card e e': e ≦ e' -> #|e| <= #|e'|.
Proof. move => A. apply: subset_leq_card. apply/subsetP => x. exact: A. Qed.

Lemma weq_card e e' : e ≡ e' -> #|e| = #|e'|.
Proof. rewrite weq_spec (rwP eqP) eqn_leq => [[A B]]. by rewrite !leq_card. Qed.

Lemma fhrel_card0 : #|fzero aT rT| = 0%N.
Proof. exact: card0. Qed.

Lemma fhrel_cardT : #|ftop aT rT| = #|aT| * #|rT|.
Proof. exact: eq_card_prod. Qed.

Lemma fhrel_card1 : #|fone aT| = #|aT|.
Proof.
  rewrite -(on_card_preimset (f := (fun x => (x,x)))).
  - rewrite eq_cardT ?cardT //= => x. by rewrite !inE oneE eqxx.
  - exists fst => //= [[x y]]. by rewrite inE oneE /= => /eqP->.
Qed.

Lemma card_cnv e : #|e°| = #|e|.
Proof. 
  rewrite -(on_card_preimset (f := (fun x => (x.2,x.1)))).
  - apply: eq_card => [[x y]]. by rewrite !inE.
  - apply: onW_bij. apply: (Bijective (g := fun x => (x.2,x.1))); by case.
Qed.

Lemma card_cup e1 e2 : #|e1 + e2| = #|e1| + #|e2| - #|e1 ∩ e2|.
Proof. by rewrite (rwP eqP) -cardUI -addnBA // subnn addn0. Qed.

Lemma card_capL e1 e2 : #|e1 ∩ e2| <= #|e1|.
Proof. apply: leq_card. by lattice. Qed.

Lemma card_capR e1 e2 : #|e1 ∩ e2| <= #|e2|.
Proof. apply: leq_card. by lattice. Qed.

Definition dom e := [pred x | [exists y, e x y]].
Definition ran e := [pred y | [exists x, e x y]].

Lemma card_dom e : #|dom e| = #|e ⋅ ftop rT unit|.
Proof.
  rewrite -[in RHS](on_card_preimset (f := (fun x : aT => (x,tt)))).
  - apply: eq_card => x. rewrite !inE /dot /=. 
    by apply/eq_bool_iff;to_prop; firstorder.
  - apply: onW_bij. by apply: (Bijective (g := fst)) => [|[? []]].
Qed.

End CardinalityBase.

Lemma ran_dom {A B} {e : {fhrel A & B}} : ran e =i dom e°.
Proof. move => x. by rewrite !inE. Qed.

Lemma card_ran A B (e : {fhrel A & B}) : 
  #|ran e| = #|ftop unit _⋅e|.
Proof. 
  rewrite (eq_card ran_dom) card_dom -card_cnv. 
  apply: weq_card. rewrite /ftop_def. 
  (* Why does ra. fail here? -- se below *)
  by rewrite cnvdot cnvtop cnv_invol.
Qed.

(* TOTHINK: This is actually a theorem of hrel, but there is no easy
way to transfer. The same is true for [fhrel_injective] and
[fhrel_univalent] *)
Lemma fhrel_surjective A B (e : {fhrel A & B}) : is_surjective e <-> forall y, exists x, e x y.
Proof.
  split => [H y|H y ?].
  - case/exists_inP : (H y y (eqxx _)) => x. by exists x.
  - move/eqP<-. apply/exists_inP. case: (H y) => x exy. by exists x.
Qed.

Lemma surjective_card A B (e : {fhrel A & B}) : 
  is_surjective e -> #|B| <= #|e|.
Proof.
  move/fhrel_surjective => E. 
  pose f y := (xchoose (E y),y).
  have inj_f : injective f by move => x y [].
  rewrite -(card_codom inj_f). 
  apply: subset_leq_card. apply/subsetP => [[x y]] /codomP => [[y'] [-> <-]]. 
  rewrite inE /=. exact: (xchooseP (E y)).
Qed.

Lemma fhrel_injective A B (e : {fhrel A & B}) : 
  is_injective e <-> forall x x' y, e x y -> e x' y -> x = x'.
Proof.
  rewrite /is_injective; split => [H x x' y E1 E2|H x x' E].
  - apply/eqP. apply: (H x x'). by apply/exists_inP;exists y.
  - apply/eqP. case/exists_inP : E. exact: H.
Qed.

Lemma injective_card A B (e : {fhrel A & B}) : 
  is_injective e -> #|e| <= #|B|.
Proof. 
  move/fhrel_injective => inj_e.
  rewrite -(card_in_imset (f := @snd A B)) ?max_card //.
  move => [x y] [x' y']. rewrite !inE /= => E1 E2 ?; subst. 
  by rewrite (inj_e _ _ _ E1 E2).
Qed.

Lemma fhrel_univalent A B (e : {fhrel A & B}) : 
  is_univalent e <-> forall x y y', e x y -> e x y' -> y = y'.
Proof. 
  split => [/@injective_cnv/fhrel_injective|H]. 
  - rewrite /cnv/= => H ? ? ?; exact: H.
  - rewrite /is_univalent. cnv_switch. rewrite cnv1 cnvdot. 
    rewrite -/(is_injective _) fhrel_injective => ? ? ?. exact: H.
Qed.

Lemma univalent_card A B (e : {fhrel A & B}) : 
  is_univalent e -> #|e| <= #|A|.
Proof. move => ?. rewrite -card_cnv. exact: injective_card. Qed.

Lemma total_card A B (e : {fhrel A & B}) : 
  is_total e -> #|A| <= #|e|.
Proof. move => ?. rewrite -card_cnv. exact: surjective_card. Qed.

End FHRel.

Notation ftop A B := (ftop_def (Phant A) (Phant B)).
Notation fzero A B := (fzero_def (Phant A) (Phant B)).
Notation fone A := (fone_def (Phant A)).

Ltac fold_fhrel := ra_fold fhrel_monoid_ops.
Tactic Notation "fold_fhrel" "in" hyp_list(H) := ra_fold fhrel_monoid_ops in H.
Tactic Notation "fold_fhrel" "in" "*" := ra_fold fhrel_monoid_ops in *.

(** Note that, [subrel e f] (which is convertible to [e ≦ f] if [e]
and [f] are homogeneous relations over some finite type) and [e =2 f]
(which is convertible to [e ≡ f] even in the heterogeneous case) are
used pervasively in MathComp. Consequently, [fold_fhrel] can be used
to convert their statements into relation algebra statements. See
below for an examle: *)

(** This is [connect_sub] *)
Goal forall (T : finType) (e e' : rel T), subrel e (connect e') -> subrel (connect e) (connect e'). 
move => T e e'. fold_fhrel. move => H. rewrite H. ka. Abort.

(** This is [connect_eq] *)
Goal forall (T : finType) (e e' : rel T), e =2 e' -> connect e =2 connect e'.
move => T e e'. fold_fhrel. move => H. by rewrite H. Abort.
