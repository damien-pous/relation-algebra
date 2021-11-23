(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2021: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * srel: heterogeneous binary relations between setoids *)

(** counterpart to module [rel], where we provide a KAT model of relations on setoids
    relations have to be invariant under the setoid equalities, the identity relation 
    is defined as the setoid equality rather than [Logic.eq], Kleene star is defined 
    accordingly.
 *)

Require Bool.
Require Export boolean prop.
Require Import kat rel.

(* Set Universe Polymorphism. *)
(* Set Printing Universes.  *)

(** base type for setoids ; 
    if there is standard one in the standard library, we might want to switch to it 
    it could also be nice to have [lattice.weq] set up using such a structure, to share notation and lemmas
 *)
Record EqType := {
    type_of:> Type@{U};
    Eq: relation type_of;
    Equivalence_Eq: Equivalence Eq
  }.
#[export] Existing Instance Equivalence_Eq.

(* note: would be natural to try to define a counterpart to [lattice.pw_ops] 
   for equality preserving funtions from A to X (using the following record type as carrier)
 *)
Record spw (A: EqType) (X: lattice.ops) := {
    spw_bod:> lattice.pw_ops X A; (* A->X *)
    spw_Eq: Proper (Eq A ==> weq) spw_bod
  }.
(* #[export] Existing Instance spw_Eq. *)
(*
  but:
  - this requires laws on X (preservation of weq) to lift the operations, e.g., 
    the lift of [cup] requires [cup_weq] in order to preserve [Eq A]
  - this would force us to use [Proper (Eq A ==> weq)] rather than [pwr A weq] as equality 
    in order to obtain [Proper (Eq A ==> Eq A ==> weq)] for relations, 
    which is possibly not so convenient
*)

(** * setoid-preserving relations as a lattice *)

(** setoid-preserving relations *)
Record srel (n m: EqType) := {
    (* we use [hrel_lattice_ops n m] below rather than [hrel n m], so that the coercion has codomain [car] rather than [hrel] *)
    rel_of:> hrel_lattice_ops n m (* hrel n m *);
    srel_Eq: Proper (Eq n ==> Eq m ==> iff) rel_of
  }.
Arguments rel_of {_ _}.
#[export] Existing Instance srel_Eq.

(** setoid-preserving relations as a lattice; actually a sublattice of that of plain relations *)
Section s.
 Variables n m: EqType.
 Definition srel_leq (R S: srel n m): Prop := R ≦ S.  
 Definition srel_weq (R S: srel n m): Prop := R ≡ S.  
 Program Definition srel_cup (R S: srel n m): srel n m := {| rel_of := R ⊔ S |}.
 Next Obligation. now rewrite H, H0. Qed.
 Program Definition srel_cap (R S: srel n m): srel n m := {| rel_of := R ⊓ S |}.
 Next Obligation. now rewrite H, H0. Qed.
 Program Definition srel_neg (R: srel n m): srel n m := {| rel_of := !R |}.
 Next Obligation. now rewrite H, H0. Qed.
 Program Definition srel_bot: srel n m := {| rel_of := bot |}.
 Next Obligation. tauto. Qed.
 Program Definition srel_top: srel n m := {| rel_of := top |}.
 Next Obligation. tauto. Qed.
 Canonical Structure srel_lattice_ops: lattice.ops := {|
  car := srel n m;
  leq := srel_leq;
  weq := srel_weq;
  cup := srel_cup;
  cap := srel_cap;
  neg := srel_neg;
  bot := srel_bot;
  top := srel_top
 |}.
 Arguments srel_leq _ _ /. 
 Arguments srel_weq _ _ /. 
 Arguments srel_cup _ _ /. 
 Arguments srel_cap _ _ /. 
 Arguments srel_neg _ /. 
 Arguments srel_bot /. 
 Arguments srel_top /. 

 (** lattices laws follow from the fact that we have a sublattice of plain relations *)
 #[export] Instance srel_lattice_laws: lattice.laws (BDL+STR+CNV+DIV) srel_lattice_ops.
 Proof. apply (laws_of_injective_morphism rel_of); trivial. now split. Qed.

End s.

(** * setoid-preserving relations as a Kleene category *)

(** not a subcategory of plain relations: we have to modify [1] and [x^*] *)
Section RepOps.
 Implicit Types n m p : EqType.

 Program Definition srel_one n: srel n n := 
  {| rel_of := Eq n |}.

 Program Definition srel_dot n m p (x: srel n m) (y: srel m p): srel n p := 
  {| rel_of := x⋅y |}.
 Next Obligation.
   split; intros [z H1 H2].
    rewrite H in H1. rewrite H0 in H2. now exists z. 
    rewrite <-H in H1. rewrite <-H0 in H2. now exists z. 
 Qed. 

 Program Definition srel_cnv n m (x: srel n m): srel m n := 
   {| rel_of := x° |}.
 Next Obligation. unfold hrel_cnv. now rewrite H, H0. Qed.
 
 Program Definition srel_ldv n m p (x: srel n m) (y: srel n p): srel m p := 
  {| rel_of := x -o y |}.
 Next Obligation. unfold hrel_ldv. setoid_rewrite H. setoid_rewrite H0. reflexivity. Qed. 

 Program Definition srel_rdv n m p (x: srel m n) (y: srel p n): srel p m := 
  {| rel_of := y o- x |}.
 Next Obligation. unfold hrel_rdv. setoid_rewrite H. setoid_rewrite H0. reflexivity. Qed. 

 Section i.
  Variable n: EqType.
  Variable x: srel n n.
  (** finite iterations of a relation *)
  Fixpoint iter u: srel n n := match u with O => srel_one n | S u => srel_dot _ _ _ x (iter u) end.
  Program Definition srel_str: srel n n := {| rel_of i j := exists u, rel_of (iter u) i j |}.
  Next Obligation. setoid_rewrite H. setoid_rewrite H0. reflexivity. Qed.
  Definition srel_itr: srel n n := srel_dot n n n x srel_str.
 End i.

 Arguments srel_dot [_ _ _] _ _/. 
 Arguments srel_ldv [_ _ _] _ _/. 
 Arguments srel_rdv [_ _ _] _ _/. 
 Arguments srel_cnv [_ _] _ /. 
 Arguments srel_str [_] _ /. 
 Arguments srel_itr [_] _ /. 
 Arguments srel_one {_} /. 
End RepOps.

Canonical Structure srel_monoid_ops :=  
  monoid.mk_ops EqType srel_lattice_ops srel_dot srel_one srel_itr srel_str srel_cnv srel_ldv srel_rdv.

(** we cannot use [monoid.laws_of_faithful_functor]: [1] and [_^*] are not preserved by [rel_of];
    nevertheless, we can reuse [hrel_monoid_laws] for quite a few axioms; and we just reprove the remaining ones
 *)
#[export] Instance srel_monoid_laws: monoid.laws (BDL+STR+CNV+DIV) srel_monoid_ops.
Proof.
  constructor; (try now left); intros. 
   apply srel_lattice_laws.
   apply (dotA (laws:=hrel_monoid_laws)).
   intros i j. split.
    intros [k ik kj]. simpl in ik; now rewrite ik. 
    intro. exists i. simpl; reflexivity. assumption. 
   apply (cnvdot_ (laws:=hrel_monoid_laws)).
   apply (cnv_invol (laws:=hrel_monoid_laws)).
   intros i j ij. now apply (cnv_leq (laws:=hrel_monoid_laws)).
   intros i j E. exists O. exact E.
   intros i k [j Hij [u Hjk]]. exists (S u). now exists j. 
   assert (E: forall i, (iter n x i: srel n n) ⋅ z ≦ z).
    induction i. simpl. intros h k [l hl lk]. simpl in hl. now rewrite hl. 
    rewrite <-H0 at 2. transitivity (x⋅((iter n x i: srel n n)⋅z)). 
     cbn. firstorder congruence. now apply (dot_leq (H:=hrel_monoid_laws)).  
    intros i j [? [? ?] ?]. eapply E. repeat eexists; eauto.
   reflexivity. 
   apply (capdotx (laws:=hrel_monoid_laws)).
   apply (ldv_spec (laws:=hrel_monoid_laws)).
   apply (rdv_spec (laws:=hrel_monoid_laws)).
Qed.

(** * setoid-preserving relations as a Kleene category with tests *)

(** setoid-preserving tests as a Boolean lattice;
    we redo everything, for lack of nice generic operations on [spw]
 *)
Section tests.
 Variable A: ob srel_monoid_ops.
 Record dset := {
     (* like above, we use a type which gives a better codomain for the coercion *)
     dset_bod:> lattice.pw_ops bool_lattice_ops A; (* A -> bool *)
     dset_Eq: Proper (Eq A ==> eq) dset_bod;
   }.
 #[export] Existing Instance dset_Eq.
 (** all operations ar imported from [lattice.pw_ops]  *)
 Definition dset_leq (R S: dset): Prop := R ≦ S.  
 Definition dset_weq (R S: dset): Prop := R ≡ S.  
 Program Definition dset_cup (R S: dset): dset := {| dset_bod := R ⊔ S |}.
 Next Obligation. now rewrite H. Qed.
 Program Definition dset_cap (R S: dset): dset := {| dset_bod := R ⊓ S |}.
 Next Obligation. now rewrite H. Qed.
 Program Definition dset_neg (R: dset): dset := {| dset_bod := !R |}.
 Next Obligation. now rewrite H. Qed.
 Program Definition dset_bot: dset := {| dset_bod := bot |}.
 Program Definition dset_top: dset := {| dset_bod := top |}.
 Canonical Structure dset_lattice_ops: lattice.ops := {|
  car := dset;
  leq := dset_leq;
  weq := dset_weq;
  cup := dset_cup;
  cap := dset_cap;
  neg := dset_neg;
  bot := dset_bot;
  top := dset_top
 |}.
 Arguments dset_leq _ _ /. 
 Arguments dset_weq _ _ /. 
 Arguments dset_cup _ _ /. 
 Arguments dset_cap _ _ /. 
 Arguments dset_neg _ /. 
 Arguments dset_bot /. 
 Arguments dset_top /. 
 
 (** lattices laws follow from the fact that we have a sublattice of plain tests *)
 #[export] Instance dset_lattice_laws: lattice.laws (BL+STR+CNV+DIV) dset_lattice_ops.
 Proof. apply (laws_of_injective_morphism dset_bod); trivial. now split. Qed.
 
 Program Definition srel_inj (x: dset): srel A A := {|rel_of i j := Eq A i j /\ dset_bod x i|}.
 Next Obligation. now rewrite H,H0. Qed.

End tests.

(** packing everything as a Kleene category with tests *)
Canonical Structure srel_kat_ops := 
  kat.mk_ops srel_monoid_ops dset_lattice_ops srel_inj.

(** like for monoid laws, we have to reprove everything since we don't have a sub-KAT of that of plain relations *)
#[export] Instance srel_kat_laws: kat.laws srel_kat_ops.
Proof.
  constructor. apply lower_laws.
  intro. simpl. apply lower_lattice_laws. 
  assert (inj_leq: forall n, Proper (leq ==> leq) (@srel_inj n)).
   intros n e f H i j [E H']. split. assumption. revert H'. apply mm_bool_Prop, H.
  constructor; try discriminate. 
  apply inj_leq.
  apply op_leq_weq_1.
  intros _ x y i j. split. 
   intros [E H']. setoid_rewrite Bool.orb_true_iff in H'. 
    destruct H'; [left|right]; split; assumption.  
   intros [[E H']|[E H']]; split; trivial; setoid_rewrite Bool.orb_true_iff; now auto.
  intros _ i j. compute. intuition discriminate. 
  intros ? i j. compute. tauto. 
  intros ? p q i j. split. 
   intros [E H']. setoid_rewrite Bool.andb_true_iff in H'. exists i; split; try tauto. reflexivity. 
   intros [k [ik Hi] [kj Hk]]. subst. split; trivial.
   now transitivity k.
   setoid_rewrite Bool.andb_true_iff; split; trivial.
   now rewrite ik. 
Qed.

Ltac fold_srel := ra_fold srel_monoid_ops.
Tactic Notation "fold_srel" "in" hyp_list(H) := ra_fold srel_monoid_ops in H.
Tactic Notation "fold_srel" "in" "*" := ra_fold srel_monoid_ops in *.
