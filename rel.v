(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * rel: the main model of heterogeneous binary relations *)

Require Bool.
Require Export boolean prop.
Require Import kat.

(** a relation between two sets is just a predicate  *)
Definition rel (n m: Set) := n -> m -> Prop.

(** * Relations as a (bounded, distributive) lattice *)

(** lattice operations and laws are obtained for free, by two
   successive pointwise liftings of the [Prop] lattice *)

Canonical Structure rel_lattice_ops n m := 
  lattice.mk_ops (rel n m) leq weq cup cap neg bot top.

Global Instance rel_lattice_laws n m: 
  lattice.laws (BDL+STR+CNV+DIV) (rel_lattice_ops n m) := pw_laws _. 

(** * Relations as a residuated Kleene allegory *)

(** relational composition *)
Definition rel_dot n m p (x: rel n m) (y: rel m p): rel n p := 
  fun i j => exists2 k, x i k & y k j.

(** converse (or transpose) *)
Definition rel_cnv n m (x: rel n m): rel m n := 
  fun i j => x j i.

(** left / right divisions *)
Definition rel_ldv n m p (x: rel n m) (y: rel n p): rel m p := 
  fun i j => forall k, x k i -> y k j.

Definition rel_rdv n m p (x: rel m n) (y: rel p n): rel p m := 
  fun j i => forall k, x i k -> y j k.

Section i.
  Variable n: Set.
  Variable x: rel n n.
  (** finite iterations of a relation *)
  Fixpoint iter u := match u with O => @eq _ | S u => rel_dot _ _ _ x (iter u) end.
  (** Kleene star (reflexive transitive closure) *)
  Definition rel_str: rel n n := fun i j => exists u, iter u i j.
  (** strict iteration (transitive closure) *)
  Definition rel_itr: rel n n := rel_dot n n n x rel_str.
End i.


(** packing all operations into a monoid; note that the unit on [n] is
   just the equality on [n], i.e., the identity relation on [n] *)

Canonical Structure rel_monoid_ops := 
  monoid.mk_ops Set rel_lattice_ops rel_dot (@eq) rel_itr rel_str rel_cnv rel_ldv rel_rdv.

(** binary relations form a residuated Kleene allegory *)
Instance rel_monoid_laws: monoid.laws (BDL+STR+CNV+DIV) rel_monoid_ops.
Proof.
  assert (dot_leq: forall n m p,
    Proper (leq ==> leq ==> leq) (rel_dot n m p)).
   intros n m p x y H x' y' H' i k [j Hij Hjk]. exists j. apply H, Hij. apply H', Hjk.
  constructor; (try now left); intros. 
   apply rel_lattice_laws.
   intros i j. firstorder. 
   intros i j. firstorder congruence.
   intros i j. firstorder. 
   intros i j. reflexivity. 
   intros x y E i j. apply E.
   intros i j E. exists O. exact E.
   intros i k [j Hij [u Hjk]]. exists (S u). firstorder. 
   assert (E: forall i, (iter n x i: rel n n) * z <== z).
    induction i. simpl. firstorder now subst.
    rewrite <-H0 at 2. transitivity (x*((iter n x i: rel n n)*z)). 
     simpl. firstorder congruence. now apply dot_leq. 
    intros i j [? [? ?] ?]. eapply E. repeat eexists; eauto.
   reflexivity. 
   intros i k [[j Hij Hjk] Hik]. exists j; trivial. split; firstorder.    
   split. intros E i j [k Hik Hkj]. apply E in Hkj. now apply Hkj. 
    intros E i j Hij k Hki. apply E. firstorder. 
   split. intros E i j [k Hik Hkj]. apply E in Hik. now apply Hik. 
    intros E i j Hij k Hki. apply E. firstorder. 
Qed.


(** * Relations as a Kleene algebra with tests *)

(** "decidable" sets or predicates: Boolean functions *)
Definition dset: ob rel_monoid_ops -> lattice.ops := pw_ops bool_lattice_ops.

(** injection of decidable predicates into relations, as sub-identities *)
Definition rel_inj n (x: dset n): rel n n := fun i j => i=j /\ x i.

(** packing relations and decidable sets as a Kleene algebra with tests *)
Canonical Structure rel_kat_ops := 
  kat.mk_ops rel_monoid_ops dset rel_inj.

Instance rel_kat_laws: kat.laws rel_kat_ops.
Proof.
  constructor. apply lower_laws. intro. apply (pw_laws (H:=lower_lattice_laws)).
  assert (inj_leq: forall n, Proper (leq ==> leq) (@rel_inj n)).
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
   intros [E H']. setoid_rewrite Bool.andb_true_iff in H'. exists i; split; tauto. 
   intros [k [ik Hi] [kj Hk]]. subst. split; trivial. setoid_rewrite Bool.andb_true_iff; now split.
Qed.


(** * Functional relations  *)

Definition frel {A B: Set} (f: A -> B): rel A B := fun x y => y = f x. 

Lemma frel_comp {A B C: Set} (f: A -> B) (g: B -> C): frel f * frel g == frel (fun x => g (f x)).
Proof.
  apply antisym. intros x z [y -> ->]. reflexivity. 
  simpl. intros x z ->. eexists; reflexivity. 
Qed.

Instance frel_weq {A B}: Proper (pwr eq ==> weq) (@frel A B).
Proof. unfold frel; split; intros ->; simpl. apply H. apply eq_sym, H. Qed.
