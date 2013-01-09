(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * bmx: Boolean matrices, characterisation of reflexive transitive closure *)

Require Import kleene boolean sups matrix.
Set Implicit Arguments.

Notation bmx := (mx_ops bool_ops bool_tt).

(** intermediate alternative definition of the star of a Boolean matrix *)

Fixpoint bmx_str n: bmx n n -> bmx n n :=
  match n with
    | O => fun M => M
    | S n => fun M =>
      let b := sub01_mx (n1:=1) (m1:=1) M in
      let c := sub10_mx (n1:=1) (m1:=1) M in
      let d := bmx_str (sub11_mx (n1:=1) (m1:=1)  M) in
      blk_mx 1 (b*d) (d*c) (d+d*c*(b*d))
  end.

Lemma bmx_top_1: top == (1: bmx 1%nat 1%nat).
Proof. intros i j. now setoid_rewrite ord0_unique. Qed.

Lemma bmx_str_str n (M: bmx n n): M^* == bmx_str M.
Proof.
  induction n as [|n IHn]. intro i. elim (ord_0_empty i).
  change (M^*) with (mx_str _ _ _ M).
  simpl mx_str. simpl bmx_str. unfold mx_str_build.
  ra_fold (mx_ops bool_ops bool_tt). rewrite bmx_top_1.
  now rewrite IHn, dot1x, dotx1. 
Qed.

(** reflexive transitive closure as an inductive predicate *)

Inductive rt_clot n (M: bmx n n): ord n -> ord n -> Prop :=
| clot_nil: forall i, rt_clot M i i
| clot_cons: forall i j k, M i j -> rt_clot M j k -> rt_clot M i k.

Lemma clot_app n (M: bmx n n): forall i j k, rt_clot M i j -> rt_clot M j k -> rt_clot M i k.
Proof. induction 1; eauto using clot_cons. Qed.

Lemma clot_snoc n (M: bmx n n): forall i j k, rt_clot M i j -> M j k -> rt_clot M i k.
Proof. intros. eapply clot_app. eassumption. eapply clot_cons. eassumption. constructor. Qed.

Lemma rt_clot_S_S n (M: bmx (1+n)%nat (1+n)%nat): forall i j,
  rt_clot (sub11_mx M) i j -> rt_clot M (rshift i) (rshift j).
Proof. induction 1. constructor. eapply clot_cons; eassumption. Qed.

(** characterisation theorem  *)

Theorem bmx_str_clot n (M: bmx n n) i j: M^* i j <-> rt_clot M i j. 
Proof.
split.
- rewrite bmx_str_str. revert i j. 
  induction n as [|n IH]; intros i' j'. 
   simpl. intro. eapply clot_cons. eassumption. constructor. 
  unfold bmx_str; fold (@bmx_str n). set (M' := sub11_mx (n1:=1) (m1:=1) M). 
  specialize (IH M'). unfold blk_mx, row_mx, col_mx. 
  case ordinal.split_spec; intros i ->; case ordinal.split_spec; intros j -> Hij.
  + setoid_rewrite ord0_unique. constructor. 
  + setoid_rewrite is_true_sup in Hij. destruct Hij as [k [_ Hk]].
    apply Bool.andb_true_iff in Hk as [Hik Hkj]. 
    apply IH in Hkj. unfold M' in Hkj. 
    eapply clot_cons. eassumption. now apply rt_clot_S_S. 
  + setoid_rewrite is_true_sup in Hij. destruct Hij as [k [_ Hk]].
    apply Bool.andb_true_iff in Hk as [Hik Hkj]. 
    apply IH in Hik. unfold M' in Hik. 
    eapply clot_snoc. apply rt_clot_S_S; eassumption. assumption.
  + setoid_rewrite Bool.orb_true_iff in Hij. destruct Hij as [Hij|Hij].
     apply IH in Hij. now apply rt_clot_S_S.
    setoid_rewrite is_true_sup in Hij. destruct Hij as [k [_ Hk]].
    apply Bool.andb_true_iff in Hk as [Hik Hkj]. 
    setoid_rewrite is_true_sup in Hik. destruct Hik as [i' [_ Hi']].
    apply Bool.andb_true_iff in Hi' as [Hii' Hi'k]. 
    setoid_rewrite is_true_sup in Hkj. destruct Hkj as [j' [_ Hj']].
    apply Bool.andb_true_iff in Hj' as [Hkj' Hj'j]. 
    apply IH in Hii'. apply IH in Hj'j. 
    eapply clot_app. apply rt_clot_S_S, Hii'. 
    eapply clot_cons. apply Hi'k. 
    eapply clot_cons. apply Hkj'. 
    apply rt_clot_S_S, Hj'j. 
- induction 1 as [i|i j k Hij Hjk IH]. 
  + pose proof (str_refl (X:=bmx) M i i). simpl in H. 
    setoid_rewrite le_bool_spec in H. apply H. unfold mx_one. now rewrite eqb_refl. 
  + pose proof (str_cons (X:=bmx) M i k). simpl in H. 
    setoid_rewrite le_bool_spec in H. apply H. clear H. 
    unfold mx_dot. rewrite is_true_sup. eexists. split. apply in_seq.  
    apply Bool.andb_true_iff. split; eassumption. 
Qed.
