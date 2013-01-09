(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * glang: the KAT model of guarded string languages *)

(** The model of guarded string languages is the model of traces, when
   states are the atoms of a Boolean lattice, we prove here that this
   it is a model of Kleene algebra with tests (KAT), where the Boolean
   subalgebra is just the free one: the set of Boolean expressions. 

   Like for traces, we provide both untyped and typed models. *)

Require Export traces.
Require Import kat lsyntax ordinal comparisons boolean.
Set Implicit Arguments.

Section s.

(** * Untyped model *)

(** We consider the free Boolean lattice over a set of [pred]
   predicates, whose atoms are just functions [a: ord pred -> bool]
   assigning a truth value to each variable. *)

Variable pred: nat.
Notation Sigma := positive.

(** to avoid extensionality problems, we call "atom" an element of
   [ord (pow2 pred)], relying on the bijection between [ord pred ->
   bool] and that set when needed *)

Notation Atom := (ord (pow2 pred)).

(** Boolean expressions over [pred] variables are injected into
   traces as follows: take all traces reduced to a single atom
   (i.e., state) such that the Boolean expression evaluates to [true]
   under the corresponding assignation of variables *)
Definition glang_inj (n: traces_unit) (x: expr_ops (ord pred) BL):
  traces Atom :=
  fun w => 
    match w with 
      | tnil a => is_true (eval (set.mem a) x)
      | _ => False
    end.

(** packing this injection together with the Kleene algebra of traces
   and the Boolean algebra of expressions *)
Canonical Structure glang_kat_ops := kat.mk_ops _ _ glang_inj.

(** This model satisfies KAT laws *)
Global Instance glang_kat_laws: kat.laws glang_kat_ops. 
Proof.
  constructor. apply lower_laws. intro. apply expr_laws.
  assert (inj_leq: forall n, Proper (leq ==> leq) (@glang_inj n)).
  intros n e f H [a|]. 2: reflexivity. 
   apply (fn_leq _ _ (H _ lower_lattice_laws _)). 
  constructor; try discriminate. 
  apply inj_leq. 
  apply op_leq_weq_1. 
  intros _ x y [a|]. 2: compute; tauto. simpl.
   setoid_rewrite Bool.orb_true_iff. reflexivity.
  intros _ [a|]. 2: reflexivity. simpl. intuition discriminate. 
  intros ? [a|]. 2: reflexivity. simpl. now intuition. 
  intros ? x y [a|]. simpl. setoid_rewrite Bool.andb_true_iff. split. 
   intros (Hx&Hy). repeat exists (tnil a); try split; trivial. constructor. 
   intros [[b|] Hu [[c|] Hv H]]; try elim Hu; try elim Hv.
   inversion H. intuition congruence. 
   intros. simpl. split. intros [].  
   intros [[b|] Hu [[c|] Hv H]]; try elim Hu; try elim Hv. inversion H.
Qed.


(** * Typed model *)

(** the typed model is obtained in a straighforward way from the typed
   traces model: Boolean expressions can be injected as in the untyped
   case since there are no typing constraints on the generated traces
   (they are reduced to a single state).  *)

Variables src tgt: Sigma -> positive.

Program Definition tglang_inj n (x: expr_ops (ord pred) BL): ttraces Atom src tgt n n :=
  glang_inj traces_tt x.
Next Obligation. intros [a|???] []. constructor. Qed.

Canonical Structure tglang_kat_ops := kat.mk_ops _ _ tglang_inj.

(* TODO: comment factoriser les deux preuves? *)
Global Instance tglang_kat_laws: kat.laws tglang_kat_ops. 
Proof.
  constructor. apply lower_laws. intro. apply expr_laws.
  assert (inj_leq: forall n, Proper (leq ==> leq) (@tglang_inj n)).
  intros n e f H [a|]. 2: reflexivity. 
   apply (fn_leq _ _ (H _ lower_lattice_laws _)). 
  constructor; try discriminate. 
  apply inj_leq. 
  apply op_leq_weq_1.
  intros _ x y [a|]. 2: compute; tauto. simpl.
   setoid_rewrite Bool.orb_true_iff. tauto.
  intros _ [a|]. 2: reflexivity. simpl. intuition discriminate. 
  intros ? [a|]. 2: reflexivity. simpl. now intuition. 
  intros ? x y [a|]. simpl. setoid_rewrite Bool.andb_true_iff. split. 
   intros (Hx&Hy). repeat exists (tnil a); try split; trivial. constructor. 
   intros [[b|] Hu [[c|] Hv H]]; try elim Hu; try elim Hv.
   inversion H. intuition congruence. 
   intros. simpl. split. intros [].  
   intros [[b|] Hu [[c|] Hv H]]; try elim Hu; try elim Hv. inversion H.
Qed.

End s.
