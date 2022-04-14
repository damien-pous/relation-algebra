(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * powerfix: bounded fixpoint operator *)

(** we define a fixpoint operator which recursively unfolds an
   open-recursive function with recursive depth at most [2^n], for
   arbitrary [n].  This allows us to define arbitrary recursive
   functions, without needing to prove their termination. The operator
   is defined in a computationally efficient way. (We already used
   such a trick in ATBR ; it's simplified here thanks to the
   introduction of eta in Coq v8.4 *)

Require Import common.
Set Implicit Arguments.

Section powerfix.

Variables A B: Type.
Notation Fun := (A -> B).

(** the three following functions "iterate" their [f] argument lazily: 
   iteration stops whenever [f] no longer makes recursive calls.
   - [powerfix' n f k] iterates [f] at most [(2^n-1)] times and then yields to [k] 
   - [powerfix n f k] iterates [f] at most [(2^n)] times and then yields to [k] 
   - [linearfix n f k] iterates [f] at most [n] times and then yields to [k] 
   *)
Fixpoint powerfix' n (f: Fun -> Fun) (k: Fun): Fun := 
  fun a => match n with O => k a | S n => f (powerfix' n f (powerfix' n f k)) a end.
Definition powerfix n f k a := f (powerfix' n f k) a.

Fixpoint linearfix n (f: Fun -> Fun) (k: Fun): Fun :=
  fun a => match n with O => k a | S n => f (linearfix n f k) a end.

(** simple lemmas about [2^n]  *)
Lemma pow2_S n: pow2 n = S (pred (pow2 n)).
Proof. induction n. reflexivity. simpl. now rewrite IHn. Qed.

Lemma pred_pow2_Sn n: pred (pow2 (S n)) = S (double (pred (pow2 n))).
Proof. simpl. now rewrite pow2_S. Qed.

(** characterisation of [powerfix] with [linearfix] *)
Section linear_carac.

 Variable f: Fun -> Fun.

 Lemma linearfix_S: forall n k, 
   f (linearfix n f k) = linearfix n f (f k).
 Proof. induction n; intros k; simpl. reflexivity. now rewrite IHn. Qed.

 Lemma linearfix_double: forall n k, 
   linearfix n f (linearfix n f k) = linearfix (double n) f k.
 Proof. 
   induction n; intros k. reflexivity. simpl linearfix.
   now rewrite <-IHn, <-linearfix_S. 
 Qed.

 Lemma powerfix'_linearfix: forall n k, 
   powerfix' n f k = linearfix (pred (pow2 n)) f k.
 Proof.
   induction n; intros. reflexivity.
   rewrite pred_pow2_Sn. simpl. 
   now rewrite <-linearfix_double, 2IHn.
 Qed.

 Theorem powerfix_linearfix: forall n k, 
   powerfix n f k = linearfix (pow2 n) f k.
 Proof. intros. unfold powerfix. now rewrite powerfix'_linearfix, pow2_S. Qed.

End linear_carac.

(** [powerfix_invariant] gives an induction principle for [powerfix],
   that does not care about the number of iterations -- in particular,
   the trivial "emptyfix" function : ([fun f k a => k a]) satisfies
   the same induction principle, so that this can only be used to
   reason about partial correctness. *)
Section invariant.
 Variable P: Fun -> Prop.

 Lemma powerfix_invariant: forall n f g, 
   (forall k, P k -> P (f k)) -> P g -> P (powerfix n f g).
 Proof. 
   intros n f g Hf Hg. apply Hf. 
   revert g Hg. induction n; intros g Hg; simpl; auto. 
 Qed.

End invariant.

End powerfix.
