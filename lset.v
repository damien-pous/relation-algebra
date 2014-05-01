(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * lset: finite sets represented as lists *)

(** This module is used quite intensively, as finite sets are
   pervasives (free variables, summations, partial derivatives...):

   We implement finite sets as simple lists, without any additional
   structure: this allows for very simple operations and
   specifications, without the need for keeping well-formedness
   hypotheses around.
   
   When a bit of efficiency is required, we use sorted listed without
   duplicates as a special case (but without ensuring that these lists
   are sorted: we managed to avoid such a need in our proofs).

   We declare these finite sets a sup-semilattice with bottom element,
   allowing us to use the lattice tactics and theorems in a
   transparent way. *)

Require Import lattice comparisons.
Require Export List. Export ListNotations.

Set Implicit Arguments.

(** * semi-lattice of finite sets as simple lists *)

(** two lists are equal when they contain the same elements,
   independently of their position or multiplicity *)

Canonical Structure lset_ops A := lattice.mk_ops (list A)
  (fun h k => forall a, In a h -> In a k)
  (fun h k => forall a, In a h <-> In a k)
  (@app A) (@app A) (assert_false id) (@nil A) (@nil A).

(** the fact that this makes a semi-lattice is almost trivial *)
Instance lset_laws A: lattice.laws BSL (lset_ops A).
Proof. 
  constructor; simpl; try discriminate.
   firstorder. 
   firstorder. 
   setoid_rewrite in_app_iff. firstorder. 
   firstorder. 
Qed.

(** the [map] function on lists is actually a monotone function over the
   represented sets *)
Instance map_leq A B (f: A -> B): Proper (leq ==> leq) (map f).
Proof.
  intro h. induction h as [|a h IH]; intros k H. apply leq_bx. 
  intros i [<-|I]. apply in_map. apply H. now left. 
  apply IH. 2: assumption. intros ? ?. apply H. now right. 
Qed.
Instance map_weq A B (f: A -> B): Proper (weq ==> weq) (map f) := op_leq_weq_1.

(** [map] is extensional *)
Instance map_compat A B: Proper (pwr eq ==> eq ==> eq) (@map A B).
Proof. intros f g H h k <-. apply map_ext, H. Qed.

(** belonging to a singleton *)
Lemma in_singleton A (x y: A): In x [y] <-> y=x.
Proof. simpl. tauto. Qed.

(** the following tactic replaces all occurrences of [cons] with
   degenerated concatenations, so that the [lattice] can subsequently
   handle them *)

Ltac fold_cons := 
  repeat match goal with 
    | |- context[@cons ?A ?x ?q] => (constr_eq q (@nil A); fail 1) || change (x::q) with ([x]++q)
    | H: context[!cons ?A ?x ?q] |- _ => (constr_eq q (@nil A); fail 1) || change (x::q) with ([x]++q) in H
  end.



(** * sorted lists without duplicates *)

(** when the elements come with a [cmpType] structure, one can perform
   sorted lists operations *)

Section m.
 Context {A: cmpType}.

 (** sorted merge of sorted lists *)
 Fixpoint union (l1: list A) :=
   match l1 with
     | nil => fun l2 => l2
     | h1::t1 =>
       let fix union' l2 :=
         match l2 with
           | nil => l1
           | h2::t2 =>
             match cmp h1 h2 with
               | Eq => h1::union t1 t2
               | Lt => h1::union t1 l2
               | Gt => h2::union' t2
             end
         end
         in union'
   end.

 (** sorted insertion in a sorted list *)
 Fixpoint insert (i: A) l := 
   match l with
     | nil => i::nil
     | j::q => 
       match cmp i j with
         | Eq => l
         | Lt => i::l
         | Gt => j::insert i q
       end
   end.

 (** weak specification: [union] actually performs an union *)
 Lemma union_app: forall h k, union h k == h ++ k. 
 Proof.
   induction h as [|x h IHh]; simpl union. reflexivity. 
   induction k as [|y k IHk]. lattice. case cmp_spec. 
   intros ->. fold_cons. rewrite IHh. lattice.
   intros _. fold_cons. rewrite IHh. lattice.
   intros _. fold_cons. rewrite IHk. lattice.
 Qed.

 (** and [insert] actually performs an insertion *)
 Lemma insert_union: forall i l, insert i l = union [i] l. 
 Proof.
   induction l; simpl. reflexivity. 
   case cmp_spec. congruence. reflexivity. now rewrite IHl. 
 Qed.

 Lemma insert_app: forall i l, insert i l == [i] ++ l. 
 Proof. intros. rewrite insert_union. apply union_app. Qed.

End m.

Module Fix.

Canonical Structure lset_ops A := lattice.mk_ops (list A)
  (fun h k => forall a, In a h -> In a k)
  (fun h k => forall a, In a h <-> In a k)
  (@app A) (@app A) (assert_false id) (@nil A) (@nil A).

End Fix.
