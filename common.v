(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * common: basic modules, utilities, and tactics *)

Require Export Setoid Morphisms. 
Require Import BinNums.
Set Implicit Arguments.

Bind Scope nat_scope with nat.

(** this lemma is useful when applied in hypotheses 
   ([apply apply in H] makes it possible to specialize an hypothesis [H] 
   by generating the corresponding subgoals) *)
Definition apply X x Y (f: X -> Y) := f x.

(** for debugging *)
Ltac print_goal := match goal with |- ?x => idtac x end.

(** closing tactic *)
Ltac Now tac := tac; solve [auto].


(** coercion from Booleans to propositions *)
Coercion is_true: bool >-> Sortclass.
Hint Unfold is_true.

(** lazy Boolean connectives *)
Notation "a <<< b" := (if (a:bool) then (b:bool) else true) (at level 49).
Notation "a &&& b" := (if (a:bool) then (b:bool) else false) (right associativity, at level 59).
Notation "a ||| b" := (if (a:bool) then true else (b:bool)) (right associativity, at level 60).

(** specification in Prop of the above operations *)
Lemma le_bool_spec a b: is_true (a<<<b) <-> (a -> b).
Proof. case a; intuition. discriminate.  Qed.
Lemma landb_spec a b: is_true (a&&&b) <-> a /\ b.
Proof. case a; intuition. discriminate. Qed.
Lemma lorb_spec a b: is_true (a|||b) <-> a \/ b.
Proof. case a; intuition. discriminate. Qed.
Lemma negb_spec a: is_true (negb a) <-> a = false.
Proof. case a; intuition. Qed.

Lemma eq_bool_iff (a b: bool): (a<->b) <-> a=b.
Proof. 
  split. unfold is_true. 2: now intros <-. 
  case a; case b; intuition discriminate.
Qed.

(** Booleans inclusion *)
Definition le_bool a b := is_true (a <<< b). 
Hint Unfold le_bool.


(** coercion from sums to Booleans  *)
Fixpoint bool_of_sumbool A B (c: sumbool A B): bool := if c then true else false.
Coercion bool_of_sumbool: sumbool >-> bool.

Lemma sumbool_true A (c: sumbool A (~A)): A -> c.
Proof. intro HA. case c; intro F. reflexivity. elim (F HA). Qed.

Lemma is_true_sumbool A (c: {A}+{~A}): is_true c <-> A.
Proof. case c; simpl; intuition; discriminate. Qed.

Lemma sumbool_iff A B: (A<->B) -> {A}+{~A} -> {B}+{~B}.
Proof. tauto. Qed.


(** simplifictation hints *)
Arguments Basics.flip {_ _ _} _ _ _/.
Arguments Basics.impl _ _ /.
Arguments Proper {_} _ _ /.
Arguments respectful {_ _} _ _ / _ _.
Arguments pointwise_relation _ {_} _ / _ _.
Arguments Transitive {_} _ /.
Arguments Symmetric {_} _ /.
Arguments Reflexive {_} _ /.
Notation flip := Basics.flip.
Notation impl := Basics.impl.
Notation pwr := (pointwise_relation _).


(** opaque identity, used to document impossible cases *)
Definition assert_false {A} (x: A): A. Proof. assumption. Qed.


(** 2^n (defined through the [double] function to ease definition of finite sets as ordinals) *)
Fixpoint double n := match n with 0 => 0 | S n => S (S (double n)) end.
Fixpoint pow2 n := match n with 0 => 1 | S n => double (pow2 n) end.


(** closing tactics by reflection, without re-computing at Qed-time *)
Ltac close_by_reflection val := (abstract (vm_cast_no_check (eq_refl val))).

(** introduce non propositional variables *)
Ltac intro_vars :=
  match goal with
    | |- ?H -> _ => 
      match type of H with 
        | Prop => let H' := fresh in intro H'; intro_vars; revert H'
        | _ => intro; intro_vars 
      end 
    | |- _ => idtac
  end.

(** revert all propositional variables *)
Ltac revert_prop := 
  match goal with 
    | H:?t |- _ => match type of t with Prop => revert H; revert_prop end 
    | _ => idtac 
  end.
