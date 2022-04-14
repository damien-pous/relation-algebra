(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * lsyntax: syntactic model for flat structures (lattice operations) *)

Require Export positives.
Require Import comparisons lattice lset sups.
Set Implicit Arguments.

(** * Free syntactic model *)

Section s.
Variable A: Set.
(* [A = ord n] in KAT proofs
   [A = positive] in reification, (and possibly in computations in the future) *)

(** Boolean lattice expressions over a set [A] of variables *)
Inductive expr := 
| e_bot
| e_top
| e_cup (e f: expr)
| e_cap (e f: expr)
| e_neg (e: expr)
| e_var (a: A).

(** level of an expression: the set of operations that appear in that expression *)
Fixpoint e_level e :=
  match e with
    | e_bot => BOT
    | e_top => TOP
    | e_cup x y => CUP + e_level x + e_level y
    | e_cap x y => CAP + e_level x + e_level y
    | e_neg x => BL + e_level x 
      (* negation is ill-defined without the other Boolean operations, 
         whence the [BL] rather than [NEG] *)
    | e_var _ => MIN
  end%level.

Section e.
Context {X: ops}.
Variable f: A -> X.

(** interpretation of an expression into an arbitray Boolean lattice
   structure, given an assignation [f] of the variables *)
Fixpoint eval e: X :=
  match e with
    | e_bot => bot
    | e_top => top
    | e_cup x y => eval x ⊔ eval y
    | e_cap x y => eval x ⊓ eval y
    | e_neg x => ! eval x
    | e_var a => f a
  end.
End e.


Section l.
Variable l: level.

(** * (In)equality of syntactic expressions.

   Rather than defining (in)equality of syntactic expressions as
   inductive predicates, we exploit the standard impredicative
   encoding of such predicates: two expressions are equal (resp.,
   lower or equal) iff they are equal (resp., lower or equal) under
   any interpretation. 

   These definitions are parametrised by the level [l] at which one
   wants to interpret the expressions: this allows us to capture once
   and for all the equational theories of each flat structure. *)

Definition e_leq (x y: expr) := forall X (L: laws l X) (f: A -> X), eval f x ≦ eval f y.
Definition e_weq (x y: expr) := forall X (L: laws l X) (f: A -> X), eval f x ≡ eval f y.

(** by packing syntactic expressions and the above predicates into a
   canonical structure, we get all notations for free *)
Canonical Structure expr_ops := {|
  car := expr;
  leq := e_leq;
  weq := e_weq;
  cup := e_cup;
  cap := e_cap;
  neg := e_neg;
  bot := e_bot;
  top := e_top
|}.

(** we easily show that we get a model so that we immediately benefit
   from all lemmas about flat structures *)

Global Instance expr_laws: laws l expr_ops.
Proof.
  constructor; try right. constructor.
   intros x X L f. reflexivity.
   intros x y z H H' X L f. transitivity (eval f y); auto.
   intros x y. split. 
    intro H. split; intros X L f. now apply weq_leq, H. now apply weq_geq, H.
    intros [H H'] X L f. apply antisym; auto.
   intros Hl x y z. split. 
    intro H. split; intros X L f; specialize (H X L f); simpl in H; hlattice. 
    intros [H H'] X L f. simpl. apply cup_spec; auto.
   intros Hl x y z. split. 
    intro H. split; intros X L f; specialize (H X L f); simpl in H; hlattice. 
    intros [H H'] X L f. simpl. apply cap_spec; auto.
   intros x X L f. apply leq_bx.
   intros x X L f. apply leq_xt.
   intros Hl x y z X L f. apply cupcap_.
   intros Hl x X L f. apply capneg.
   intros Hl x X L f. apply cupneg.
Qed.


(** the interpretation function is an homomorphism, so that it
   preserves all finite sups and infs *)
Lemma eval_sup I (J: list I) (f: I -> expr) (X: lattice.ops) (g: A -> X): 
  eval g (sup (X:=expr_ops) f J) = \sup_(i\in J) eval g (f i).
Proof. apply f_sup_eq; now f_equal. Qed.

Lemma eval_inf I (J: list I) (f: I -> expr) (X: lattice.ops) (g: A -> X): 
  eval g (sup (X:=dual expr_ops) f J) = \inf_(i\in J) eval g (f i).
Proof. apply (f_sup_eq (Y:=dual X)); now f_equal. Qed.

(** [e_var] is a unit for the underlying monad *)
Lemma eval_var (e: expr_ops): eval e_var e = e.
Proof. induction e; simpl; congruence. Qed.

End l.

End s.
Arguments e_var [A] a.
Arguments e_bot {A}.
Arguments e_top {A}.

Declare Scope last_scope.
Bind Scope last_scope with expr.
Delimit Scope last_scope with last.

(** additional notations, to specify explicitly at which level
   expressions are considered, or to work directly with the
   bare constructors (by opposition with the encapsulated ones, 
   through lattice.ops)*)
Notation expr_ l := (car (expr_ops _ l)).
Notation "x <==_[ l ] y" := (@leq (expr_ops _ l) x%last y%last) (at level 79): ra_scope.
Notation "x ==_[ l ] y" := (@weq (expr_ops _ l) x%last y%last) (at level 79): ra_scope.

Infix "⊔" := e_cup: last_scope.
Infix "⊓" := e_cap: last_scope.
Notation "! x"  := (e_neg x): last_scope.


(** * Comparing expressions *)

(** we get a [cmpType] on expressions if the set of variable is such
   (currently used in ugregex_dec) *)

Section expr_cmp.
Context {A: cmpType}.
Fixpoint expr_compare (x y: expr A) :=
  match x,y with
    | e_bot, e_bot 
    | e_top, e_top => Eq
    | e_var a, e_var b => cmp a b
    | e_cup x x', e_cup y y' 
    | e_cap x x', e_cap y y' => lex (expr_compare x y) (expr_compare x' y')
    | e_neg x, e_neg y => expr_compare x y
    | e_bot, _      => Lt
    | _, e_bot      => Gt
    | e_top, _      => Lt
    | _, e_top      => Gt
    | e_var _, _    => Lt
    | _, e_var _    => Gt
    | e_cup _ _, _  => Lt
    | _, e_cup _ _  => Gt
    | e_cap _ _, _  => Lt
    | _, e_cap _ _  => Gt
  end.

Lemma expr_compare_spec: forall x y, compare_spec (x=y) (expr_compare x y).
Proof.
  induction x; destruct y; try (constructor; congruence).
  - eapply lex_spec; eauto. intuition congruence.
  - eapply lex_spec; eauto. intuition congruence.
  - simpl; case IHx; constructor; congruence. 
  - simpl; case cmp_spec; constructor; congruence. 
Qed.

Canonical Structure cmp_expr := mk_simple_cmp _ expr_compare_spec.

(** variables appearing in an expression ([A] needs to be a [cmpType]
   so that the resulting list is without duplicates) *)
Fixpoint vars (e: expr A): list A :=
  match e with
    | e_bot 
    | e_top => []
    | e_cup x y 
    | e_cap x y => union (vars x) (vars y)
    | e_neg x => vars x
    | e_var x => [x]
  end.
End expr_cmp.
