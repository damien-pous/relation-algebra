(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * comparisons: types equiped with a comparison function *)

Require Import List.
Require Import Eqdep Eqdep_dec. 
Import ListNotations.
Set Implicit Arguments.

(** * Specifying Boolean *)

Inductive reflect (P: Prop): bool -> Set :=
| reflect_t : P -> reflect P true
| reflect_f : ~ P -> reflect P false.


(** * Specifying ternary comparisons *)
(** note that [Lt] and [Gt] have the same meaning, i.e., not [Eq] *)

Inductive compare_spec (P: Prop): comparison -> Set :=
| compare_eq: P -> compare_spec P Eq
| compare_lt: ~P -> compare_spec P Lt
| compare_gt: ~P -> compare_spec P Gt.

(** turning a comparison function into a Boolean test  *)
Definition eqb_of_compare A (f: A -> A -> comparison): A -> A -> bool := 
  fun x y => match f x y with Eq => true | _ => false end.

Lemma eqb_of_compare_spec A f: 
  (forall a b: A, compare_spec (a=b) (f a b)) -> 
  forall a b, reflect (a=b) (eqb_of_compare f a b).
Proof. unfold eqb_of_compare. intros H a b. now case H; constructor. Qed.

(** lexicographic ternary comparison *)
Notation lex a b := match a with Eq => b | Lt => Lt | Gt => Gt end.

Lemma lex_spec P Q R a b (H: R<->P/\Q):
  compare_spec P a -> compare_spec Q b -> compare_spec R (lex a b).
Proof.
  destruct 1; try (constructor; tauto). 
  destruct 1; constructor; tauto. 
Qed.

Lemma compare_lex_eq a b: lex a b = Eq <-> a = Eq /\ b = Eq.
Proof. destruct a; intuition discriminate. Qed. 


(** * Structure for types equiped with a Boolean equality and a comparison function.
   Note that the specification of [cmp] is weak: we only have
   [cmp a b = Eq <-> a=b]. As a consequence, the difference betwen
   [Lt] and [Gt] can only be used as a heuristic. *)
Structure cmpType := mk_cmp {
  carr:> Set;
  eqb: carr -> carr -> bool;
  _: forall x y, reflect (x=y) (eqb x y);
  cmp: carr -> carr -> comparison;
  _: forall x y, compare_spec (x=y) (cmp x y)
}.
Arguments cmp {c} x y. 
Arguments eqb {c} x y. 

Lemma eqb_spec (A: cmpType): forall x y: A, reflect (x=y) (eqb x y). 
Proof. now case A. Qed.
Lemma cmp_spec (A: cmpType): forall x y: A, compare_spec (x=y) (cmp x y). 
Proof. now case A. Qed.

(** building comparison types without providing an equality function *)
Definition mk_simple_cmp A cmp cmp_spec := 
  @mk_cmp A _ (eqb_of_compare_spec _ cmp_spec) cmp cmp_spec.

(** phantom identity to generate cmpTypes by unification (see ssreflect) *)
Definition cmp_id (A: cmpType) (X: Set) (_:X -> carr A): cmpType := A.
Notation "[ X  :cmp]" := (@cmp_id _ X%type (fun x => x)) (at level 0).

(** basic properties   *)
Lemma cmp_eq (A: cmpType) (x y: A): cmp x y = Eq -> x=y.
Proof. case cmp_spec; congruence. Qed.

Lemma cmp_refl (A: cmpType) (x: A): cmp x x = Eq.
Proof. case cmp_spec; congruence. Qed.

Lemma eqb_eq (A: cmpType) (x y: A): eqb x y = true -> x = y.
Proof. case eqb_spec; congruence. Qed.

Lemma eqb_refl (A: cmpType) (x: A): eqb x x = true.
Proof. case eqb_spec; congruence. Qed.

Lemma eqb_sym (A: cmpType) (x y: A): eqb x y = eqb y x.
Proof. case eqb_spec; case eqb_spec; congruence. Qed.

Lemma cmp_dec (A: cmpType) (x y: A): {x=y}+{x<>y}.
Proof. case (eqb_spec A x y); tauto. Qed.

(** equality on cmpTypes being decidable, we get uniqueness of identity 
    proofs and elimination of dependent equality *)
Lemma cmp_eq_dep_eq (A: cmpType) (P: A -> Type): 
  forall p (x y: P p), eq_dep A P p x p y -> x = y.
Proof. apply eq_dep_eq_dec, cmp_dec. Qed.

Lemma cmp_eq_rect_eq (A: cmpType): 
  forall (p: A) Q (x: Q p) (h: p = p), eq_rect p Q x p h = x.
Proof. symmetry. apply eq_rect_eq_dec, cmp_dec. Qed.

Lemma UIP_cmp (A: cmpType) (p q: A) (x y: p=q): x = y.
Proof. apply UIP_dec, cmp_dec. Qed.


(** * Natural numbers as a [cmpType] *)
Fixpoint eqb_nat i j := 
  match i,j with 
    | O,O => true
    | S i,S j=> eqb_nat i j
    | _,_ => false
  end.
Lemma eqb_nat_spec: forall i j, reflect (i=j) (eqb_nat i j).
Proof.
  induction i; intros [|j]; try (constructor; congruence). 
  simpl. case IHi; constructor; congruence.
Qed.
Fixpoint nat_compare i j := 
  match i,j with 
    | O,O => Eq
    | S i,S j=> nat_compare i j
    | O,_ => Lt 
    | _,O => Gt
  end.
Lemma nat_compare_spec: forall i j, compare_spec (i=j) (nat_compare i j).
Proof.
  induction i; intros [|j]; try (constructor; congruence). 
  simpl. case IHi; constructor; congruence.
Qed.
Canonical Structure cmp_nat := mk_cmp _ eqb_nat_spec _ nat_compare_spec.


(** * Booleans as a [cmpType] *)
Fixpoint eqb_bool i j := 
  match i,j with 
    | false,false | true,true => true
    | _,_ => false
  end.
Lemma eqb_bool_spec: forall i j, reflect (i=j) (eqb_bool i j).
Proof. destruct i; destruct j; constructor; congruence. Qed.
Fixpoint bool_compare i j := 
  match i,j with 
    | false,false | true,true => Eq
    | false,true => Lt
    | true,false => Gt
  end.
Lemma bool_compare_spec: forall i j, compare_spec (i=j) (bool_compare i j).
Proof. destruct i; destruct j; constructor; congruence. Qed.
Canonical Structure cmp_bool := mk_cmp _ eqb_bool_spec _ bool_compare_spec.


(** * Pairs of [cmpType]s *)
Section p.
  Variables A B: cmpType.
  Definition eqb_pair (x y: A*B) :=
    let '(x1,x2) := x in
    let '(y1,y2) := y in
      if (eqb x1 y1) then (eqb x2 y2) else false.
  Lemma eqb_pair_spec: forall x y, reflect (x=y) (eqb_pair x y).
  Proof. 
    unfold eqb_pair. intros [? ?] [? ?]; simpl;
    repeat case eqb_spec; constructor; congruence. 
  Qed.
  Definition pair_compare (x y: A*B) :=
    let '(x1,x2) := x in
    let '(y1,y2) := y in
      lex (cmp x1 y1) (cmp x2 y2).
  Lemma pair_compare_spec: forall x y, compare_spec (x=y) (pair_compare x y).
  Proof. 
    unfold pair_compare. intros [? ?] [? ?]; simpl;
    repeat case cmp_spec; constructor; congruence. 
  Qed.
  Canonical Structure cmp_pair := mk_cmp _ eqb_pair_spec _ pair_compare_spec.  
End p.


(** * Sums of [cmpType]s *)
Section s.
  Variables A B: cmpType.
  Definition eqb_sum (x y: A+B) := 
    match x,y with
      | inl x,inl y | inr x,inr y => eqb x y
      | _,_ => false
    end.
  Lemma eqb_sum_spec: forall x y, reflect (x=y) (eqb_sum x y).
  Proof. 
    unfold eqb_sum. intros [?|?] [?|?]; simpl; 
     try case eqb_spec; constructor; congruence. 
  Qed.
  Definition sum_compare (x y: A+B) :=
    match x,y with
      | inl x,inl y | inr x,inr y => cmp x y
      | inl _,inr _ => Lt
      | inr _,inl _ => Gt
    end.
  Lemma sum_compare_spec: forall x y, compare_spec (x=y) (sum_compare x y).
  Proof. 
    unfold sum_compare. intros [?|?] [?|?]; simpl; 
     try case cmp_spec; constructor; congruence. 
  Qed.
  Canonical Structure cmp_sum := mk_cmp _ eqb_sum_spec _ sum_compare_spec.
End s.


(** * Lists of a [cmpType] *)
Section l.
  Variables A: cmpType.
  Fixpoint eqb_list (h k: list A) := 
    match h,k with
      | nil, nil => true
      | u::h, v::k => if eqb u v then eqb_list h k else false
      | _, _ => false
    end.
  Fixpoint list_compare (h k: list A) := 
    match h,k with
      | nil, nil => Eq
      | nil, _   => Lt
      | _,   nil => Gt
      | u::h, v::k => lex (cmp u v) (list_compare h k)
    end.
  Lemma eqb_list_spec: forall h k, reflect (h=k) (eqb_list h k). 
  Proof.
    induction h as [|x h IH]; destruct k; simpl;
      try case eqb_spec; try case IH; constructor; congruence.
  Qed.
  Lemma list_compare_spec: forall h k, compare_spec (h=k) (list_compare h k). 
  Proof.
    induction h as [|x h IH]; destruct k; simpl;
      try case cmp_spec; try case IH; constructor; congruence.
  Qed.
  Canonical Structure cmp_list := mk_cmp _ eqb_list_spec _ list_compare_spec.
End l.

