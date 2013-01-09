(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * denum: retracting various countable types into positives *)

Require Import common positives ordinal.
Set Implicit Arguments.

(** * Sums *)

Definition mk_sum (x: positive+positive) :=
  match x with
    | inl p => xO p
    | inr p => xI p
  end.
Definition get_sum x := 
  match x with
    | xO p => inl p
    | xI p => inr p
    | _ => assert_false (inl xH)
  end.
Lemma get_mk_sum x: get_sum (mk_sum x) = x.  
Proof. now destruct x. Qed.

(** * Pairs *)

Fixpoint xpair y x :=
  match x with 
    | xH => xI (xO y)
    | xO x => xO (xO (xpair y x))
    | xI x => xI (xI (xpair y x))
  end.
Definition mk_pair (x: positive*positive) := xpair (snd x) (fst x).
Fixpoint get_pair x := 
  match x with 
    | xI (xO p) => (xH,p)
    | xO (xO x) => let '(x,y) := get_pair x in (xO x,y)
    | xI (xI x) => let '(x,y) := get_pair x in (xI x,y)
    | _ => assert_false (xH,xH)
  end.
Lemma get_mk_pair x: get_pair (mk_pair x) = x.  
Proof. 
  destruct x as [x y]. unfold mk_pair. simpl. 
  induction x; simpl; now rewrite ?IHx. 
Qed.

(** * Natural numbers *)

(** we use a much simpler function than the standard bijection, 
   since we only need a retract *)
Definition mk_nat := nat_rec (fun _=>positive) xH (fun _ => xO).
Fixpoint get_nat x := 
  match x with 
    | xH => O
    | xO x => S (get_nat x) 
    | _ => assert_false O 
  end.
Lemma get_mk_nat x: get_nat (mk_nat x) = x.  
Proof. induction x; simpl; now rewrite ?IHx. Qed.

(** * Ordinals *)

Definition mk_ord n (x: ord n) := mk_nat x.
(** get_ord returns an option since [n] could be 0, 
   this is not problematic in practice *)
Definition get_ord n (x: positive): option (ord n).
 set (y:=get_nat x). case (lt_ge_dec y n).
 intro Hy. exact (Some (Ord y Hy)).
 intros _. exact None.
Defined.
Lemma get_mk_ord n x: get_ord n (mk_ord x) = Some x.  
Proof. 
  unfold mk_ord, get_ord. destruct x as [i Hi]; simpl. 
  rewrite get_mk_nat. case lt_ge_dec.
  intro. f_equal. now apply eq_ord. 
  rewrite Hi at 1. discriminate.
Qed.
