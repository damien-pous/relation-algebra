(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * positives: basic facts about binary positive numbers *)

Require Export BinNums.
Require Import comparisons.

(** positives as a [cmpType] *)

Fixpoint eqb_pos i j := 
  match i,j with 
    | xH,xH => true
    | xI i,xI j | xO i, xO j => eqb_pos i j
    | _,_ => false
  end.

Lemma eqb_pos_spec: forall i j, reflect (i=j) (eqb_pos i j).
Proof. induction i; intros [j|j|]; simpl; (try case IHi); constructor; congruence. Qed.

Fixpoint pos_compare i j := 
  match i,j with
    | xH, xH => Eq
    | xO i, xO j | xI i, xI j => pos_compare i j
    | xH, _ => Lt
    | _, xH => Gt
    | xO _, _ => Lt 
    | _,_ => Gt
  end.
 
Lemma pos_compare_spec: forall i j, compare_spec (i=j) (pos_compare i j).
Proof. induction i; destruct j; simpl; try case IHi; try constructor; congruence. Qed.

Canonical Structure cmp_pos := mk_cmp _ eqb_pos_spec _ pos_compare_spec.


(** positive maps (for making environments) *)
(** we redefine such trees here rather than importing them from the standard library: 
   since we do not need any proof about them, this avoids us a heavy Require Import *)
Section e.
Variable A: Type.
Inductive sigma := sigma_empty | N(l: sigma)(o: option A)(r: sigma).
Fixpoint sigma_get default m i :=
  match m with 
    | N l o r => 
      match i with
        | xH => match o with None => default | Some a => a end
        | xO i => sigma_get default l i
        | xI i => sigma_get default r i
      end
    | _ => default
  end.
Fixpoint sigma_add i v m :=
    match m with
    | sigma_empty =>
        match i with
        | xH => N sigma_empty (Some v) sigma_empty
        | xO i => N (sigma_add i v sigma_empty) None sigma_empty
        | xI i => N sigma_empty None (sigma_add i v sigma_empty)
        end
    | N l o r =>
        match i with
        | xH => N l (Some v) r
        | xO i => N (sigma_add i v l) o r
        | xI i => N l o (sigma_add i v r)
        end
    end.
End e.

