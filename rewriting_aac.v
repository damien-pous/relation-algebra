(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * rewriting_aac: bridge with AAC_tactics *)

Require Import monoid.

From AAC_tactics
Require Export AAC.

Section lattice.
Context `{lattice.laws}. 

Global Instance aac_cupA `{CUP ≪ l} : Associative weq cup := cupA.
Global Instance aac_cupC `{CUP ≪ l} : Commutative weq cup := cupC.
Global Instance aac_cupI `{CUP ≪ l} : Idempotent weq cup := cupI.
Global Instance aac_cupU `{BOT+CUP ≪ l} : Unit weq cup bot := Build_Unit _ _ _ cupbx cupxb.

Global Instance aac_capA `{CAP ≪ l} : Associative weq cap := capA.
Global Instance aac_capC `{CAP ≪ l} : Commutative weq cap := capC.
Global Instance aac_capI `{CAP ≪ l} : Idempotent weq cap := capI.
Global Instance aac_capU `{TOP+CAP ≪ l} : Unit weq cap top := Build_Unit _ _ _ captx capxt.

Global Instance aac_lift_leq_weq : AAC_lift leq weq. 
Proof. constructor; eauto with typeclass_instances. Qed.

End lattice.

Section monoid.
Context `{monoid.laws} {n: ob X}.
Global Instance aac_dotA: Associative weq (dot n n n) := (@dotA _ _ _ n n n n).
Global Instance aac_dotU: Unit weq (dot n n n) (one n). 
Proof. constructor; intro. apply dot1x. apply dotx1. Qed.
End monoid.

(*
(* tests *)
Require Import kleene.
Goal forall `{laws} `{BKA ≪ l} n (a b c: X n n), a+b ≡ c -> (forall x: X n n, x⋅x ≡ x) -> 
  a⋅b+b+1⋅a+(b+0)^* ≡ a⋅b⋅c⋅b⋅c⋅a+0.
Proof. 
  intros. aac_normalise. 
  aac_rewrite H1. 
  aac_rewrite H2 in_right. 
Abort.

Require Import rel.
Goal forall (a b c: hrel nat nat), a+b ≡ c -> (forall x: hrel nat nat, x⋅x ≡ x) -> 
  a⋅b+b+1⋅a+(b+0)^* ≡ a⋅b⋅c⋅b⋅c⋅a+0.
Proof.
  intros.
  aac_rewrite H.
  aac_rewrite H0 in_right.
  aac_normalise. 
  (* TOFIX: can we prevent the unfoldings? *)
  ra_fold hrel_monoid_ops nat.
  (* TOFIX: incomplete folding *)
Abort.
*)
