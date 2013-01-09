(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * prop: Propositions ([Prop]) as a bounded distributive lattice *)

Require Import lattice.

(** lattice operations *)

Canonical Structure Prop_lattice_ops: lattice.ops := {|
  leq := impl;
  weq := iff;
  cup := or;
  cap := and;
  neg := not;
  bot := False;
  top := True
|}.

(** bounded distributive lattice laws 
   (we could get a Boolean lattice by assuming excluded middle) *)

Instance Prop_lattice_laws: lattice.laws (BDL+STR+CNV+DIV) Prop_lattice_ops.
Proof.
  constructor; (try apply Build_PreOrder); simpl;
    repeat intro; try discriminate; tauto. 
Qed.

(** we could also equip Prop with a flat monoid structure, but this is
   not useful in practice *)
(*
Require Import monoid.

CoInductive Prop_unit := Prop_tt.

Canonical Structure Prop_ops: monoid.ops := {|
  ob := Prop_unit;
  mor n m := Prop_lattice_ops;
  dot n m p := and;
  one n := True;
  str n x := True;
  cnv n m x := x;
  ldv n m p := impl;
  rdv n m p := impl
|}.

Notation Prop' := (Prop_ops Prop_tt Prop_tt).

Instance Prop_laws: laws (BDL+STR+CNV+DIV) Prop_ops.
Proof.
  constructor; [intros; apply Prop_lattice_laws |..];
    (try now left); repeat right; simpl; try tauto.
Qed.
*)
