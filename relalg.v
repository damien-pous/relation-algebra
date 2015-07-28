(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2015: Damien Pous, Insa Stucke.                      *)
(*******************************************************************)

Require Import lattice monoid normalisation rewriting.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** generic lemmas *)

Lemma dottx `{laws} `{TOP<<l} n m (x: X n m): x <== top*x.
Proof. rewrite <-dot1x at 1. apply dot_leq; lattice. Qed.

Lemma dotxt `{laws} `{TOP<<l} n m (x: X m n): x <== x*top.
Proof. dual @dottx. Qed.

Lemma top_nnm `{laws} `{TOP<<l} n m: top' n n * top' n m == top' n m. 
Proof. apply leq_tx_iff. apply dottx. Qed.

Lemma top_mnn `{laws} `{TOP<<l} n m: top' m n * top' n n == top' m n. 
Proof. dual @top_nnm. Qed.



(** algebraic properties of relations *)


Section props.
  
Context `{X: ops}. 

Class is_reflexive n (x: X n n) := reflexive: 1 <== x.
Class is_irreflexive n (x: X n n) := irreflexive: x <== !1.
Class is_transitive n (x: X n n) := transitive: x * x <== x.
Class is_symmetric n (x: X n n) := symmetric: x` == x.
Class is_antisymmetric n (x: X n n) := antisymmetric: x`\cap x <== 1.
Class is_univalent n m (x: X n m) := univalent: x` * x <== 1.
Class is_injective n m (x: X n m) := injective: x * x` <== 1.
Class is_surjective n m (x: X n m) := surjective: 1 <== x` * x.
Class is_total n m (x: X n m) := total: 1 <== x * x`.
Class is_vector n m (v: X n m) := vector: v*top == v.

Class is_point n m (p: X n m) := {
  point_vector:> is_vector p;
  point_injective:> is_injective p;
  point_surjective:> is_surjective p}.

Class is_mapping n m (f: X n m) := {
  mapping_univalent:> is_univalent f;
  mapping_total:> is_total f}.

Class is_per n (e: X n n) := {
  per_symmetric:> is_symmetric e;
  per_transitive:> is_transitive e}.

Class is_preorder n (p: X n n) := {
  pre_reflexive:> is_reflexive p;
  pre_transitive:> is_transitive p}.

Class is_order n (p: X n n) := {
  ord_preorder:> is_preorder p;
  ord_antisymmetric:> is_antisymmetric p}.

Context {l} {L:laws l X} {Hl: CNV<<l}.

Global Instance reflexive_cnv {n} {x: X n n} {H: is_reflexive x}: is_reflexive (x`).
Proof. unfold is_reflexive. cnv_switch. now ra_normalise. Qed.

Global Instance irreflexive_cnv {n} {x: X n n} {H: is_irreflexive x}: is_irreflexive (x`).
Admitted.

Global Instance transitive_cnv {n} {x: X n n} {H: is_transitive x}: is_transitive (x`).
Proof. unfold is_transitive. cnv_switch. now ra_normalise. Qed.

Global Instance symmetric_cnv {n} {x: X n n} {H: is_symmetric x}: is_symmetric (x`).
Proof. unfold is_symmetric. now rewrite cnv_invol. Qed.

Global Instance antisymmetric_cnv {n} {x: X n n} {H: is_antisymmetric x}: is_antisymmetric (x`).
Admitted.                       (* need CAP<<l *)

Global Instance injective_cnv {n m} {x: X n m} {H: is_univalent x}: is_injective (x`).
Proof. unfold is_injective. now rewrite cnv_invol. Qed.

Global Instance univalent_cnv {n m} {x: X n m} {H: is_injective x}: is_univalent (x`).
Proof. unfold is_univalent. now rewrite cnv_invol. Qed.

Global Instance surjective_cnv {n m} {x: X n m} {H: is_total x}: is_surjective (x`).
Proof. unfold is_surjective. now rewrite cnv_invol. Qed.

Global Instance total_cnv {n m} {x: X n m} {H: is_surjective x}: is_total (x`).
Proof. unfold is_total. now rewrite cnv_invol. Qed.

Global Instance preorder_cnv {n} {x: X n n} {H: is_preorder x}: is_preorder (x`).
Proof. constructor; eauto with typeclass_instances. Qed.

Global Instance order_cnv {n} {x: X n n} {H: is_order x}: is_order (x`).
Proof. constructor; eauto with typeclass_instances. Qed.

End props.

(** alternative characterisation of [is_total]  *)

Lemma total_xt `{laws} `{TOP+CNV<<l} {n m x} {Hx: @is_total X n m x} p: x*top' _ p == top.
Proof.
  apply leq_tx_iff. transitivity (x * x` * top' _ p).
  rewrite <-total. ra. rewrite <-dotA. apply dot_leq; lattice.
Qed.

Lemma xt_total `{laws} `{TOP+CAP+CNV<<l} n m (x: X n m): top' n n <== x*top -> is_total x.
Proof.
  intro E. unfold is_total.
  transitivity (1 ^ (x*top' m n)). rewrite <-E. lattice.
  rewrite capC, capdotx. ra. 
Qed.

(** lemmas about relations of a specific shape *)

Lemma dot_univalent_cap `{laws} `{CAP+CNV<<l} n m p (x: X n m)(y z: X m p)
  {E: is_univalent x}: x * (y ^ z) == (x*y) ^ (x*z).  
Proof. apply antisym. ra. rewrite capdotx. mrewrite univalent. ra. Qed.

Lemma dot_cap_injective `{laws} `{CAP+CNV<<l} n m p (x: X m n)(y z: X p m)
  {E: is_injective x}: (y ^ z) * x == (y*x) ^ (z*x).  
Proof. revert E. dual @dot_univalent_cap. Qed.
