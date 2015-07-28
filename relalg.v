(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2015: Damien Pous, Insa Stucke.                      *)
(*******************************************************************)

Require Export lattice monoid kleene normalisation rewriting kat_tac.

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



(** algebraic properties of relations 
    we use typeclasses to infer those properties automatically whenever possible
    typically, [rewrite transitive] will rewrite the first occurrence of a
    pattern [x*x] such that [x] is provably transitive. 
*)


Section props.
  
Context `{X: ops}. 

Class is_reflexive n (x: X n n) := reflexive: 1 <== x.
Class is_irreflexive n (x: X n n) := irreflexive: x <== !1.
Class is_transitive n (x: X n n) := transitive: x * x <== x.
Class is_symmetric n (x: X n n) := symmetric_: x` <== x. (* see below for [symmetric] *)
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

Context {l} {L:laws l X}.

Lemma symmetric {Hl: CNV<<l} {n} {x: X n n} {Hx: is_symmetric x}: x`==x.
Proof. apply antisym. assumption. now cnv_switch. Qed.

Lemma vector' {Hl: TOP<<l} {n m} {v: X n m} {Hv: is_vector v} x: v * x <== v.
Proof. rewrite <-vector at 2. ra. Qed.

Global Instance is_symmetric_neg1 {Hl: BL+CNV<<l} {n}: is_symmetric (!one n).
Proof. unfold is_symmetric. rewrite <-dotx1. apply Schroeder_. rewrite negneg. ra. Qed.

Global Instance irreflexive_cnv {Hl: BL+CNV<<l} {n} {x: X n n} {H: is_irreflexive x}: is_irreflexive (x`).
Proof. unfold is_irreflexive. cnv_switch. now rewrite symmetric. Qed.

Context {Hl: CNV<<l}.

Global Instance reflexive_cnv {n} {x: X n n} {H: is_reflexive x}: is_reflexive (x`).
Proof. unfold is_reflexive. cnv_switch. now ra_normalise. Qed.

Global Instance transitive_cnv {n} {x: X n n} {H: is_transitive x}: is_transitive (x`).
Proof. unfold is_transitive. cnv_switch. now ra_normalise. Qed.

Global Instance symmetric_cnv {n} {x: X n n} {H: is_symmetric x}: is_symmetric (x`).
Proof. unfold is_symmetric. now cnv_switch. Qed.

Global Instance antisymmetric_cnv {Hl': CAP+CNV<<l} {n} {x: X n n} {H: is_antisymmetric x}: is_antisymmetric (x`).
Proof. clear Hl. unfold is_antisymmetric. now rewrite cnv_invol, capC. Qed.

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

End props.

Instance order_cnv `{laws} `{BL+CNV<<l} {n} {x: X n n} {H: is_order x}: is_order (x`).
Proof. constructor; eauto with typeclass_instances. Qed.

(** properties of Kleene star and strict iteration *)

Instance preorder_str `{laws} `{STR<<l} n (x: X n n): is_preorder (x^*).
Proof. split. apply str_refl. apply weq_leq, str_trans. Qed.

Instance symmetric_str `{laws} `{STR+CNV<<l} {n} {x: X n n} {Hx: is_symmetric x}: is_symmetric (x^*).
Proof. unfold is_symmetric. now rewrite cnvstr, symmetric. Qed.

Instance reflexive_itr `{laws} `{STR<<l} {n} {x: X n n} {Hx: is_reflexive x}: is_reflexive (x^+).
Proof. unfold is_reflexive. rewrite reflexive. apply itr_ext. Qed.

Instance transitive_itr `{laws} `{STR<<l} n (x: X n n): is_transitive (x^+).
Proof. apply itr_trans. Qed.

Instance symmetric_itr `{laws} `{STR+CNV<<l} {n} {x: X n n} {Hx: is_symmetric x}: is_symmetric (x^+).
Proof. unfold is_symmetric. now rewrite cnvitr, symmetric. Qed.

Lemma itr_transitive `{laws} `{STR<<l} n (R: X n n): is_transitive R -> R^+ == R.
Proof. 
  intro. apply antisym. now apply itr_ind_l1. apply itr_ext.
Qed.

Lemma str_transitive `{laws} `{STR+CUP<<l} n (R: X n n): is_transitive R -> R^* == 1+R.
Proof. intro. now rewrite str_itr, itr_transitive. Qed.


(** alternative characterisation of [is_total] and [is_surjective] *)

Lemma total_xt `{laws} `{TOP<<l} {n m x} {Hx: @is_total X n m x} p: x*top' _ p == top.
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

Lemma surjective_tx `{laws} `{TOP<<l} {n m} {x: X n m} {Hx: is_surjective x} p: top' p _ * x == top.
Proof. now dual @total_xt. Qed.

Lemma tx_surjective `{laws} `{TOP+CAP+CNV<<l} n m (x: X m n): top' n n <== top*x -> is_surjective x.
Proof. now dual @xt_total. Qed.


(** lemmas about relations of a specific shape *)

Lemma dot_univalent_cap `{laws} `{CAP+CNV<<l} {n m p} {x: X n m} {y z: X m p}
  {E: is_univalent x}: x * (y ^ z) == (x*y) ^ (x*z).  
Proof. apply antisym. ra. rewrite capdotx. mrewrite univalent. ra. Qed.

Lemma dot_cap_injective `{laws} `{CAP+CNV<<l} {n m p} {x: X m n} {y z: X p m}
  {E: is_injective x}: (y ^ z) * x == (y*x) ^ (z*x).  
Proof. revert E. dual @dot_univalent_cap. Qed.
