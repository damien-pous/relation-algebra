(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2015: Damien Pous, Insa Stucke.                      *)
(*******************************************************************)

(** * relalg: standard relation algebra facts and definitions *)

Require Export common lattice monoid kleene normalisation rewriting.

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

Lemma disjoint_id `{laws} `{AL+BOT<<l} n m (p q: X n m): p \cap q <== 0 -> 1\cap (p*q`) == 0. 
Proof. 
  intro Hpq. apply leq_xb_iff. rewrite capC, capxdot. ra_normalise.
  rewrite Hpq. ra. 
Qed.

Lemma dedekind `{laws} `{AL<<l} n m p (x : X n m) (y : X m p) (z : X n p):
  x*y \cap z <== (x \cap (z*y`))*(y \cap (x`*z)).
Proof. rewrite <-(capI z) at 1. rewrite capA, capdotx, capxdot. ra. Qed.
  
(** algebraic properties of relations 
    we use typeclasses to infer those properties automatically whenever possible
    typically, [rewrite transitive] will rewrite the first occurrence of a
    pattern [x*x] such that [x] is provably transitive. 
*)

Ltac tc := solve [eauto with typeclass_instances].

Class is_nonempty {X: ops} n m (x: X n m) := nonempty: forall p q, top' p q <== top * x * top.
Notation is_nonempty' m := (is_nonempty (one m)).

Lemma nonempty_dom `{laws} `{TOP<<l} n m {x: X n m} {Hx: is_nonempty x}: is_nonempty' n.
Proof. intros i j. rewrite nonempty. mrewrite (leq_xt (x*top' _ j)). ra. Qed.

Lemma nonempty_cod `{laws} `{TOP<<l} n m {x: X n m} {Hx: is_nonempty x}: is_nonempty' m.
Proof. intros i j. rewrite nonempty. rewrite (leq_xt (top' i _*x)). ra. Qed.


Section props.
  
Context {l: level} {X: ops}. 

Class is_reflexive n (x: X n n) := reflexive: 1 <== x.
Class is_irreflexive n (x: X n n) := irreflexive: x \cap 1 == 0.
Class is_transitive n (x: X n n) := transitive: x * x <== x.
Class is_linear n (x: X n n) := linear: x \cup x` == top.
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
  point_nonempty:> is_nonempty p}.

Class is_atom n m (a: X n m) := {
  a_top_a': a*top*a` <== 1;
  a'_top_a: a`*top*a <== 1;
  atom_nonempty:> is_nonempty a}.

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

Context {L: laws l X}.

(** all properties are compatible with equality  *)

Global Instance is_reflexive_weq {n}: Proper (weq ==> iff) (@is_reflexive n).
Proof. intros ? ? E. unfold is_reflexive. now rewrite E. Qed.
Global Instance is_irreflexive_weq {n} `{CAP<<l}: Proper (weq ==> iff) (@is_irreflexive n).
Proof. intros ? ? E. unfold is_irreflexive. now rewrite E. Qed.
Global Instance is_transitive_weq {n}: Proper (weq ==> iff) (@is_transitive n).
Proof. intros ? ? E. unfold is_transitive. now rewrite E. Qed.
Global Instance is_linear_weq `{CUP+CNV<<l} {n}: Proper (weq ==> iff) (@is_linear n).
Proof. intros ? ? E. unfold is_linear. now rewrite E. Qed.
Global Instance is_symmetric_weq `{CNV<<l} {n}: Proper (weq ==> iff) (@is_symmetric n).
Proof. intros ? ? E. unfold is_symmetric. now rewrite E. Qed.
Global Instance is_antisymmetric_weq `{AL<<l} {n}: Proper (weq ==> iff) (@is_antisymmetric n).
Proof. intros ? ? E. unfold is_antisymmetric. now rewrite E. Qed.
Global Instance is_univalent_weq `{CNV<<l} {n m}: Proper (weq ==> iff) (@is_univalent n m).
Proof. intros ? ? E. unfold is_univalent. now rewrite E. Qed.
Global Instance is_injective_weq `{CNV<<l} {n m}: Proper (weq ==> iff) (@is_injective n m).
Proof. intros ? ? E. unfold is_injective. now rewrite E. Qed.
Global Instance is_surjective_weq `{CNV<<l} {n m}: Proper (weq ==> iff) (@is_surjective n m).
Proof. intros ? ? E. unfold is_surjective. now rewrite E. Qed.
Global Instance is_total_weq `{CNV<<l} {n m}: Proper (weq ==> iff) (@is_total n m).
Proof. intros ? ? E. unfold is_total. now rewrite E. Qed.
Global Instance is_vector_weq {n m}: Proper (weq ==> iff) (@is_vector n m).
Proof. intros ? ? E. unfold is_vector. now rewrite E. Qed.
Global Instance is_nonempty_weq {n m}: Proper (weq ==> iff) (@is_nonempty X n m).
Proof. intros ? ? E. unfold is_nonempty. now setoid_rewrite E. Qed.

Lemma proper_weq_leq_iff n m (P: X n m -> Prop): Proper (weq ==> impl) P -> Proper (weq ==> iff) P.
Proof. intros HP ? ? E. split; now apply HP. Qed.

Global Instance is_point_weq `{CNV<<l} {n m}: Proper (weq ==> iff) (@is_point n m).
Proof. apply proper_weq_leq_iff. intros ? ? E [? ? ?]. split; now rewrite <-E. Qed.
Global Instance is_atom_weq `{CNV<<l} {n m}: Proper (weq ==> iff) (@is_atom n m).
Proof. apply proper_weq_leq_iff. intros ? ? E [? ? ?]. split; now rewrite <-E. Qed.
Global Instance is_mapping_weq `{CNV<<l} {n m}: Proper (weq ==> iff) (@is_mapping n m).
Proof. apply proper_weq_leq_iff. intros ? ? E [? ?]. split; now rewrite <-E. Qed.
Global Instance is_per_weq `{CNV<<l} {n}: Proper (weq ==> iff) (@is_per n).
Proof. apply proper_weq_leq_iff. intros ? ? E [? ?]. split; now rewrite <-E. Qed.
Global Instance is_preorder_weq {n}: Proper (weq ==> iff) (@is_preorder n).
Proof. apply proper_weq_leq_iff. intros ? ? E [? ?]. split; now rewrite <-E. Qed.
Global Instance is_order_weq `{AL<<l} {n}: Proper (weq ==> iff) (@is_order n).
Proof. apply proper_weq_leq_iff. intros ? ? E [? ?]. split; now rewrite <-E. Qed.

(** alternative characterisation of [is_surjective] *)

Lemma surjective_tx `{TOP<<l} {n m} {x: X n m} {Hx: is_surjective x} p: top' p _ * x == top.
Proof.
  apply leq_tx_iff. transitivity (top' p _ * (x` * x)).
  rewrite <-surjective. ra. rewrite dotA. apply dot_leq; lattice.
Qed.

Lemma tx_surjective `{AL+TOP<<l} n m (x: X m n): top' n n <== top*x -> is_surjective x.
Proof.
  intro E. unfold is_surjective.
  transitivity (1 ^ (top' n m * x)). rewrite <-E. lattice.
  rewrite capC, capxdot. ra. 
Qed.

(** basic properties  *)

Lemma symmetric `{CNV<<l} {n} {x: X n n} {Hx: is_symmetric x}: x`==x.
Proof. apply antisym. assumption. now cnv_switch. Qed.

Lemma irreflexive' `{BL<<l} {n} {x: X n n} {Hx: is_irreflexive x}: x <== !1.
Proof. now rewrite <-leq_cap_neg', Hx. Qed.

Lemma vector' `{TOP<<l} {n m} {v: X n m} {Hv: is_vector v} x: v * x <== v.
Proof. rewrite <-vector at 2. ra. Qed.

Lemma top_nonempty `{TOP<<l} {n m p} {Hm: is_nonempty' m}: top' n m * top' m p == top.
Proof. apply leq_tx_iff. rewrite nonempty. ra. Qed.


(** instances for proof search  *)

Global Instance point_surjective `{AL+TOP<<l} {n m} {p: X n m} {Hp: is_point p}: is_surjective p | 1.
Proof. apply tx_surjective. rewrite nonempty at 1. now mrewrite vector. Qed.

Global Instance atom_injective `{TOP<<l} {n m} {a: X n m} {Ha: is_atom a}: is_injective a.
Proof. unfold is_injective. rewrite <-a_top_a'. rewrite <-(leq_xt 1). ra. Qed.

Global Instance atom_univalent `{TOP<<l} {n m} {a: X n m} {Ha: is_atom a}: is_univalent a.
Proof. unfold is_univalent. rewrite <-a'_top_a. rewrite <-(leq_xt 1). ra. Qed.

Global Instance is_symmetric_neg1 `{BL+CNV<<l} {n}: is_symmetric (!one n).
Proof. unfold is_symmetric. rewrite <-dotx1. apply Schroeder_. rewrite negneg. ra. Qed.

Global Instance irreflexive_cnv `{AL+BOT<<l} {n} {x: X n n} {H: is_irreflexive x}: is_irreflexive (x`).
Proof. unfold is_irreflexive. cnv_switch. now ra_normalise. Qed.

Global Instance reflexive_cnv `{CNV<<l} {n} {x: X n n} {H: is_reflexive x}: is_reflexive (x`).
Proof. unfold is_reflexive. cnv_switch. now ra_normalise. Qed.

Global Instance transitive_cnv `{CNV<<l} {n} {x: X n n} {H: is_transitive x}: is_transitive (x`).
Proof. unfold is_transitive. cnv_switch. now ra_normalise. Qed.

Global Instance symmetric_cnv `{CNV<<l} {n} {x: X n n} {H: is_symmetric x}: is_symmetric (x`).
Proof. unfold is_symmetric. now cnv_switch. Qed.

Global Instance antisymmetric_cnv `{AL<<l} {n} {x: X n n} {H: is_antisymmetric x}: is_antisymmetric (x`).
Proof. unfold is_antisymmetric. now rewrite cnv_invol, capC. Qed.

Global Instance injective_cnv `{CNV<<l} {n m} {x: X n m} {H: is_univalent x}: is_injective (x`).
Proof. unfold is_injective. now rewrite cnv_invol. Qed.

Global Instance univalent_cnv `{CNV<<l} {n m} {x: X n m} {H: is_injective x}: is_univalent (x`).
Proof. unfold is_univalent. now rewrite cnv_invol. Qed.

Global Instance surjective_cnv `{CNV<<l} {n m} {x: X n m} {H: is_total x}: is_surjective (x`).
Proof. unfold is_surjective. now rewrite cnv_invol. Qed.

Global Instance total_cnv `{CNV<<l} {n m} {x: X n m} {H: is_surjective x}: is_total (x`).
Proof. unfold is_total. now rewrite cnv_invol. Qed.

Global Instance preorder_cnv `{CNV<<l} {n} {x: X n n} {H: is_preorder x}: is_preorder (x`).
Proof. constructor; tc. Qed.

Global Instance nonempty_cnv `{CNV+TOP<<l} {n m} {x: X n m} {Hx: is_nonempty x}: is_nonempty (x`).
Proof. intros i j. cnv_switch. ra_normalise. apply Hx. Qed.

Global Instance atom_cnv `{CNV+TOP<<l} {n m} {x: X n m} {Hx: is_atom x}: is_atom (x`).
Proof.
  split.
  rewrite cnv_invol. apply a'_top_a.
  rewrite cnv_invol. apply a_top_a'.
  apply nonempty_cnv.
Qed.

Global Instance mapping_cnv `{AL+TOP<<l} {n m} {x: X n m} {Hx: is_point x}: is_mapping (x`).
Proof. split; tc. Qed.          (* actually just need x to be injective and surjective *)

Global Instance order_cnv `{AL<<l} {n} {x: X n n} {Hx: is_order x}: is_order (x`).
Proof. constructor; tc. Qed.

Global Instance vector_cap `{CAP+TOP<<l} {n m} {v w: X n m} {Hv: is_vector v} {Hw: is_vector w}: is_vector (v \cap w). 
Proof. 
  unfold is_vector. apply antisym. 2: apply dotxt. 
  now rewrite dotcapx, 2vector. 
Qed.   

Global Instance preorder_str `{STR<<l} n (x: X n n): is_preorder (x^*).
Proof. split. apply str_refl. apply weq_leq, str_trans. Qed.

Global Instance symmetric_str `{STR+CNV<<l} {n} {x: X n n} {Hx: is_symmetric x}: is_symmetric (x^*).
Proof. unfold is_symmetric. now rewrite cnvstr, symmetric. Qed.

Global Instance reflexive_itr `{STR<<l} {n} {x: X n n} {Hx: is_reflexive x}: is_reflexive (x^+).
Proof. unfold is_reflexive. rewrite reflexive. apply itr_ext. Qed.

Global Instance transitive_itr `{STR<<l} n (x: X n n): is_transitive (x^+).
Proof. apply itr_trans. Qed.

Global Instance symmetric_itr `{STR+CNV<<l} {n} {x: X n n} {Hx: is_symmetric x}: is_symmetric (x^+).
Proof. unfold is_symmetric. now rewrite cnvitr, symmetric. Qed.


(** lemmas about relations of a specific shape *)

Lemma itr_transitive `{STR<<l} n (x: X n n): is_transitive x -> x^+ == x.
Proof. intro. apply antisym. now apply itr_ind_l1. apply itr_ext. Qed.

Lemma str_transitive `{KA<<l} n (x: X n n): is_transitive x -> x^* == 1+x.
Proof. intro. now rewrite str_itr, itr_transitive. Qed.

Lemma dot_mono `{AL<<l} n (x y: X n n): x <== 1 -> y <== 1 -> x*y == x \cap y. 
Proof. 
  intros Hx Hy. apply antisym. apply leq_xcap.
   rewrite Hy; ra.
   rewrite Hx; ra.
  transitivity (x*1 \cap y). ra.
  rewrite capdotx. rewrite Hx at 2.
  ra_normalise. apply dot_leq; lattice. 
Qed.

Lemma kernel_refl_antisym `{laws} `{CAP+CNV<<l} {n} {x: X n n}
  {Hr: is_reflexive x} {Ha: is_antisymmetric x}: x` \cap x == 1. 
Proof. 
  apply antisym. assumption.
  apply cap_spec; split; trivial. 
  now rewrite <-reflexive. 
Qed. 

Lemma dot_univalent_cap `{AL<<l} {n m p} {x: X n m} {y z: X m p}
  {E: is_univalent x}: x * (y ^ z) == (x*y) ^ (x*z).  
Proof. apply antisym. ra. rewrite capdotx. mrewrite univalent. ra. Qed.

Lemma univalent_antisym `{AL+TOP<<l} {n m} {x y: X n m}
  {Hy: is_univalent y}: y*top' m m <== x*top -> x <== y -> x == y. 
Proof. 
  intros Ht Hxy. apply antisym. assumption.
  transitivity (y \cap (x*(top' m m))). rewrite <- Ht, <- dotxt. lattice.
  rewrite capC, capdotx. 
  ra_normalise. rewrite Hxy at 2. mrewrite univalent. ra.
Qed.

Lemma surjective_injective_antisym `{AL+TOP<<l} {n m} {p q: X n m}
   {Hp: is_surjective p} {Hq: is_injective q}: p <== q -> p == q. 
Proof.
  intros Hpq. cnv_switch. apply univalent_antisym.
  cnv_switch; ra_normalise. rewrite surjective_tx. lattice.
  now cnv_switch.
Qed.

Lemma disjoint_vect_iff `{BL+CNV<<l} {n m} {p q: X n m}
  {Hq: is_vector q}: p\cap q <== 0 <-> q`*p <== 0.
Proof.
  rewrite Schroeder_l, cnv_invol, negbot.
  rewrite vector, capC. apply leq_cap_neg'.
Qed.

Lemma disjoint_vect_iff' `{AL+DIV+BOT+TOP<<l} {n m} {p q: X n m}
  {Hq: is_vector q}: p\cap q <== 0 <-> q`*p <== 0.
Proof.
  split; intro Hpq.
   rewrite <-capxt, capdotx, cnv_invol, vector, Hpq. ra.
  rewrite <-ldv_spec in Hpq. rewrite capC, Hpq.
  rewrite <-vector at 1. rewrite capdotx. rewrite ldv_cancel. ra.
Qed.

Lemma gen_point {Hl: CNV+TOP<<l} n m k (p: X n m):
   is_nonempty' k -> is_point p -> is_point (p*top' m k).
Proof.
  intros Hk Hp. split.
  unfold is_vector. now mrewrite top_mnn.
  unfold is_injective. ra_normalise. mrewrite (leq_xt (top' m k * top' k m)).
  mrewrite vector. apply injective.
  intros i j. mrewrite (top_nonempty (n:=m) (m:=k) (p:=j)). apply nonempty. 
Qed.

Lemma leq_xyp `{AL+TOP<<l} {n m k} {p: X m k} {x: X n k} {y: X n m}
  {Hp: is_point p}: x <== y*p <-> x*p` <== y.
Proof.
  split; intro E.
   rewrite <-(dotx1 y). rewrite <-injective. now mrewrite <-E.
   rewrite <-(dotx1 x). rewrite surjective. now mrewrite E.
Qed.

Lemma leq_pxq `{AL+TOP<<l} {n m k} {p: X n k} {q: X m k} {x: X n m}
   {Hp: is_point p} {Hq: is_point q}: p <== x*q <-> q <==x`*p.
Proof. rewrite 2leq_xyp. now rewrite cnv_leq_iff', cnvdot, cnv_invol. Qed.

Lemma point_lattice_atom {Hl: AL+TOP<<l} {n m} {p v: X n m} {Hp: is_point p} {Hv: is_vector v}:
  is_nonempty v -> v <== p -> v == p.
Proof.
  intros Hv' Hvp. apply antisym. assumption.
  assert (is_nonempty (p^v)). rewrite leq_iff_cap in Hvp. now rewrite capC, Hvp.
  apply leq_iff_cap. cnv_switch. ra_normalise.
  apply univalent_antisym. 2: lattice. cnv_switch. ra_normalise.
  rewrite (leq_xt (top*p)). rewrite nonempty. now rewrite <-dotA, vector. 
Qed.


Lemma dot_neg_inj {Hl: BL+CNV<<l} {n m p} {x: X n m} {y: X m p} {Hy: is_injective y}: !x * y <== !(x*y).
Proof. rewrite Schroeder_r, 2negneg. mrewrite injective. ra. Qed.

Lemma dot_neg_surj {Hl: BL+CNV<<l} {n m p} {x: X n m} {y: X m p} {Hy: is_surjective y}: !(x*y) <== !x * y.
Proof.
  rewrite leq_cap_neg. rewrite <-negcup, <-dotplsx, cupneg. now rewrite surjective_tx, negtop.
Qed.

Lemma dot_neg_point {Hl: BL+CNV<<l} {n m k} {x: X n m} {p: X m k} {Hp: is_point p}: !x * p == !(x*p).
Proof. apply antisym. apply dot_neg_inj. apply dot_neg_surj. Qed.

Lemma disjoint_vect_ext {Hl: BL+CNV<<l} {n m k} {x y: X n m} {x' y': X m k}
      {Hx: is_vector x}: x \cap y <== 0 -> (x * x') \cap (y * y') <== 0.
Proof.
  rewrite capC. intro H. apply disjoint_vect_iff in H.
  rewrite capdotx. mrewrite H. ra.
Qed.

Lemma atom_of_points_aux `{AL+TOP<<l} {n m k} {p: X n m} {q: X k m} {Hp: is_point p} {Hq: is_point q}:
  p * q` * top * q * p` <== 1.
Proof.
  mrewrite surjective_tx. transitivity (p*(top*q)`*p`). ra.
  mrewrite surjective_tx. ra_normalise. rewrite vector. now apply injective.
Qed.

Lemma atom_of_points `{AL+TOP<<l} {n m k} {p: X n m} {q: X k m} {Hp: is_point p} {Hq: is_point q}:
  is_atom (p*q`).
Proof.
  split. ra_normalise. apply atom_of_points_aux. 
  ra_normalise. apply atom_of_points_aux.
  intros i j. mrewrite (surjective_tx (x:=p)). now apply nonempty_cnv.
Qed.

Lemma point_a_top `{CNV+TOP<<l} {n m} {a: X n m} {Ha: is_atom a}: is_point (a*top' m m).
Proof.
  split.
  unfold is_vector. now mrewrite top_nnm.
  unfold is_injective. ra_normalise. mrewrite top_nnm. apply a_top_a'.
  intros i j. mrewrite top_nnm. apply atom_nonempty.
Qed.

Lemma point_a'_top `{CNV+TOP<<l} {n m} {a: X n m} {Ha: is_atom a}: is_point (a`*top' n n).
Proof. apply point_a_top. Qed.

Lemma a_top_a_aux `{AL+TOP<<l} {n m} {a: X n m} {Ha: is_atom a}: (a * top) ^ (top * a) == a.
Proof.
  apply antisym.
  rewrite capdotx. mrewrite a'_top_a. ra.
  rewrite <-2(leq_xt 1). ra. 
Qed.  
  
Lemma a_top_a `{AL+TOP<<l} {n m} {a: X n m} {Ha: is_atom a}: a * top * a == a.
Proof.
  rewrite <-a_top_a_aux at 3.
  apply antisym.
  rewrite <-(leq_xt (top*a)), <-(leq_xt (a*top)). ra.
  rewrite capdotx. mrewrite <-(leq_xt (a`*top' n n)). ra.
Qed.

Global Instance atom_transitive `{AL+TOP<<l} {n} {a: X n n} {Ha: is_atom a}: is_transitive a.
Proof. unfold is_transitive. rewrite <-a_top_a at 3. rewrite <-(leq_xt 1). ra. Qed.

(* TOTHINK: transitivity should follow from mono *)
Lemma atom_mono `{AL+TOP<<l} {n} {a: X n n} {Ha: is_atom a}: a*a <== 1.
Proof.
  transitivity (a*a \cap a). apply leq_xcap. reflexivity. apply atom_transitive.
  rewrite dedekind. transitivity ((a*a`)*(a`*a)). apply dot_leq; lattice.
  mrewrite (injective (x:=a)). mrewrite (univalent (x:=a)). ra.
Qed.

Lemma atom_points `{AL+TOP<<l} {n m k} {a: X n m} {Ha: is_atom a} {Hk: is_nonempty' k}:
  exists p q: X _ k, is_point p /\ is_point q /\ a == p*q`.
Proof.
  exists (a*top). exists (a`*top). 
  split. rewrite <-top_nnm, dotA. apply gen_point. assumption. apply point_a_top. 
  split. rewrite <-top_nnm, dotA. apply gen_point. assumption. apply point_a'_top.
  ra_normalise. mrewrite (top_nonempty (n:=m) (p:=n)). now rewrite a_top_a.
Qed.

Lemma atom_lattice_atom {Hl: AL+TOP<<l} {n m} {a x: X n m} {Ha: is_atom a}:
  is_nonempty x -> x <== a -> x == a.
Proof.
  intros Hx Hax. 
  pose proof point_a_top as Hat.
  assert(Hxt: is_vector (x * top' m m)). unfold is_vector. now mrewrite top_nnm.
  apply univalent_antisym. apply weq_geq. apply point_lattice_atom.
   intros i j. mrewrite top_nnm. apply nonempty.
   now rewrite Hax. 
  assumption. 
Qed.

End props.

(** lemmas obtained by duality *)

Lemma total_xt `{laws} `{TOP<<l} {n m} {x: X n m} {Hx: is_total x} p: x*top' _ p == top.
Proof. now dual @surjective_tx. Qed.

Lemma xt_total `{laws} `{AL+TOP<<l} n m (x: X n m): top' n n <== x*top -> is_total x.
Proof. now dual @tx_surjective. Qed.

Lemma dot_cap_injective `{laws} `{AL<<l} {n m p} {x: X m n} {y z: X p m}
      {Hx: is_injective x}: (y ^ z) * x == (y*x) ^ (z*x).  
Proof. revert Hx. dual @dot_univalent_cap. Qed.
