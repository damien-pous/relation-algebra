(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * sums: finite sums, a la ssreflect *)

(** this tiny module extends [sups] to the setting of monoids (it is
   a separate module just to avoid [sups] to depend on [monoid]) *)

Require Import monoid.
Require Export sups.

(** in the setting of monoids, we prefer the "sum" notation *)

Notation "\sum_ ( i \in l ) f" := (@sup (mor _ _) _ (fun i => f) l)
  (at level 41, f at level 41, i, l at level 50,
    format "'[' \sum_ ( i \in  l ) '/  '  f ']'"): ra_terms.

Notation "\sum_ ( i < n ) f" := (\sum_(i \in seq n) f)
  (at level 41, f at level 41, i, n at level 50,
    format "'[' \sum_ ( i < n ) '/  '  f ']'"): ra_terms.

(** [dot] distributes over sums *)
Lemma dotxsum `{laws} `{BSL<<l} I J n m p (f: I -> X m n) (x: X p m): 
  x * (\sum_(i\in J) f i) == \sum_(i\in J) (x * f i).
Proof. apply f_sup_weq. apply dotx0. intros; apply dotxpls. Qed.

Lemma dotsumx `{laws} `{BSL<<l} I J n m p (f: I -> X n m) (x: X m p): 
  (\sum_(i\in J) f i) * x == \sum_(i\in J) (f i * x).
Proof. dual @dotxsum. Qed.

(** converse commutes with sums *)
Lemma cnvsum `{laws} `{BSL+CNV<<l} I J n m (f: I -> X n m): 
  (\sum_(i\in J) f i)` == \sum_(i\in J) (f i`).
Proof. apply f_sup_weq. apply cnv0. apply cnvpls. Qed.
