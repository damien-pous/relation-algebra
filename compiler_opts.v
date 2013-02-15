(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * compiler_opts: certifying compiler optimisations *)

(** To illustrate some usage of the kat and hkat tactics, we formalise
   most of the compiler optimisations studied in the following paper:

   Dexter Kozen and Maria-Cristina Patron. 
   Certification of compiler optimizations using Kleene algebra with tests. 
   In Proc. 1st Int. Conf. Computational Logic (CL2000), 
   Vol. 1861 of LNAI, pages 568-582, July 2000. Springer-Verlag.

   Most goals are solved with one single call to [kat] or [hkat]. 

   The remaining cases correspond to situations where one has to
   exploit permutations of some Kleene variables (the Horn theory of
   KA with such commutation hypotheses is undecidable). *)

Require Import kat normalisation rewriting kat_tac.
Set Implicit Arguments.

(** in this module, we prefer the ";" notation for composition *)
Infix " ;" := (dot _ _ _) (left associativity, at level 40): ra_terms. 


(** ** preliminary lemmas  *)

Lemma lemma_1 `{L: monoid.laws} `{Hl: BKA<<l} n (x y: X n n): 
  x;y == x;y;x -> x;y^* == x;(y;x)^*.
Proof. 
  intro H. apply antisym. apply str_ind_r'. ka. 
  rewrite str_dot, <-dotA. rewrite H at 2. ka.
  rewrite str_dot. apply str_ind_l'. ka. 
  rewrite str_unfold_l. ra_normalise. rewrite <-H. ka.
Qed.

Lemma lemma_1' `{L: monoid.laws} `{Hl: BKA<<l} n (x y: X n n): 
  y;x == x;(y;x) -> y^*;x == (x;y)^*;x.
Proof. monoid.dual @lemma_1. Qed.

Lemma lemma_1'' `{L: monoid.laws} `{Hl: BKA<<l} n (p q r: X n n):
  p;q == q;p -> p;r == r -> (p;q)^*;r == q^*;r. 
Proof.
  intros Hpq Hpr. apply antisym.
  rewrite Hpq. apply str_ind_l'. ka. apply str_move in Hpq. mrewrite Hpq. mrewrite Hpr. ka. 
  apply str_ind_l'. ka. rewrite <-str_snoc at 2. rewrite Hpq at 2 3. mrewrite Hpr. ka. 
Qed.

Lemma lemma_2 `{L: laws} n b (q: X n n): 
  [b];q == q;[b] -> [b];q^* == [b];(q;[b])^*.
Proof. hkat. Qed.


(** ** 3.1 Deadcode elimination  *)

Lemma opti_3_1_a `{L: laws} n (a: tst n) (p q: X n n): 
  p == p;[!a] -> p;([a];q+[!a]) == p.
Proof. hkat. Qed.

Lemma opti_3_1_b `{L: laws} n (a: tst n) (p q: X n n): 
  p == p;[!a] -> p;([a];q)^*;[!a] == p.
Proof. hkat. Qed.


(** ** 3.2 Common sub-expression elimination  *)

Lemma opti_3_2 `{L: laws} n (a b: tst n) (p q r w: X n n):
  p == p;[a] -> 
  [a];q == [a];q;[b] -> 
  [b];r == [b] -> 
  r == w;r -> 
  q;w == w -> 
  p;q == p;r.
Proof. 
  intros Hpa Haq Hbr Hr Hw. 
  rewrite Hr, <-Hw. mrewrite <-Hr.
  hkat. 
Qed.


(** ** 3.3 Copy propagation *)

Lemma opti_3_3 `{L: laws} n (a b: tst n) (p q r s v w: X n n):
  q == q;[a] -> 
  [a];r == [a];r;[b] -> 
  [b];s == [b] -> 
  s == w;s -> 
  r;w == w -> 
  s;v == v;s -> 
  q;v == v -> 
  p;q;r;v == p;s;v.
Proof. 
  intros Hqa Har Hbs Hs Hw Hsv Hv. 
  mrewrite Hsv. rewrite <-Hv at 2. mrewrite <-Hsv. 
  rewrite Hs, <-Hw. mrewrite <-Hs.
  hkat. 
Qed.


(** ** 3.4 Loop Hoisting *)

Lemma opti_3_4i `{L: laws} n (a b: tst n) (p q r s u w: X n n):
  u;[b] == u ->
  [b];u == [b] ->
  [b];q == q;[b] -> 
  [b];s == s;[b] -> 
  [b];r == r;[b] -> 
  [a];w == w;[a] ->
  u;r == q -> 
  u;w == w -> 
  q;s;w == w;q;s ->
  p;u;([a];r;s)^*;[!a];w == p;([a];q;s)^*;[!a];w.
Proof.
  intros ? ? ? ? ? ? Hur Huw Hqsw. 
  transitivity (p;u;[b];([a];[b];(u;r);s)^*;[!a];w). hkat. rewrite Hur. 
  transitivity (p;u;([a];q;s)^*;w;[!a]). hkat. 
  assert (E: w;([a];q;s)^* == ([a];q;s)^*;w) by (apply str_move; mrewrite Hqsw; hkat). 
  mrewrite <-E. mrewrite Huw. mrewrite E. hkat. 
Qed.

Lemma opti_3_4ii `{L: laws} n (a: tst n) (p q u w: X n n):
  u == w;u ->
  u;w == w ->
  w;p;q == p;q;w ->
  w;[a] == [a];w -> 
  ([a];u;p;q)^*;[!a];u == ([a];p;q)^*;[!a];u.
Proof.
  intros Hwu Huw Hpq Hw. rewrite Hwu at 1 2. transitivity (w;([a];u;(p;q;w))^*;[!a];u). hkat.
  rewrite <-Hpq. mrewrite Huw. mrewrite Hpq. rewrite <-lemma_1. 
  rewrite (str_move (z:=[a];p;q)). rewrite Hwu at 2. hkat. mrewrite <-Hpq. hkat. 
  mrewrite <-Hpq. rewrite <-Huw at 1. rewrite Hwu. mrewrite Huw. hkat. 
  (* intros Hwu Huw Hpq Hw. rewrite Hwu at 1 2. transitivity (w;([a];u;(p;q;w))^*;[!a];u). hkat. *)
  (* rewrite <-Hpq. mrewrite Huw. mrewrite Hpq. transitivity ((w;[a];p;q)^*;[!a];(w;u)). hkat.  *)
  (* rewrite <-3dotA, lemma_1'', <-Hwu. ra. mrewrite <-Hpq. hkat. rewrite <-Hwu at 1. hkat.  *)
Qed.


(** ** 3.5 Induction variable elimination *)

Lemma opti_3_5 `{L: laws} n (a b c: tst n) (p q r: X n n):
  q == q;[b] -> 
  [b] == [b];q -> 
  [c];r == [c];r;[b] -> 
  [b];p == [b];p;[c] -> 
  [c];q == [c];r -> 
  q;([a];p;q)^* == q;([a];p;r)^*.
Proof. 
  intros Hq Hb Hr Hbp Hcq.
  assert (E: [b];p;q == [b];p;r) by (rewrite Hbp; mrewrite Hcq; hkat). 
  transitivity (q;([a];([b];p;q))^*;[b]). hkat. rewrite E. hkat. 
Qed.


(** ** (3.6 and 3.7 are void) *)


(** ** 3.8 Loop unrolling *)

Lemma lemma_3 `{L: monoid.laws} `{Hl: BKA<<l} n (u: X n n): u^* == (1+u);(u;u)^*.
Proof. ka. Qed.

Lemma opti_3_8 `{L: laws} n a (p: X n n): 
  ([a];p)^*;[!a] == ([a];p;([a];p+[!a]))^*;[!a].
Proof. kat. Qed.


(** ** 3.9 Redundant loads and stores *)

Lemma opti_3_9 `{L: laws} n a (p q: X n n): 
  p == p;[a] -> [a];q == [a] -> p;q == p.
Proof. intros Hp Hq. hkat. Qed.


(** ** 3.10 Array bounds check elimination *)

Lemma opti_3_10'i `{L: laws} n (a b: tst n) (u v p q s: X n n): 
  u;[a] == u -> 
  [a\cap b];p == p;[a\cap b] ->
  [a];([b];p;q;v) == ([b];p;q;v);[a] ->
  u;([b];p;([a\cap b];q+[!(a\cap b)];s);v)^*;[!b] == u;([b];p;q;v)^*;[!b].
Proof. hkat. Qed.

Lemma opti_3_10' `{L: laws} n (a b c: tst n) (u v p q s: X n n): 
  a\cap b == c ->
  u;[a] == u -> 
  [c];p == p;[c] ->
  [a];([b];p;q;v) == ([b];p;q;v);[a] ->
  u;([b];p;([c];q+[!c];s);v)^*;[!b] == u;([b];p;q;v)^*;[!b].
Proof. hkat. Qed.


(** ** 3.11 Introduction of sentinels *)

Lemma opti_3_11 `{L: laws} n (a b c d: tst n) (u p q s t: X n n):
  u;[c] == u ->
  [c];p == p;[c] ->
  [c];q == q;[c] ->
  p;[d] == p ->
  [a];q;[d] == [a];q ->
  c \cap d \cap b <== a ->
  u;p;([a\cap b];q)^*;[!(a\cap b)];([a];t+[!a];s) == u;p;([b];q)^*;[!b];([a];t+[!a];s).
Proof. hkat. Qed.

(* note that it takes about 2s to solve this last one, thus
   illustrating the limits of our very basic algorithm *)
