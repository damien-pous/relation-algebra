(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2013: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * move: simple tactics allowing to move subterms inside products
  (by exploiting commutation hypotheses from the context) *)

Require Import kat normalisation rewriting kat_tac.

Local Infix " ;" := (dot _ _ _) (left associativity, at level 40): ra_terms. 

Lemma rmov_x_str `{L: monoid.laws} `{Hl: STR<<l} {n} (x e: X n n):
  x;e == e;x -> x;e^* == e^*;x.
Proof. apply str_move. Qed.

Lemma rmov_x_itr `{L: monoid.laws} `{Hl: STR<<l} {n} (x e: X n n):
  x;e == e;x -> x;e^+ == e^+;x.
Proof. apply itr_move. Qed.

Lemma rmov_x_pls `{L: monoid.laws} `{Hl: CUP<<l} {n m} x y (e f: X n m):
  x;e == e;y -> x;f == f;y -> x;(e+f) == (e+f);y. 
Proof. intros. ra_normalise. now apply cup_weq. Qed.

Lemma rmov_x_dot `{L: monoid.laws} {n m p} x y z (e: X n m) (f: X m p):
  x;e == e;y -> y;f == f;z -> x;(e;f) == (e;f);z.
Proof. intros He Hf. rewrite dotA, He, <-dotA, Hf. apply dotA. Qed.

Lemma rmov_x_1 `{L: monoid.laws} {n} (x: X n n): x;1 == 1;x.
Proof. ra. Qed.

Lemma rmov_x_0 `{L: monoid.laws} `{Hl:BOT<<l} {n m p q} (x: X n m) (y: X p q): x;0 == 0;y.
Proof. ra. Qed.

Lemma rmov_x_cap `{L: laws} {n} (x: X n n) a b:
  x;[a] == [a];x -> x;[b] == [b];x -> x;[a\cap b] == [a\cap b];x.
Proof. hkat. Qed.

Lemma rmov_x_cup `{L: laws} {n} (x: X n n) a b:
  x;[a] == [a];x -> x;[b] == [b];x -> x;[a\cup b] == [a\cup b];x.
Proof. hkat. Qed.

Lemma rmov_x_neg `{L: laws} {n} (x: X n n) a:
  x;[a] == [a];x -> x;[!a] == [!a];x.
Proof. hkat. Qed.

Lemma rmov_inj `{L: laws} {n} (a b: tst n): [a]*[b] == [b]*[a].
Proof. kat. Qed.

Ltac solve_rmov :=
  first 
    [ eassumption 
    | symmetry; eassumption
    | eapply rmov_x_dot
    | apply rmov_x_pls
    | apply rmov_x_str
    | apply rmov_x_itr
    | apply rmov_x_cap
    | apply rmov_x_cup
    | apply rmov_x_neg
    | apply rmov_inj
    | apply rmov_x_1
    | apply rmov_x_0 ]; solve_rmov.

Ltac rmov1 x :=
  rewrite ?dotA;
  (* rewrite ?(dotA _ _ x); *)
  match goal with 
    | |- context [@dot ?X ?n ?n ?m x ?e] => 
      let H := fresh "H" in 
      let y := fresh "y" in
      evar (y: car (X m m));
      assert (H: x;e == e;y) by (subst y; solve_rmov); 
      rewrite H; subst y; clear H
    | |- context [@dot ?X _ ?n ?m (?f;x) ?e] => 
      let H := fresh "H" in 
      let y := fresh "y" in
      evar (y: car (X m m));
      assert (H: x;e == e;y) by (subst y; solve_rmov); 
      rewrite <-(dotA f x e), H; subst y; clear H
  end.

Ltac lmov1 x :=
  rewrite <-?dotA;
  (* rewrite <-?(dotA x); *)
  match goal with 
    | |- context [@dot ?X ?m ?n ?n ?e x] => 
      let H := fresh "H" in 
      let y := fresh "y" in
      evar (y: car (X m m));
      assert (H: y;e == e;x) by (subst y; solve_rmov); 
      rewrite <-H; subst y; clear H
    | |- context [@dot ?X ?m _ _ ?e (x;?f)] => 
      let H := fresh "H" in 
      let y := fresh "y" in
      evar (y: car (X m m));
      assert (H: y;e == e;x) by (subst y; solve_rmov); 
      rewrite (dotA e x f), <-H; subst y; clear H
  end.

(* test
Goal forall `{laws} n (p q q' r r': X n n) (a b: tst n),
  r;[a] == [a];r -> 
  r;p == p;r ->
  r;q == q;r' ->
  p;[a];r;p^*;(q;q') == 0.
Proof. 
  intros. 
  rmov1 r. 
  rmov1 r. 
  lmov1 r'.
  lmov1 r.
  lmov1 r.
  lmov1 r.
Abort.
*)
