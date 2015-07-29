(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * factors: additional properties of left and right factors *)

Require Import kleene.
Set Implicit Arguments.

Lemma ldv_dotx `{laws} `{DIV<<l} n m p q (x: X n m) (y: X m p) (z: X n q): x*y -o z == y -o x -o z.
Proof.
  apply from_below. intro t. 
  now rewrite 3ldv_spec, dotA.
Qed.

Lemma ldv_xdot `{laws} `{DIV<<l} n m p (x: X n m) (y: X m p): y <== x -o (x*y).
Proof. now rewrite ldv_spec. Qed.

Lemma ldv_1x `{laws} `{DIV<<l} n m (x: X n m): 1 -o x == x.
Proof. apply from_below. intro y. now rewrite ldv_spec, dot1x. Qed.

Lemma ldv_0x `{laws} `{DIV+BOT+TOP<<l} n m p (x: X n m): 0 -o x == top' p m.
Proof. apply from_below. intro y. rewrite ldv_spec, dot0x. split; intros _; lattice. Qed.

Lemma ldv_xt `{laws} `{DIV+TOP<<l} n m p (x: X n m): x -o top == top' m p.
Proof. apply from_below. intro y. rewrite ldv_spec. split; intros _; lattice. Qed.

Lemma str_ldv `{laws} `{STR+DIV<<l} n m (x: X n m): (x -o x)^* == x -o x. 
Proof. apply antisym. apply str_ldv_. apply str_ext. Qed.

Lemma ldv_rdv `{laws} `{DIV<<l} n m p q (x: X n m) y (z: X p q): x -o (y o- z) == (x -o y) o- z.
Proof. apply from_below. intro. now rewrite ldv_spec, 2rdv_spec, ldv_spec, dotA. Qed.

Lemma ldv_unfold `{laws} `{BL+DIV+CNV<<l} n m p (x: X n m) (y: X n p): x -o y == !(x` * !y).
Proof. apply from_below. intro. now rewrite ldv_spec, neg_leq_iff', <-Schroeder_l. Qed.


(** dual properties for right factors *)

Lemma rdv_cancel `{laws} `{DIV<<l} n m p (x: X m n) (y: X p n): (y o- x)*x <== y.
Proof. dual @ldv_cancel. Qed.

Lemma rdv_dotx `{laws} `{DIV<<l} n m p q (x: X m n) (y: X p m) (z: X q n): z o- y*x == z o- x o- y.
Proof. dual @ldv_dotx. Qed.

Lemma rdv_xdot `{laws} `{DIV<<l} n m p (x: X m n) (y: X p m): y <== y*x o- x.
Proof. dual @ldv_xdot. Qed.

Lemma leq_rdv `{laws} `{DIV<<l} n m (x y: X m n): x <== y <-> 1 <== y o- x. 
Proof. dual @leq_ldv. Qed.

Lemma rdv_xx `{laws} `{DIV<<l} n m (x: X m n): 1 <== x o- x.
Proof. dual @ldv_xx. Qed.

Lemma rdv_1x `{laws} `{DIV<<l} n m (x: X m n): x o- 1 == x.
Proof. dual @ldv_1x. Qed.

Lemma rdv_0x `{laws} `{DIV+BOT+TOP<<l} n m p (x: X m n): x o- 0 == top' m p.
Proof. dual @ldv_0x. Qed.

Lemma rdv_xt `{laws} `{DIV+TOP<<l} n m p (x: X m n): top o- x == top' p m.
Proof. dual @ldv_xt. Qed.

Lemma rdv_trans `{laws} `{DIV<<l} n m p q (x: X m n) (y: X p n) (z: X q n): 
  (z o- y)*(y o- x) <== z o- x.
Proof. dual @ldv_trans. Qed.

Lemma str_rdv `{laws} `{STR+DIV<<l} n m (x: X m n): (x o- x)^* == x o- x.
Proof. dual @str_ldv. Qed.

Lemma rdv_unfold `{laws} `{BL+DIV+CNV<<l} n m p (x: X m n) (y: X p n): y o- x == !(!y*x`).
Proof. dual @ldv_unfold. Qed.
