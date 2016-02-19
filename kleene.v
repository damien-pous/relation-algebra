(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** kleene: simple facts about Kleene star  *)
(** and strict iteration *)

Require Export monoid.
Set Implicit Arguments.
Unset Strict Implicit.

(** * properties of Kleene star *)

(** additional induction schemes *)
Lemma str_ind_r' `{laws} `{STR<<l} n m (x: X n n) (y z: X m n): y <== z -> z*x <== z -> y*x^* <== z.
Proof. dual @str_ind_l'. Qed.

Lemma str_ind_r1 `{laws} `{STR<<l} n (x z: X n n): 1 <== z -> z * x <== z -> x ^* <== z.
Proof. dual @str_ind_l1. Qed.

Lemma str_unfold_r `{laws} `{KA<<l} n (x: X n n): x^* == 1 + x^* * x.
Proof. dual @str_unfold_l. Qed.

(** bisimulation rules *)
Lemma str_move_l `{laws} `{STR<<l} n m (x: X n m) y z:
  x * y <== z * x  ->  x * y^* <== z^* * x.
Proof.
  intro E. apply str_ind_r'. now rewrite <-str_refl, dot1x.
  rewrite <-str_snoc at 2. now rewrite <-dotA, E, dotA.
Qed.

Lemma str_move_r `{laws} `{STR<<l} n m (x: X m n) y z:
  y * x <== x * z  ->  y^* * x <== x * z^*.
Proof. dual @str_move_l. Qed.

Lemma str_move `{laws} `{STR<<l} n m (x: X n m) y z:
  x * y == z * x  ->  x * y^* == z^* * x.
Proof. 
  intro. apply antisym. 
  apply str_move_l. now apply weq_leq. 
  apply str_move_r. now apply weq_geq. 
Qed.

Lemma str_dot `{laws} `{STR<<l} n m (x: X n m) y: x * (y * x)^* == (x * y)^* * x.
Proof. apply str_move, dotA. Qed.

(** [str] is uniquely determined *)
Lemma str_unique `{laws} `{STR<<l} n (a x: X n n):
 1<==x -> a*x <== x -> (forall y: X n n, a*y<==y -> x*y<==y) -> a^* == x.
Proof.
  intros H1 H2 H3. apply antisym. now apply str_ind_l1.
  rewrite <-(dotx1 x), (str_refl a). apply H3. apply str_cons.
Qed.  

Lemma str_unique' `{laws} `{KA<<l} n (a x: X n n):
 1+a*x <== x -> (forall y: X n n, a*y<==y -> x*y<==y) -> a^* == x.
Proof. rewrite cup_spec. intros []. now apply str_unique. Qed.  

(** value of [str] on constants  *)
Lemma str1 `{laws} `{STR<<l} n: 1^* == one n.
Proof. apply str_unique. reflexivity. now rewrite dotx1. trivial. Qed.

Lemma str0 `{laws} `{STR+BOT<<l} n: 0^* == one n.
Proof. apply str_unique. reflexivity. rewrite dot0x. lattice. now intros; rewrite dot1x. Qed.

Lemma strtop `{laws} `{STR+TOP<<l} n: top^* == @top (mor n n).
Proof. apply leq_tx_iff. apply str_ext. Qed.

(** transitivity of starred elements  *)
Lemma str_trans `{laws} `{STR<<l} n (x: X n n): x^* * x^* == x^*.
Proof. 
  apply antisym. apply str_ind_l; apply str_cons. 
  rewrite <-str_refl at 2. now rewrite dot1x. 
Qed.

(** [str] is involutive *)
Lemma str_invol `{laws} `{STR<<l} n (x: X n n): x^*^* == x^*.
Proof. apply antisym. apply str_ind_l1. apply str_refl. now rewrite str_trans. apply str_ext. Qed.

(** (de)nesting rule *)
Lemma str_pls `{laws} `{KA<<l} n (x y: X n n): (x+y)^* == x^**(y*x^*)^*.
Proof.
  apply str_unique.
   rewrite <-2str_refl. now rewrite dotx1.
   rewrite dotplsx. apply leq_cupx. 
    now rewrite dotA, str_cons.
    rewrite <-(str_refl x) at 3. now rewrite dot1x, dotA, str_cons.
   intros z Hz. rewrite dotplsx in Hz. apply cup_spec in Hz as [Hxz Hyz]. rewrite <-dotA. 
   apply str_ind_l'. 2: assumption. 
   apply str_ind_l. rewrite <- Hyz at 2. rewrite <-dotA. apply dot_leq. reflexivity. 
   now apply str_ind_l. 
Qed.

Lemma str_pls' `{laws} `{KA<<l} n (x y: X n n): (x+y)^* == (x^**y)^**x^*.
Proof. rewrite str_pls. apply str_dot. Qed.

Lemma str_pls_str `{laws} `{KA<<l} n (x y: X n n): (x+y)^* == (x^* + y^* )^* .
Proof.
  symmetry. rewrite str_pls, str_invol, <-str_pls. 
  rewrite cupC. now rewrite str_pls, str_invol, <-str_pls, cupC. 
Qed.

(** links with reflexive closure and reflexive elements *)
Lemma str_pls1x `{laws} `{KA<<l} n (x: X n n): (1+x)^* == x^*.
Proof. now rewrite str_pls, str1, dot1x, dotx1. Qed.

Lemma str_weq1 `{laws} `{KA<<l} n (x y: X n n): 1+x == 1+y -> x^* == y^*. 
Proof. rewrite <-(str_pls1x x), <-(str_pls1x y). apply str_weq. Qed.

Lemma str_dot_refl `{laws} `{KA<<l} n (x y: X n n): 1<==x -> 1<==y -> (x*y)^* == (x+y)^*.
Proof.
  intros Hx Hy. apply antisym.
  - apply str_ind_l1. apply str_refl.
    rewrite <-2str_cons at 2. rewrite dotA. repeat apply dot_leq; lattice.
  - apply str_ind_l1. apply str_refl.
    rewrite <-str_cons at 2. apply dot_leq. 2: reflexivity.
    apply leq_cupx. now rewrite <-Hy, dotx1. now rewrite <-Hx, dot1x.
Qed.


(** * counterparts for strict iteration *)

Lemma itr_ind_l `{laws} `{STR<<l} n m (x: X n n) (y z: X n m): x*y <== z -> x*z <== z -> x^+*y <== z.
Proof. intros xy xz. rewrite itr_str_r, <-dotA, xy. now apply str_ind_l. Qed.

Lemma itr_ind_l1 `{laws} `{STR<<l} n (x z: X n n): x <== z -> x*z <== z -> x^+ <== z.
Proof. intros xz xz'. rewrite <-dotx1. apply itr_ind_l. now rewrite dotx1. assumption. Qed.

Lemma itr_ind_r `{laws} `{STR<<l} n m (x: X n n) (y z: X m n): y*x <== z -> z*x <== z -> y*x^+ <== z.
Proof. dual @itr_ind_l. Qed.

Instance itr_leq `{laws} `{STR<<l} n: Proper (leq ==> leq) (itr n).
Proof. intros x y E. now rewrite 2itr_str_l, E. Qed.

Instance itr_weq `{laws} `{STR<<l} n: Proper (weq ==> weq) (itr n) := op_leq_weq_1.

Lemma itr1 `{laws} `{STR<<l} n: 1^+ == one n.
Proof. now rewrite itr_str_l, str1, dot1x. Qed.

Lemma itr0 `{laws} `{STR+BOT<<l} n: 0^+ == zer n n.
Proof. now rewrite itr_str_l, str0, dotx1. Qed.

Lemma itr_ext `{laws} `{STR<<l} n (x: X n n): x <== x^+.
Proof. now rewrite itr_str_l, <-str_refl, dotx1. Qed.

Lemma itrtop `{laws} `{STR+TOP<<l} n: top^+ == @top (mor n n).
Proof. apply leq_tx_iff. apply itr_ext. Qed.

Lemma itr_cons `{laws} `{STR<<l} n (x: X n n): x*x^+ <== x^+.
Proof. rewrite itr_str_l. now rewrite str_cons at 1. Qed.

Lemma itr_snoc `{laws} `{STR<<l} n (x: X n n): x^+*x <== x^+.
Proof. dual @itr_cons. Qed.

Lemma itr_pls_itr `{laws} `{KA<<l} n (x y: X n n): (x+y)^+ == (x^+ + y^+)^+.
Proof.
  apply antisym. apply itr_leq. now rewrite <-2itr_ext.
  apply itr_ind_l1. apply leq_cupx; apply itr_leq; lattice.
  rewrite dotplsx. apply leq_cupx; apply itr_ind_l; rewrite <-itr_cons at 2; apply dot_leq; lattice. 
Qed.

Lemma itr_trans `{laws} `{STR<<l} n (x: X n n): x^+ * x^+ <== x^+.
Proof. apply itr_ind_l; apply itr_cons. Qed.

Lemma itr_invol `{laws} `{STR<<l} n (x: X n n): x^+^+ == x^+.
Proof. apply antisym. apply itr_ind_l1. reflexivity. apply itr_trans. apply itr_ext. Qed.

Lemma itr_move `{laws} `{STR<<l} n m (x: X n m) y z:
  x * y == z * x  ->  x * y^+ == z^+ * x.
Proof. 
  intro E. rewrite itr_str_l, dotA, E, <-dotA, str_move by eassumption.
  now rewrite dotA, <-itr_str_l.
Qed.

Lemma itr_dot `{laws} `{STR<<l} n m (x: X n m) y: x*(y*x)^+ == (x*y)^+*x.
Proof. apply itr_move, dotA. Qed.


(** this lemma is used for KAT completeness *)
Lemma itr_aea `{laws} `{STR<<l} n (a e: X n n): a*a==a -> (a*e)^+*a == (a*e*a)^+.
Proof.
  intro Ha. rewrite (itr_str_l (a*e*a)), <-dotA, str_dot, (dotA a a), Ha. 
  now rewrite dotA, <-itr_str_l.
Qed.


(** * converse and iteration commute *)

Lemma cnvstr `{laws} `{CNV+STR<<l} n (x: X n n): x^*` == x`^*.
Proof. apply antisym. apply cnvstr_. cnv_switch. now rewrite cnvstr_, cnv_invol. Qed.

Lemma cnvitr `{laws} `{CNV+STR<<l} n (x: X n n): x^+` == x`^+.
Proof. now rewrite itr_str_l, itr_str_r, cnvdot, cnvstr. Qed.
