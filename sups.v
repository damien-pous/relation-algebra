(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * sups: finite joins (or supremums), a la ssreflect  *)

(** We define a few operations for manipulating finite supremums or
   intersections. We basically follow the scheme proposed for "bigops"
   in ssreflect, but we simplify it as much as possible since we do
   not need the whole machinery. The two main simplifications are:
   - the fact that we restrict ourselves to the associative,
     commutative, and idempotent operation [cup] of lattices
     (intersections being obtained by working in the dual lattices)
   - the fact that we do not include a "selection" operator *)

Require Import lset lattice.
Require Export ordinal.

Section s.
Context `{L:laws} `{Hl:BSL<<l}.

Section i.
Context {I: Type}.

(** * Supremums *)

(** the unique operator which we define is the following one, 
   which intuitively corresponds to [fold_right cup (map f J) bot],
   we redefine it to get a better behaviour with [simpl] *)

(** sup f [j1;...;jn] = f j1 \cup ... \cup f jn *)
Fixpoint sup (f: I -> X) J := 
  match J with
    | nil => bot
    | cons i J => f i \cup sup f J
  end.

(** sup specification *)
Lemma sup_spec f J x: sup f J <== x <-> forall i, In i J -> f i <== x.
Proof. 
  induction J; simpl. split. tauto. intro. lattice. 
  rewrite cup_spec, IHJ. clear IHJ. intuition. now subst. 
Qed.

(** ** basic facts about [sup] *)
Lemma sup_app f h k: sup f (h++k) == sup f h \cup sup f k.
Proof. induction h; simpl. lattice. rewrite IHh. hlattice. Qed.

Lemma sup_singleton f i: sup f (i::nil) == f i.
Proof. simpl. lattice. Qed.

Lemma leq_supx f J x: (forall i, In i J -> f i <== x) -> sup f J <== x.
Proof. apply sup_spec. Qed.

Lemma leq_xsup f J i: In i J -> f i <== sup f J.
Proof. now apply sup_spec. Qed.

Lemma leq_xsup' f J i x: In i J -> x <== f i -> x <== sup f J.
Proof. intros ? E. rewrite E. now apply leq_xsup. Qed.

(** [sup] is monotone, w.r.t, both the function [f] and the set [J] *)
Global Instance sup_leq: Proper (pwr leq ==> leq ==> leq) sup.
Proof.
  intros f f' Hf J J' HJ. induction J. apply leq_bx.
  simpl. apply leq_cupx. rewrite Hf. apply leq_xsup. apply HJ. now left. 
  apply IHJ. intros j ?. apply HJ. now right.
Qed.

Global Instance sup_weq: Proper (pwr weq ==> weq ==> weq) sup.
Proof. simpl. setoid_rewrite weq_spec. split; apply sup_leq; firstorder. Qed.

Lemma supcup f g J: sup (fun i => f i \cup g i) J == sup f J \cup sup g J.
Proof. induction J; simpl. lattice. rewrite IHJ. lattice. Qed.

(** refined monotonicity result: the functions have to be pointwise
   comparable only on the elements of [J] *)
Lemma sup_leq' J J' (f f': I -> X):
  J<==J' -> (forall i, In i J -> f i <== f' i) -> sup f J <== sup f' J'.
Proof. 
  induction J; intros HJ Hf. apply leq_bx. 
  simpl. apply leq_cupx. 
  rewrite Hf. apply leq_xsup. apply HJ. now left. now left.
  apply IHJ. rewrite <- HJ. clear; firstorder. clear -Hf; firstorder. 
Qed.

Lemma sup_weq' J J' (f f': I -> X):
  J==J' -> (forall i, In i J -> f i == f' i) -> sup f J == sup f' J'.
Proof. setoid_rewrite weq_spec. split; apply sup_leq'; firstorder. Qed.

(** the sup of empty elements is still empty *)
Lemma sup_b J (f: I -> X) (Hf: forall i, In i J -> f i == bot): sup f J == bot.  
Proof.
  apply antisym. 2: apply leq_bx. 
  apply leq_supx. intros. now rewrite Hf. 
Qed.

End i.

(** ** swapping and reindexing indices *)

Theorem sup_swap I J (f: I -> J -> X) I' J':
  sup (fun i => sup (fun j => f i j) J') I' ==
  sup (fun j => sup (fun i => f i j) I') J'.
Proof.
  induction I'; simpl. apply antisym. apply leq_bx. apply leq_supx; trivial.
  now rewrite IHI', supcup. 
Qed.

Lemma sup_map I J (f: J -> X) (m: I -> J) I':
  sup f (map m I') = sup (fun i => f (m i)) I'.
Proof. induction I'; simpl; congruence. Qed.

End s.

(** ** notations *)

(** we use "\sup_(i\in l) f" in the general case *)
Notation "\sup_ ( i \in l ) f" := (sup (fun i => f) l)
  (at level 41, f at level 41, i, l at level 50,
    format "'[' \sup_ ( i \in  l ) '/  '  f ']'"): ra_terms.

(** and "\sup_(i<n) f" when [l] is the set of ordinals smaller than [n] *)
Notation "\sup_ ( i < n ) f" := (\sup_(i \in seq n) f)
  (at level 41, f at level 41, i, n at level 50,
    format "'[' \sup_ ( i < n ) '/  '  f ']'"): ra_terms.

(** we shall moreover use the notation [\sum] when the lattice
   operations actually come from a partially ordered monoid (see sum.v) *)


(** ** additional properties *)

(** two "meta" results, to prove that some operation commutes with supremums *)

Lemma f_sup_weq {X: ops} {Y l} {L: laws l Y} `{Hl: CUP<<l} (f: X -> Y):
  (f bot == bot) ->
  (forall x y, f (x\cup y) == f x \cup f y) ->
  forall I J (g: I -> X), f (sup g J) == \sup_(i\in J) f (g i).
Proof.
  intros Hbot Hcup I J g. induction J. apply Hbot. 
  simpl. rewrite Hcup. now apply cup_weq.
Qed.

Lemma f_sup_eq {X Y: ops} (f: X -> Y):
  (f bot = bot) ->
  (forall x y, f (x\cup y) = f x \cup f y) ->
  forall I J (g: I -> X), f (sup g J) = \sup_(i\in J) f (g i).
Proof.
  intros Hbot Hcup I J g. induction J. apply Hbot.
  simpl. rewrite Hcup. congruence.
Qed.

(** same thing, to prove that a predicate is preserved under supremums *)

Lemma P_sup {X: ops} {P: X -> Prop} I J (f: I -> X):
  P bot -> 
  (forall x y, P x -> P y -> P (x \cup y)) ->
  (forall i, In i J -> P (f i)) -> 
  P (sup f J).
Proof.
  intros Hbot Hcup.
  induction J; intro H; simpl. apply Hbot. 
  apply Hcup. apply H; now left. apply IHJ. intros. apply H. now right. 
Qed.



(** cutting a supremum over ordinals of size [n+m] *)
Lemma sup_cut `{L:laws} `{BSL<<l} n m f:
  \sup_(i<n+m) f i == \sup_(i<n) f (lshift i) \cup \sup_(i<m) f (rshift i).
Proof. now rewrite seq_cut, sup_app, 2sup_map. Qed.

(** supremums where the indices come from a supremum *)
Lemma sup_sup `{L: laws} `{BSL<<l} I (f: I -> X) A (J: A -> list I) h: 
  sup f (sup J h) == sup (fun a => sup f (J a)) h.
Proof. induction h. reflexivity. simpl. now rewrite sup_app, IHh. Qed.

(** belonging to a finite union *)
Lemma in_sup A I J (f: I -> list A) a: In a (sup f J) <-> exists i, In i J /\ In a (f i).
Proof.
  induction J; simpl. firstorder. 
  rewrite in_app_iff, IHJ. clear. firstorder congruence. 
Qed.

(** link between [map] and [sup] *)
Lemma map_sup A I J (f: I -> A): map f J = \sup_(i\in J) [f i].
Proof. induction J; simpl; congruence. Qed.


(** distribution of meets over supremums *)
Lemma capxsup `{laws} `{BSL+CAP<<l} I J (f: I -> X) (x: X): 
  x \cap (\sup_(i\in J) f i) == \sup_(i\in J) (x \cap f i).
Proof. apply f_sup_weq. apply capxb. intros; apply capcup. Qed.

Lemma capsupx `{laws} `{BSL+CAP<<l} I J (f: I -> X) (x: X): 
  (\sup_(i\in J) f i) \cap x == \sup_(i\in J) (f i \cap x).
Proof. rewrite capC, capxsup. now setoid_rewrite capC at 1. Qed.


(** * Infimum (or intersections) *)

(** obtained for free, by duality *)

Notation inf f l := (@sup (dual _) _ f l).

Notation "\inf_ ( i \in l ) f" := (inf (fun i => f) l)
  (at level 41, f at level 41, i, l at level 50,
    format "'[' \inf_ ( i \in  l ) '/  '  f ']'"): ra_terms.

Notation "\inf_ ( i < n ) f" := (\inf_(i \in seq n) f)
  (at level 41, f at level 41, i, n at level 50,
    format "'[' \inf_ ( i < n ) '/  '  f ']'"): ra_terms.

Section inf.
Context `{laws} `{CAP+TOP<<l} {I: Type}.

Global Instance inf_leq:
  Proper (pwr (@leq X) ==> leq --> @leq X) (@sup (dual X) I).
Proof. intros ? ? ? ? ?. now dual @sup_leq. Qed.

Lemma inf_spec (f: I -> X) J (x: X): 
  x <== \inf_(i\in J) f i <-> forall i, In i J -> x <== f i.
Proof. dual @sup_spec. Qed.

Lemma inf_singleton (f: I -> X) i: inf f (i::nil) == f i.
Proof. dual @sup_singleton. Qed.

Lemma leq_xinf (f: I -> X) J x: (forall i, In i J -> x <== f i) -> x <== inf f J.
Proof. dual @leq_supx. Qed.

Lemma leq_infx (f: I -> X) J i: In i J -> @leq X (inf f J) (f i).
Proof. dual @leq_xsup. Qed.

Lemma leq_infx' (f: I -> X) J i x: In i J -> f i <== x -> @leq X (inf f J) x.
Proof. dual @leq_xsup'. Qed.

End inf.

