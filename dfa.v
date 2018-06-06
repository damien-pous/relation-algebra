(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * dfa: Deterministic Finite Automata, decidability of language inclusion *)

Require Import comparisons positives ordinal pair lset.
Require Import monoid boolean prop sups bmx.
Set Implicit Arguments.
Unset Printing Implicit Defensive.

(** * DFA and associated language *)

(** A DFA is given by its number of states, a deterministic transition
   function, an acceptance condition, and a finite subset of the
   alphabet.

   States are represented by ordinals of the appropriate size.  

   Making the finite subset of the alphabet explicit avoids us to use
   ordinals for the alphabet. *)

Record t := mk {
  n: nat;
  u: ord n;
  M: ord n -> positive -> ord n;
  v: ord n -> bool;
  vars: list positive
}.
Notation "x ^u" := (u x) (at level 2, left associativity, format "x ^u").
Notation "x ^M" := (M x) (at level 2, left associativity, format "x ^M").
Notation "x ^v" := (v x) (at level 2, left associativity, format "x ^v").

(** changing the initial state *)
Definition reroot A i := mk i A^M A^v (vars A).

Lemma reroot_id A: A = reroot A (A^u).
Proof. destruct A; reflexivity. Qed.

(** language of a DFA [A], starting from state [i] *)
Fixpoint lang A i w := 
  match w with 
    | nil => is_true (A^v i)
    | cons a w => In a (vars A) /\ lang A (A^M i a) w
  end.


(** * Reduction of DFA language inclusion to DFA language emptiness  *)

Section diff.

Variables A B: t.

(** automaton for [A\B] *)
Definition diff := mk 
  (pair.mk (u A) (u B))
  (fun p a => pair.mk (M A (pair.pi1 p) a) (M B (pair.pi2 p) a))
  (fun p => v A (pair.pi1 p) \cap ! v B (pair.pi2 p))
  (vars A).

(** specification of its language *)
Lemma diff_spec: vars A <== vars B -> 
  forall i j, lang A i <== lang B j <-> lang diff (pair.mk i j) <== bot. 
Proof.
  intro H. 
  cut (forall w i j, lang A i w <== lang B j w <-> ~ lang diff (pair.mk i j) w).
   intros G i j. split. intros Hij w Hw. apply G in Hw as []. apply Hij.
   intros Hij w. apply G. intro Hw. elim (Hij _ Hw).  
  induction w; intros i j; simpl lang; rewrite pair.pi1mk, pair.pi2mk. 
   case (v A i); case (v B j); firstorder discriminate.
    split. intros Hij [HaB Hw]. apply IHw in Hw as []. intro Aw. apply Hij. now split.
    intros Hw [Ha Aw]. split. apply H, Ha. eapply IHw. 2: eassumption. tauto. 
Qed.

End diff.


(** * Decidability of DFA language emptiness 

   We proceed as follows: 
   1. we forget all transition labels to get a directed graph whose
      nodes have an accepting status.
   2. we compute the reflexive and transitive closure of this graph
   3. we deduce the set of all states reachable from the initial state.
   4. the DFA is empty iff this set does not contain any accepting
      states. 

   All these computations are straightforward, except for 2, for which
   we exploit Kleene star on Boolean matrices.

   The resulting algorithm is not efficient at all. We don't care
   because this is not the one we execute in the end: this one is just
   used to establish KA completeness. *)

Section empty_dec.

Variables A: t.

(** erased transition graph, represented as a Boolean matrix *)
Definition step: bmx (n A) (n A) := fun i j => \sup_(a\in vars A) eqb_ord (M A i a) j.

(** reflexive transitive closure of this graph *)
Definition steps := (@str bmx _ step). 

Variable i: ord (n A).

(** basic properties of this closed graph *)
Lemma steps_refl: steps i i.
Proof. apply bmx_str_clot. constructor. Qed.

Lemma steps_snoc: forall j a, steps i j -> In a (vars A) -> steps i (M A j a).
Proof. 
  setoid_rewrite bmx_str_clot. intros. eapply clot_snoc. eassumption. 
  setoid_rewrite is_true_sup. eexists. split. eassumption. apply eqb_refl. 
Qed.

(** state reached from [i] by following a word [w] in the DFA *)
Fixpoint Ms i w := match w with nil => i | cons a w => Ms (M A i a) w end.

(** each unlabelled path in the erased graph corresponds to a labelled
   path (word) in the DFA *)
Lemma steps_least: forall j, steps i j -> exists w, w <== vars A /\ j = Ms i w. 
Proof.
  intros j H. apply bmx_str_clot in H. induction H as [i|i j k Hij _ [w [Hw ->]]]. 
   exists nil. split. lattice. reflexivity.
  setoid_rewrite is_true_sup in Hij. destruct Hij as [a [Ha Hij]]. 
  exists (a::w). split. intros b [<-|Hb]. assumption. now apply Hw. 
  revert Hij. case eqb_ord_spec. 2: discriminate. now intros <-. 
Qed.

(** can we reach an accepting state from [i] *)
Definition empty := \inf_(j<_) (steps i j <<< !v A j).

(* TODO: les deux lemmes suivants sont certainement simplifiables en
   prouvant directement l'équivalence *)

(** if not, all states reachable from [i] map to the empty language *)
Lemma empty_lang1 j: steps i j -> empty -> lang A j <== bot.
Proof.
  intros Hj He. setoid_rewrite is_true_inf in He. setoid_rewrite le_bool_spec in He. 
  pose proof (fun i => He i (ordinal.in_seq _)) as H. clear He. 
  intro w. revert j Hj. induction w as [|a w IH]; simpl lang; intros j Hj. 
  apply (H j), negb_spec in Hj. rewrite Hj. discriminate. 
  intros [Ha Hj']. apply IH in Hj' as []. now apply steps_snoc.
Qed.

(** conversely, if [i] maps to them empty language, then there is no
   reachable accepting state *)
Lemma empty_lang2: lang A i <== bot -> empty.
Proof.
  intro H. setoid_rewrite is_true_inf. intros j _. 
  rewrite le_bool_spec. intro Hj. apply steps_least in Hj as [w [Hw ->]].
  generalize i (H w) Hw. clear. induction w; intros i Hi Hw. 
   simpl in *. destruct (v A i). now elim Hi. reflexivity. 
   apply IHw. intro H. elim Hi. split. apply Hw. now left. assumption. 
   intros ? ?. apply Hw. now right. 
Qed.

(** decidability of language emptiness follows *)
Theorem empty_dec: {lang A i <== bot} + {~ (lang A i <== bot)}.
Proof.
  case_eq empty; [left|right]. 
   apply (empty_lang1 _ steps_refl H). 
  intro E. apply empty_lang2 in E. rewrite H in E. discriminate. 
Qed.

End empty_dec.


(** * Decidability of DFA language inclusion *)

Corollary lang_incl_dec A B: vars A <== vars B -> 
  forall i j, {lang A i <== lang B j} + {~(lang A i <== lang B j)}.
Proof. intros. eapply sumbool_iff. symmetry. now apply diff_spec. apply empty_dec. Qed.
