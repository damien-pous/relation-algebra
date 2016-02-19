(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * lang: the (flat) model of languages of finite words *)

Require Import List.
Require Export prop.
Require Import monoid.

(** singleton type for the objects of this flat structure *)
CoInductive lang_unit := lang_tt.

Section l.

Variable X: Type.

(** a language on [X] is a predicate on finite words with letters in [X] *)
Definition lang := list X -> Prop.
Implicit Types x y z: lang.
Implicit Types n m p q: lang_unit.
Notation tt := lang_tt.

(** * Languages as a lattice *)

(** lattice operations and laws are obtained for free, by pointwise
   lifting of the [Prop] lattice *)

Canonical Structure lang_lattice_ops := 
  lattice.mk_ops lang leq weq cup cap neg bot top.

Global Instance lang_lattice_laws: 
  lattice.laws (BDL+STR+DIV) lang_lattice_ops := lower_lattice_laws (H:=pw_laws _). 

(** * Languages a residuated Kleene lattice *)

(** ** language operations *)

(** language concatenation *)
Definition lang_dot n m p x y: lang := fun w => exists2 u, x u & exists2 v, y v & w=u++v.

(** languages left and right residuals *)
Definition lang_ldv n m p x y: lang := fun w => forall u, x u -> y (u++w).
Definition lang_rdv n m p x y: lang := fun w => forall u, x u -> y (w++u).

(** language reduced to the empty word *)
Definition lang_one n: lang := eq nil.

(** language of reversed words *)
Definition lang_cnv n m x: lang := fun w => x (rev w).

(** finite iterations of a language (with a slight generalisation: [y*x^n]) *)
Fixpoint iter i y x: lang := 
  match i with O => y | S i => lang_dot tt tt tt x (iter i y x) end.

(** strict iteration: union of finite iterations, starting with [x]  *)
Definition lang_itr n x: lang := fun w => exists i, iter i x x w.

(** Kleene star: union of finite iterations, starting with [1]  *)
Definition lang_str n x: lang := fun w => exists i, iter i (lang_one n) x w.

(** packing all operations in a canonical structure *)
Canonical Structure lang_ops := 
  mk_ops lang_unit _ lang_dot lang_one lang_itr lang_str lang_cnv lang_ldv lang_rdv.

(** shorthand for [lang], when a morphism is expected *)
Notation lang' := (lang_ops tt tt).


(** ** languages form a residuated Kleene lattice *)

(** auxiliary lemmas, to establish that languages form a residuated Kleene lattice *)
Lemma lang_dotA n m p q x y z: 
  lang_dot n m q x (lang_dot m p q y z) == lang_dot n p q (lang_dot n m p x y) z.
Proof.
  intro w. split. 
  intros [u Hu [v [u' Hu' [v' Hv' ->]] ->]]. repeat eexists; eauto. apply ass_app.
  intros [u [u' Hu' [v' Hv' ->]] [v Hv ->]]. repeat eexists; eauto. apply app_ass.
Qed.

Lemma lang_dotx1 x: lang_dot tt tt tt x (lang_one tt) == x.
Proof.
  intro w. split. 
   intros [u Hu [v <- ->]]. now rewrite <-app_nil_end. 
   intro Hw. exists w; trivial. exists nil.  reflexivity. apply app_nil_end.
Qed.

Lemma lang_dot_leq n m p: Proper (leq ==> leq ==> leq) (lang_dot n m p).
Proof.
  intros x y H x' y' H' w [u Hu [v Hv Hw]]. 
  exists u. apply H, Hu. exists v. apply H', Hv. assumption.
Qed.

Lemma lang_iter_S i x: iter i x x == iter (S i) (lang_one tt) x.
Proof. 
  induction i; simpl iter. symmetry. apply lang_dotx1. 
  now apply (op_leq_weq_2 (Hf:=@lang_dot_leq _ _ _)).
Qed.

(** languages form a residuated Kleene lattice 
   (we do not have an allegory, since the converse operation does not
   satisfy the law [x<==x*x`*x]) *)
Global Instance lang_laws: laws (BDL+STR+DIV) lang_ops.
Proof.
  constructor; (try (intro; discriminate)); (try now left); repeat right; intros. 
   apply lower_lattice_laws.
   apply lang_dotA.
   intro w. split. 
    now intros [u <- [v Hv ->]].
    intro Hw. exists nil. reflexivity. now exists w.
   apply lang_dotx1.
   intros w Hw. now exists O.
   intros w [u Hu [v [i Hi] ->]]. exists (S i). repeat eexists; eauto.
   intros w [u [i Hu] [v Hv ->]]. revert u Hu. induction i. 
    now intros u <-.
    intros u [u' Hu' [u'' Hu'' ->]]. apply H0. rewrite app_ass. eexists; eauto. 
   intro w. split. 
    intros [i H']. apply lang_iter_S in H' as [? ? [? ? ?]]. repeat eexists; eauto.
    intros [? ? [? [i H'] ?]]. exists i. apply lang_iter_S. repeat eexists; eauto.
   split; intros E w. intros [u xu [v xv ->]]. now apply E. 
    intros Hw u Hu. apply E. repeat eexists; eauto.
   split; intros E w. intros [u xu [v xv ->]]. now apply E. 
    intros Hw u Hu. apply E. repeat eexists; eauto.
Qed.

(** empty word property for concatenated languages *)
Lemma lang_dot_nil (L L': lang'): (L*L')%ra nil <-> L nil /\ L' nil.
Proof. 
  split. 2:firstorder. intros [h H [k K E]].
  apply eq_sym, List.app_eq_nil in E. intuition congruence.
Qed.

(** concatenation of singleton languages *)
Lemma eq_app_dot u v: eq (u++v) == (eq u: lang') * (eq v: lang').
Proof. split. intros <-. repeat eexists; eauto. now intros [? <- [? <- <-]]. Qed.


(** * Language derivatives *)

Definition lang_deriv a (L: lang'): lang' := fun w => L (a::w). 

Lemma lang_deriv_0 a: lang_deriv a 0 == 0. 
Proof. firstorder. Qed.

Lemma lang_deriv_1 a: lang_deriv a 1 == 0. 
Proof. compute. intuition discriminate. Qed.

Lemma lang_deriv_pls a (H K: lang'): 
  lang_deriv a (H+K) == lang_deriv a H + lang_deriv a K.
Proof. intro. now apply cup_weq. Qed.

Lemma lang_deriv_dot_1 a (H K: lang'): H nil ->
  lang_deriv a (H*K) == lang_deriv a H * K + lang_deriv a K.
Proof.
  intros Hnil w; simpl; unfold lang_deriv, lang_dot.
   split. 
    intros [[|b u] Hu [v Kv E]]; simpl in E. 
     right. now rewrite E.
     injection E; intros -> <-; clear E. left. repeat eexists; eauto. 
    intros [[u Hu [v Kv ->]]|Ka]; repeat eexists; eauto. 
Qed.

Lemma lang_deriv_dot_2 a (H K: lang'): ~ (H nil) ->
  lang_deriv a (H*K) == lang_deriv a H * K.
Proof.
  intros Hnil w; simpl; unfold lang_deriv, lang_dot.
   split. 
    intros [[|b u] Hu [v Kv E]]; simpl in E. 
     tauto. 
     injection E; intros -> <-; clear E. repeat eexists; eauto. 
    intros [u Hu [v Kv ->]]; repeat eexists; eauto. 
Qed.

Lemma lang_deriv_str a (H: lang'): 
  lang_deriv a (H^*) == lang_deriv a H * H^*.
Proof.
  intro w. split. 
  intros [n Hn]. induction n in a, w, Hn; simpl in Hn. 
   discriminate. 
   destruct Hn as [[|b v] Hv [u Hu Hw]]; simpl in Hw.
    rewrite <- Hw in Hu. apply IHn, Hu. 
    injection Hw; intros -> ->; clear Hw. repeat eexists; eauto.
  intros [u Hu [v [n Hv] ->]]. exists (S n). repeat eexists; eauto.
Qed.

End l.

Implicit Arguments lang_deriv [[X]].
Notation lang' X := ((lang_ops X) lang_tt lang_tt).

Ltac fold_lang := ra_fold lang_ops lang_tt.
