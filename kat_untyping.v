(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * kat_untyping: untyping theorem for KAT *)

(** We prove a strong untyping theorem for KAT: 
   - types can be erased (as in the untyping theorem in [untyping])
   - predicate variables of distinct types can be merged

   The proofs are quite simple since we can perform them at the level
   of guarded string languages: unlike for KA, we proved typed
   completeness of KAT w.r.t. these models. *)

Require Import kat gregex ugregex ordinal positives glang.
Set Implicit Arguments.

Section s.
Variable Pred: nat.
Notation Atom := (ord (pow2 Pred)).
Notation Sigma := positive.
Variables src tgt: Sigma -> positive.
Notation pred := (ord Pred).
Notation gregex := (gregex_kat_ops Pred src tgt).
Notation ugregex := (ugregex_monoid_ops Pred ugregex_tt ugregex_tt).
Notation glang := (@gregex.lang Pred src tgt).
Notation uglang := (@ugregex.lang Pred).
Notation typed := (@typed' Atom src tgt).

(** type-erasing function on extended regular expressions *)

Fixpoint gerase n m (e: gregex n m): ugregex :=
  match e with
    | g_zer _ _ _ => 0
    | g_prd _ _ p => u_prd p
    | g_pls e f => gerase e + gerase f
    | g_dot e f => gerase e * gerase f
    | g_itr e => gerase e ^+
    | g_var i => u_var _ i
  end.

(** charaterisation of the guarded string language of erased epressions *)

Lemma uglang_gerase n m (e: gregex n m): 
  uglang (gerase e) == eval (fun _ => traces_tt) (fun _ => @lsyntax.e_var _) tsingle e.
Proof. 
  induction e; simpl gerase. 
   apply lang_0. 
   simpl. rewrite lsyntax.eval_var. reflexivity. 
   reflexivity. 
   now apply cup_weq.
   now apply dot_weq.
   now apply itr_weq.
Qed.

Corollary gerase_weq n m: Proper (weq ==> weq) (@gerase n m).
Proof. intros ? ? H. simpl. unfold u_weq. rewrite 2uglang_gerase. apply (H _ _ _). Qed.


(** the a priori untyped guarded string language of a typed gregex is necessarily typed *)

Lemma typed_uglang_gerase n m (e: gregex n m): typed n m (uglang (gerase e)).
Proof.
  induction e. 
   intros [|] H. discriminate. destruct H.
   apply typed'_inj.
   apply typed'_single.
   revert IHe1 IHe2. apply typed'_cup.
   revert IHe1 IHe2. apply typed'_dot.
   revert IHe. apply typed'_itr.
Qed.


(** we can thus recover the typed language out of the untyped one *)

Notation restrict := (restrict src tgt).

Theorem untype_glang n m (e: gregex n m): glang e == restrict n m (uglang (gerase e)).
Proof.
  symmetry. induction e.
   setoid_rewrite lang_0. apply restrict_0.
   setoid_rewrite restrict_inj. simpl. unfold ttraces_weq. simpl. now rewrite lsyntax.eval_var. 
   apply restrict_single.
   etransitivity. 2: apply cup_weq; eassumption. apply restrict_pls. 
   etransitivity. 2: apply dot_weq; eassumption. apply restrict_dot; apply typed_uglang_gerase. 
   etransitivity. 2: apply itr_weq; eassumption. apply restrict_itr; apply typed_uglang_gerase. 
Qed.

End s.
