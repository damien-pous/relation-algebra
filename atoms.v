(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * atoms: atoms of the free Boolean lattice over a finite set  *)

(** An atom is an expression that cannot be decomposed into a
   non-trivial disjunction.  When the set of variables is finite, the
   atoms are the complete conjunctions of literals, and any expression
   can be decomposed as a sum of atoms, in a unique way. 

   We work with ordinals to get the finiteness property for free: the
   set of variables is [ord n], for some natural number [n]. 
   Atoms are in bijection with [ord n -> bool], and thus, [ord (pow2 n)]. *)

Require Import lattice lsyntax comparisons lset boolean sups.
Set Implicit Arguments.

(** Atom corresponding to a subset of variables, encoded as an ordinal *)
Definition atom {n} (f: ord (pow2 n)): expr_ops (ord n) BL := 
  sup (X:=dual (expr_ops _ BL))
  (fun i => if set.mem f i then e_var i else ! e_var i) (seq n). 


(** * Decomposition of the [top] element into atoms  *)

(** Alternative definition of the [top] element, as the sum of all atoms 
   the first step consists in proving that this is actaully the [top] element. *)

Definition e_top' n: expr_ BL := \sup_(a<pow2 n) atom a.

(** auxiliary lemmas about the set of ordinals coding for a subset: if
   there is at least one variable, it can be partioned into to sets,
   those which assign [true] to that variable, and those which assign
   [false] to it *)
Lemma seq_double n: seq (double n) == map (@set.xO _) (seq n) ++ map (@set.xI _) (seq n).
Proof.
  induction n. reflexivity. 
  simpl double. simpl seq. fold_cons.
  rewrite IHn. simpl map.
  rewrite 2map_app. rewrite 6map_map. 
  rewrite set.xO_0, set.xI_0.
  setoid_rewrite set.xO_S. 
  setoid_rewrite set.xI_S.
  refine (comm4 [_] [_] _ _).
Qed.

Lemma atom_xO n (f: ord (pow2 n)): 
  @atom (S n) (set.xO f) == ! e_var ord0 \cap eval (fun i => e_var (ordS i)) (atom f).
Proof.
  unfold atom. simpl. rewrite set.mem_xO_0. apply cap_weq. reflexivity.
  setoid_rewrite eval_inf. rewrite sup_map.
  apply (sup_weq (l:=BL) (L:=lattice.dual_laws _ _ _)). 2: reflexivity. intro i.
  rewrite set.mem_xO_S. now case set.mem. 
Qed.

Lemma atom_xI n (f: ord (pow2 n)): 
  @atom (S n) (set.xI f) == e_var ord0 \cap eval (fun i => e_var (ordS i)) (atom f).
Proof.
  unfold atom. simpl. rewrite set.mem_xI_0. apply cap_weq. reflexivity.
  setoid_rewrite eval_inf. rewrite sup_map.
  apply (sup_weq (l:=BL) (L:=lattice.dual_laws _ _ _)). 2: reflexivity. intro i.
  rewrite set.mem_xI_S. now case set.mem. 
Qed.
  
(** the deomposition of [top] into atoms follow by induction *)
Theorem decomp_top n: top == e_top' n.
Proof.
  unfold e_top'. induction n. symmetry. apply cupxb. 
  simpl pow2. rewrite seq_double, sup_app.
  rewrite 2sup_map. setoid_rewrite atom_xO. setoid_rewrite atom_xI. 
  rewrite <- 2capxsup. rewrite capC, (capC (e_var _)), <- capcup. 
  rewrite cupC, cupneg, capxt. 
  intros X L f. simpl. rewrite (IHn X L (fun i => f (ordS i))).
  rewrite 2eval_sup. apply sup_weq. 2: reflexivity. intro i.
  induction (atom i); first [reflexivity|apply cup_weq|apply cap_weq|apply neg_weq]; assumption. 
Qed.


(** * Decomposition of the other expressions into atoms  *)

Section atom_props.
Variable n: nat.
Notation Atom := (ord (pow2 n)).

(** auxiliary lemmas *)
Lemma cap_var_atom (a: Atom) b: 
  e_var b \cap atom a == (if set.mem a b then atom a else bot).
Proof. 
  generalize (in_seq b). unfold atom. induction (seq n). intros []. 
  simpl (sup _ _). intros [->|Hl]. 
   case set.mem. lattice. rewrite capA, capneg. apply capbx. 
  rewrite capA, (capC (e_var _)), <-capA, IHl by assumption.
  case (set.mem a b). reflexivity. apply capxb. 
Qed.

Lemma cup_var_atom (a: Atom) b: 
  e_var b \cup !atom a == (if set.mem a b then top else !atom a).
Proof. 
  generalize (in_seq b). unfold atom. induction (seq n). intros []. 
  simpl (sup _ _). intros [->|Hl]. 
   case set.mem. rewrite negcap, cupA, cupneg. apply cuptx. 
   rewrite negcap, negneg. lattice.
  rewrite negcap at 1. rewrite cupA, (cupC (e_var _)), <-cupA, IHl by assumption.
  case (set.mem a b). apply cupxt. now rewrite negcap.
Qed.

Lemma eval_mem_cap (a: Atom) e: e\cap atom a == if eval (set.mem a) e then atom a else bot
with eval_mem_cup (a: Atom) e: e\cup !atom a == if eval (set.mem a) e then top else !atom a.
Proof.
- destruct e; simpl eval.
   apply capbx.  
   apply captx. 
   rewrite capC, capcup, capC, eval_mem_cap, capC, eval_mem_cap.
    case (eval (set.mem a) e1); case (eval (set.mem a) e2); lattice.
   transitivity ((e1\cap atom a)\cap (e2\cap atom a)). lattice. rewrite 2eval_mem_cap. 
    case (eval (set.mem a) e1); case (eval (set.mem a) e2); lattice.
   neg_switch. rewrite negcap, negneg, eval_mem_cup. 
    case (eval (set.mem a) e). now rewrite <-negbot. reflexivity. 
   apply cap_var_atom.
- destruct e; simpl eval.
   apply cupbx.  
   apply cuptx. 
   transitivity ((e1\cup !atom a)\cup (e2\cup !atom a)). lattice. rewrite 2eval_mem_cup. 
    case (eval (set.mem a) e1); case (eval (set.mem a) e2); lattice.
   rewrite cupC, cupcap, cupC, eval_mem_cup, cupC, eval_mem_cup.
    case (eval (set.mem a) e1); case (eval (set.mem a) e2); lattice.
   neg_switch. rewrite negcup, 2negneg, eval_mem_cap. 
    case (eval (set.mem a) e). apply negneg. apply negtop.
   apply cup_var_atom. 
Qed.

(** decomposition of arbitrary expressions *)
Theorem decomp_expr e: 
  e ==_[BL] \sup_(i \in filter (fun f => eval (set.mem f) e) (seq (pow2 n))) atom i.
Proof.
  rewrite <-capxt. setoid_rewrite decomp_top. setoid_rewrite capxsup. 
  setoid_rewrite eval_mem_cap. 
  induction (seq (pow2 n)). reflexivity. simpl filter. simpl (sup _ _).
  case (eval (set.mem a) e). now apply cup_weq. now rewrite cupbx. 
Qed.

(** * Atoms are pairwise disjoint *)

Lemma eval_atom (a b: Atom): eval (set.mem a) (atom b) -> a=b. 
Proof.
  intro. apply set.ext. intro i. 
  unfold atom in H. setoid_rewrite eval_inf in H. 
  rewrite is_true_inf in H. specialize (H i (in_seq i)). 
  destruct (set.mem b i). assumption. apply Bool.negb_true_iff. assumption. 
Qed.

Lemma empty_atom_cap (a b: Atom): a<>b -> atom a \cap atom b == bot.
Proof.
  intro E. rewrite eval_mem_cap. generalize (eval_atom b a). 
  case (eval (set.mem b) (atom a)). 2: reflexivity. 
  intro. elim E. symmetry; auto. 
Qed.

End atom_props.
