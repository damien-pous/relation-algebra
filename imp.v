(************************************************************************)
(*    This is part of RelationAlgebra, it is distributed under the      *)
(*      terms of the GNU Lesser General Public License version 3        *)
(*                (see file LICENSE for more details)                   *)
(*                                                                      *)
(*  Copyright 2012-2013: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(************************************************************************)

(** * imp: a formalisation of the IMP programming language on top of KAT *)

(* We formalise the IMP language (whose programs are also known as
   "while programs"). We give a big step semantics as an inductive
   predicate, and using KAT, and we show that the two versions
   actually coincide.
   
   We then use the [kat] tactic to prove some simple program
   equivalences, and to derive all rules of corresponding Hoare logic
   for partial correctness. *)

Require Import kat prop rel comparisons kat_tac.

Section s.
(** identifiers for memory locations  *)
Variable loc: Set.
(** abstract state (or memory) *)
Variable state: Set.
(** updating the state *)
Variable update: loc -> nat -> state -> state.

(** * Definition of the languague *)

(** programs *)

Inductive prog :=
| skp
| aff (x: loc) (e: state -> nat)
| seq (p q: prog)
| ite (t: dset state) (p q: prog)
| whl (t: dset state) (p: prog).

(** notations *)
Bind Scope imp_scope with prog.
Delimit Scope imp_scope with imp.
Notation "x  <- y" := (aff x y) (at level 90): imp_scope.
Notation "p  ;; q" := (seq p%imp q%imp) (left associativity, at level 101): imp_scope.
Arguments ite _%ra _%imp _%imp.
Arguments whl _%ra _%imp.


(** * Big step semantics *)

(** corresponding functional relation *)
Notation upd x e := (frel (fun s => update x (e s) s)).


(** ** using KAT expressions in the model of relations

   the semantics can then be given by induction on the program, using
   a simple fixpoint *)

Fixpoint bstep (p: prog): rel state state :=
  match p with
    | skp => 1
    | aff x e => upd x e
    | seq p q => bstep p * bstep q
    | ite b p q => [b] * bstep p + [!b] * bstep q
    | whl b p => ([b] * bstep p)^*  *  [!b]
  end.

(** ** using an inductive predicate, as in standard textbooks *)

Inductive bstep': prog -> rel state state :=
| s_skp: forall s, bstep' skp s s
| s_aff: forall x e s, bstep' (x <- e) s (update x (e s) s)
| s_seq: forall p q s s' s'', bstep' p s s' -> bstep' q s' s'' -> bstep' (p ;; q) s s''
| s_ite_ff: forall (b: dset state) p q s s', b s = false -> bstep' q s s' -> bstep' (ite b p q) s s'
| s_ite_tt: forall (b: dset state) p q s s', b s = true -> bstep' p s s' -> bstep' (ite b p q) s s'
| s_whl_ff: forall (b: dset state) p s, b s = false -> bstep' (whl b p) s s
| s_whl_tt: forall (b: dset state) p s s', b s = true -> bstep' (p ;; whl b p) s s' -> bstep' (whl b p) s s'.

(** ** equivalence between the two definitions *)

Lemma bstep_eq p: bstep' p == bstep p.
Proof.
  apply antisym. 
  - intros s s'. induction 1. 
     reflexivity. 
     reflexivity. 
     eexists; eassumption. 
     right. eexists. split. reflexivity. simpl; now rewrite H. assumption.
     left. eexists. split. reflexivity. assumption. assumption. 
     exists s. apply (str_refl ([b] * bstep p)). reflexivity.
      simpl. unfold rel_inj. simpl. now rewrite H.
     destruct IHbstep' as [t ? [t' ? ?]]. exists t'. 2: assumption. 
     apply (str_cons ([b] * bstep p)). exists t. 2: assumption.
     eexists; eauto. now split. 
  - induction p; unfold bstep; fold bstep.
     intros ? ? <-. constructor. 
     intros ? ? ->. constructor. 
     intros ? ? [? H1 H2]. econstructor. apply IHp1, H1. apply IHp2, H2.
     intros ? ? [[? [<- H] H']|[? [<- H] H']]. 
      apply s_ite_tt. assumption. apply IHp1, H'. 
      apply s_ite_ff. now apply Bool.negb_true_iff. apply IHp2, H'. 
     apply str_ind_l'.
      intros ? ? [<- H]. apply s_whl_ff. now apply Bool.negb_true_iff.
      rewrite <-dotA. intros s s'' [? [<- H] [s' H' H'']]. apply s_whl_tt. assumption.
      econstructor. apply IHp, H'. assumption.
Qed. 


(** * Some program equivalences *)

(** two programs are said to be equivalent if they have the same semantics *)
Notation "p ~ q" := (bstep p == bstep q) (at level 80). 

(** ad-hoc simplification tactic *)
Ltac simp := unfold bstep; fold bstep.


(** ** denesting nested loops *)
Lemma two_loops b p: 
  whl b (whl b p)  ~  whl b p.
Proof. simp. kat. Qed.

(** ** folding a loop *)
Lemma fold_loop b p: 
  whl b (p ;; ite b p skp)  ~  
  whl b p.
Proof. simp. kat. Qed.

(** ** eliminating deadcode *)
Lemma dead_code b p q r: 
  (whl b p ;; ite b q r)  ~  
  (whl b p ;; r).
Proof. simp. kat. Qed.

Lemma dead_code' a b p q r: 
  (whl (a \cup b) p ;; ite b q r)  ~ 
  (whl (a \cup b) p ;; r).
Proof. simp. kat. Qed.


(** * Reasoning about assignations *)

(** (higher-order style) substitution in formulas and expressions *)
Definition subst x v (A: dset state): dset state := 
  fun s => A (update x (v s) s).
Definition esubst x v (e: state -> nat): state -> nat := 
  fun s => e (update x (v s) s).

(** is [x] fresh in the expression e *)
Definition fresh x (e: state -> nat) := forall v s, e (update x v s) = e s.

Hypothesis update_twice: forall x i j s, update x j (update x i s) = update x j s.
Hypothesis update_comm: forall x y i j s, x<>y -> update x i (update y j s) = update y j (update x i s).


(** ** stacking assignations *)

Lemma aff_stack x e f:
  (x <- e ;; x <- f)  ~  
  (x <- esubst x e f).
Proof.
  simp. rewrite frel_comp.
  apply frel_weq; intro s. 
  apply update_twice.
Qed.


(** ** removing duplicates *)

Lemma aff_idem x e: fresh x e -> (x <- e ;; x <- e)  ~  (x <- e). 
Proof. 
  intro. rewrite aff_stack. 
  intros s s'. cbv. rewrite (H (e s)). tauto.
Qed.

(** ** commuting assignations *)

Lemma aff_comm x y e f: x<>y  -> fresh y e ->  
  (x <- e ;; y <- f)  ~ (y <- esubst x e f ;; x <- e).
Proof.
  intros Hx Hy. simp. rewrite 2frel_comp. apply frel_weq; intro s.
  rewrite update_comm by congruence. 
  now rewrite (Hy _). 
Qed.

(** ** delaying choices *)

(** in the above example, we cannot exploit KAT since this is just
   about assignations. In the following example, we show how to
   perform a mixed proof: once we assert that the test [t] somehow
   commutes with the assignation [x<-e], [hkat] can make use of this
   assumption to close the goal *)

Lemma aff_ite x e t p q: 
  (x <- e ;; ite t p q)  
  ~ 
  (ite (subst x e t) (x <- e ;; p) (x <- e ;; q)).
Proof.
  simp. 
  assert (H: upd x e * [t] == [subst x e t] * upd x e)
   by (cbv; firstorder; subst; eauto). 
  hkat.
Qed.



(** * Embedding Hoare logic for partial correctness *)

(** Hoare triples for partial correctness can be expressed really
   easily using KAT: *)
Notation Hoare A p B := ([A] * bstep p * [!B] <== 0).

(** ** correspondence w.r.t. the standard interpretation of Hoare triples  *)
Lemma Hoare_eq A p B: 
  Hoare A p B <-> 
  forall s s', A s -> bstep p s s' -> B s'.
Proof.
  split. 
  - intros H s s' HA Hp. case_eq (B s'). reflexivity. intro HB. 
    destruct (H s s'). exists s'. exists s. 
    now split. assumption. split. reflexivity. simpl. now rewrite HB. 
  - intros H s s' (?&?&<-&HA). intros Hp (->&HB). simpl in HB. 
    rewrite (H _ _ HA Hp) in HB. discriminate. 
Qed.



(** ** deriving Hoare logic rules using the [hkat] tactic *)

(** Hoare triples are encoded as propositions of the shape [x <== 0] ;
   therefore, they can always be eliminated by [hkat], so that all
   rules of Hoare logic can be proved automatically (except for the
   assignation rule, of course) 

   This idea come from the following paper:
   Dexter Kozen. On Hoare logic and Kleene algebra with tests. 
   Trans. Computational Logic, 1(1):60-76, July 2000.
   
   The fact that we have an automatic tactic makes it trivial to
   formalise it. *)

Lemma weakening (A A' B B': dset state) p: 
  A' <== A -> Hoare A p B -> B <== B' -> Hoare A' p B'.
Proof. hkat. Qed.

Lemma rule_skp A: Hoare A skp A.
Proof. simp. kat. Qed.

Lemma rule_seq A B C p q: 
  Hoare A p B -> 
  Hoare B q C -> 
  Hoare A (p;;q) C.
Proof. simp. hkat. Qed.

Lemma rule_ite A B t p q: 
  Hoare (A \cap t) p B -> 
  Hoare (A \cap !t) q B -> 
  Hoare A (ite t p q) B.
Proof. simp. hkat. Qed.

Lemma rule_whl A t p: 
  Hoare (A \cap t) p A -> 
  Hoare A (whl t p) (A \cap neg t).
Proof. simp. hkat. Qed.

Lemma rule_aff x v (A: dset state): Hoare (subst x v A) (x <- v) A.
Proof. 
  rewrite Hoare_eq. intros s s' HA H. 
  now inversion_clear H.
Qed.

Lemma wrong_rule_whl A t p: 
  Hoare (A \cap !t) p A -> 
  Hoare A (whl t p) (A \cap !t).
Proof. simp. Fail hkat. Abort.

Lemma rule_whl' (I A: dset state) t p: 
  Hoare (I \cap t) p I -> 
  I \cap !t <== A -> 
  Hoare I (whl t p) A.
Proof. eauto 3 using weakening, rule_whl. Qed.

End s.
