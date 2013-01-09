(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * imp: a formalisation of the IMP programming language on top of KAT *)

(* We formalise the IMP language (whose programs are also known as
   "while programs"). We give a big step semantics as an inductive
   predicate, and using KAT, and we show that the two versions
   actually coincide.
   
   We then use the [kat] tactic to prove some simple program
   equivalences, and to derive all rules of corresponding Hoare logic
   for partial correctness. *)

Require Import kat prop rel comparisons kat_tac.
Require Import String FunctionalExtensionality.
Open Scope string_scope.

(** * Definition of the languague *)

(** we use string to denote locations (variables) *)

Definition string_compare x y := if string_dec x y then Eq else Lt.
Lemma string_cmp_spec: forall x y, compare_spec (x=y) (string_compare x y).
Proof. intros. unfold string_compare. case string_dec; constructor; congruence. Qed.
Canonical Structure string_cmp := mk_simple_cmp _ string_cmp_spec.


(** state (or memory): a map from strings (locations) to natural numbers *)

Definition state := string -> nat.


(** ** arithmetic expressions *)

Inductive expr :=
| var (x: string)
| cst (k: nat)
| pls (e f: expr)
| min (e f: expr)
| mul (e f: expr).

(** coercions and notations  *)
Coercion var: string >-> expr.
Coercion cst: nat >-> expr.
Bind Scope e_scope with expr.
Delimit Scope e_scope with e.
Infix "+" := pls: e_scope.
Infix "-" := min: e_scope.
Infix "*" := mul: e_scope.
Notation "0" := O: e_scope.
Notation "1" := (S O): e_scope.
Arguments pls _%e _%e. 
Arguments min _%e _%e. 
Arguments mul _%e _%e. 

(** evaluation of arithmetic expressions *)
Fixpoint eval e (s: state) :=
  match e with
    | var x => s x
    | cst k => k
    | pls e f => eval e s + eval f s
    | mul e f => eval e s * eval f s
    | min e f => eval e s - eval f s
  end%nat.

(** ** Boolean tests *)

Inductive test :=
| tst (e f: expr)
| cnj (e f: test)
| dsj (e f: test)
| neg (f: test)
| top
| bot.

(** notations *)
Bind Scope t_scope with test.
Delimit Scope t_scope with t.
Infix "?=" := tst (at level 80): t_scope.
Infix "&&" := cnj: t_scope.
Infix "||" := dsj: t_scope.
Arguments cnj _%t _%t.
Arguments dsj _%t _%t.
Arguments neg _%t.

(** evaluation of Boolean tests *)
Fixpoint teval e: dset state :=
  match e with
    | tst e f => fun s => eqb (eval e s) (eval f s)
    | cnj e f => teval e \cap teval f
    | dsj e f => teval e \cup teval f
    | neg e => ! teval e
    | top => lattice.top
    | bot => lattice.bot
  end.
Coercion teval: test >-> car.



(** ** programs *)

Inductive prog :=
| skp
| aff (x: string) (e: expr)
| seq (p q: prog)
| ite (t: test) (p q: prog)
| whl (t: test) (p: prog).

(** notations *)
Bind Scope imp_scope with prog.
Delimit Scope imp_scope with imp.
Notation "x  <- y" := (aff x%string y%e) (at level 90): imp_scope.
Notation "p  ;; q" := (seq p%imp q%imp) (left associativity, at level 101): imp_scope.
Arguments ite _%t _%imp _%imp.
Arguments whl _%t _%imp.


(** * Big step semantics *)

(** updating a state, by assigning a new value [i] to [x] *)
Definition update x i (s: state): state :=
  fun y => if eqb x y then i else s y.

(** corresponding functional relation *)
Notation upd x e := (frel (fun s => update x (eval e s) s)).


(** ** using KAT expressions in the model of relations

   the semantics can then be given by induction on the program, using
   a simple fixpoint *)

Fixpoint bstep (p: prog): rel state state :=
  match p with
    | skp => 1
    | aff x e => upd x e
    | seq p q => bstep p * bstep q
    | ite t p q => [t] * bstep p + [!t] * bstep q
    | whl t p => ([t] * bstep p)^*  *  [!t]
  end.

(** ** using an inductive predicate, as in standard textbooks *)

Inductive bstep': prog -> rel state state :=
| s_skp: forall s, bstep' skp s s
| s_aff: forall x e s, bstep' (x <- e) s (update x (eval e s) s)
| s_seq: forall p q s s' s'', bstep' p s s' -> bstep' q s' s'' -> bstep' (p ;; q) s s''
| s_ite_ff: forall e p q s s', teval e s = false -> bstep' q s s' -> bstep' (ite e p q) s s'
| s_ite_tt: forall e p q s s', teval e s = true -> bstep' p s s' -> bstep' (ite e p q) s s'
| s_whl_ff: forall e p s, teval e s = false -> bstep' (whl e p) s s
| s_whl_tt: forall e p s s', teval e s = true -> bstep' (p ;; whl e p) s s' -> bstep' (whl e p) s s'.

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
     exists s. apply (str_refl ([e] * bstep p)). reflexivity.
      simpl. unfold rel_inj. simpl. now rewrite H.
     destruct IHbstep' as [t ? [t' ? ?]]. exists t'. 2: assumption. 
     apply (str_cons ([e] * bstep p)). exists t. 2: assumption.
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
Ltac simp := unfold bstep; fold bstep; unfold teval; fold teval.


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
  (whl (a || b) p ;; ite b q r)  ~ 
  (whl (a || b) p ;; r).
Proof. simp. kat. Qed.


(** * Reasoning about assignations *)

(** KAT cannot handle assignations: it's axioms mainly take care of
   the control flow graph. We can however setup various tools to
   reason about them manually. *)

(** ** free variables *)

Require Import lset.
Notation " [[ p ]] " := (inj p): ra_terms. 

Fixpoint fv e :=
  match e with
    | var x => [x]
    | cst k => []
    | pls e f 
    | mul e f 
    | min e f => fv e \cup fv f
  end.

Fixpoint tfv t :=
  match t with
    | tst e f => fv e \cup fv f
    | cnj e f 
    | dsj e f => tfv e \cup tfv f
    | neg e => tfv e
    | top 
    | bot => []
  end.

(** ** substitutions *)

Section s.
Variable x: string. 
Variable v: expr. 

Fixpoint subst e: expr :=
  match e with
    | var y => if eqb x y then v else y
    | cst k => k
    | pls e f => subst e + subst f
    | mul e f => subst e * subst f
    | min e f => subst e - subst f
  end%e.

Fixpoint tsubst t: test :=
  match t with
    | tst e f => subst e ?= subst f
    | cnj e f => tsubst e && tsubst f
    | dsj e f => tsubst e || tsubst f
    | neg e => neg (tsubst e)
    | top => top
    | bot => bot
  end%t.

(** ** bureaucratic lemmas about evalutaion and substitution *)

Lemma eval_subst e s: eval (subst e) s = eval e (update x (eval v s) s).
Proof. 
  induction e; simpl; try congruence. 
  unfold update; simpl. now case eqb_spec. 
Qed.

Lemma teval_subst t s: teval (tsubst t) s = teval t (update x (eval v s) s).
Proof. 
  induction t; simpl; try congruence. 
  now rewrite 2eval_subst.
Qed.

Lemma subst_out e: ~In x (fv e) -> subst e = e.
Proof.
  induction e; simpl fv; simpl subst; rewrite ?in_app_iff; intros H.
   case eqb_spec. 2: reflexivity. intros <-. elim H. now left. 
   reflexivity. 
   now rewrite IHe1, IHe2 by tauto.
   now rewrite IHe1, IHe2 by tauto.
   now rewrite IHe1, IHe2 by tauto.
Qed.

Lemma tsubst_out t: ~In x (tfv t) -> tsubst t = t.
Proof.
  induction t; simpl tfv; simpl tsubst; rewrite ?in_app_iff; intro H.
   now rewrite 2subst_out by tauto. 
   now rewrite IHt1, IHt2 by tauto.
   now rewrite IHt1, IHt2 by tauto.
   now rewrite IHt by assumption.
   reflexivity. 
   reflexivity.
Qed.

End s.

Lemma eval_out x e: ~In x (fv e) -> forall i s, eval e (update x i s) = eval e s.
Proof. intros. setoid_rewrite <-(eval_subst x i). now rewrite subst_out. Qed.

Lemma teval_out x t: ~In x (tfv t) -> forall i s, teval t (update x i s) = teval t s.
Proof. intros. setoid_rewrite <-(teval_subst x i). now rewrite tsubst_out. Qed.

Lemma update_twice x i j s: update x j (update x i s) = update x j s.
Proof. 
  unfold update. apply functional_extensionality. intro y.
  case eqb_spec; congruence. 
Qed.

Lemma update_comm x y i j s: x<>y -> update x i (update y j s) = update y j (update x i s).
Proof. 
  intro. unfold update. apply functional_extensionality. intro z.
  case eqb_spec; case eqb_spec; congruence. 
Qed.


(** ** back to program equivalences *)

(** *** stacking assignations *)
Lemma aff_stack x e f:
  (x <- e ;; x <- f)  ~  
  (x <- subst x e f).
Proof.
  simp. rewrite frel_comp.
  apply frel_weq; intro s. 
  rewrite <-eval_subst. 
  apply update_twice.
Qed.

(** *** removing duplicates *)
Lemma aff_idem x e: ~In x (fv e)  ->  
  (x <- e ;; x <- e)  ~  (x <- e). 
Proof. 
  intro. rewrite aff_stack. 
  now rewrite subst_out by assumption.
Qed.

(** *** commuting assignations *)
Lemma aff_comm x y e f: x<>y  ->  
  ~In y (fv e)  ->  
  (x <- e ;; y <- f)  ~ (y <- subst x e f ;; x <- e).
Proof.
  intros Hx Hy. simp. rewrite 2frel_comp. apply frel_weq; intro s. 
  rewrite (eval_out y) by assumption.
  rewrite eval_subst.
  now rewrite update_comm by congruence.
Qed.

(** *** delaying choices *)

(** in the above examples, we cannot exploit KAT since they are just
   about assignations. In the following example, we show how to
   perform a mixed proof: once we assert that the test [[t]] somehow
   commutes with the assignation [x<-e], [hkat] can make use of this
   assumption to close the goal *)

Lemma aff_ite x e t p q: 
  (x <- e ;; ite t p q)  
  ~ 
  (ite (tsubst x e t) (x <- e ;; p) (x <- e ;; q)).
Proof.
  simp. 
  assert (H: upd x e * [[t]] == [[tsubst x e t]] * upd x e).
   intros s s'. simpl. unfold rel_dot, rel_inj, frel. rewrite teval_subst. 
   split. intros [? -> [<- ?] ]. eauto. intros [? [<- ?] ->]. eauto.
  hkat.
Qed.



(** * Embedding Hoare logic for partial correctness *)

(** Hoare triples for partial correctness can be expressed really
   easily using KAT: *)
Notation Hoare A p B := ([[teval A]] * bstep p * [[!teval B]] <== 0).

(** ** correspondence w.r.t. the standard interpretation of Hoare triples  *)
Lemma Hoare_eq A p B: 
  Hoare A p B <-> 
  forall s s', teval A s -> bstep p s s' -> teval B s'.
Proof.
  split. 
  - intros H s s' HA Hp. case_eq (teval B s'). reflexivity. intro HB. 
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

Lemma weakening (A A' B B': test) p: 
  A' <== A -> Hoare A p B -> B <== B' -> Hoare A' p B'.
Proof. hkat. Qed.

Lemma rule_skp A: Hoare A skp A.
Proof. simp. kat. Qed.

Lemma rule_aff x v A: Hoare (tsubst x v A) (x <- v) A.
Proof. 
  rewrite Hoare_eq. intros s s' HA H. 
  inversion_clear H. now rewrite <-teval_subst. 
Qed.

Lemma rule_seq A B C p q: 
  Hoare A p B -> 
  Hoare B q C -> 
  Hoare A (p;;q) C.
Proof. simp. hkat. Qed.

Lemma rule_ite A B t p q: 
  Hoare (A && t) p B -> 
  Hoare (A && neg t) q B -> 
  Hoare A (ite t p q) B.
Proof. simp. hkat. Qed.

Lemma rule_whl A t p: 
  Hoare (A && t) p A -> 
  Hoare A (whl t p) (A && neg t).
Proof. simp. hkat. Qed.

Lemma wrong_rule_whl A t p: 
  Hoare (A && neg t) p A -> 
  Hoare A (whl t p) (A && neg t).
Proof. simp. Fail hkat. Abort.

Lemma rule_whl' (I A: test) t p: 
  Hoare (I && t) p I -> 
  teval (I && neg t) <== A -> 
  Hoare I (whl t p) A.
Proof. eauto 3 using weakening, rule_whl. Qed.
