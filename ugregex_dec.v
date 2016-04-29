(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * ugregex_dec: simple decision procedure for untyped generalised regular expressions *)

(** We implement a rather basic algorithm consisting in trying to
   build a bisimulation on-the-fly, using partial derivatives.
   
   We prove the correctness of this algorithm, but not completeness
   ("it merely let you sleep better" according to Krauss and Nipkow).
   
   This very simple algorithm seems to be sufficient for reasonable
   expressions; we plan to improve it to be able to handle larger
   ones. *)

Require Import lset kat positives sums glang boolean comparisons powerfix.
Require Export ugregex.
Set Implicit Arguments.


Section l.
Variable Pred: nat.
Notation Sigma := positive.
Notation Atom := (ord (pow2 Pred)).
Notation tt := ugregex_tt. 
Notation ugregex := (ugregex_monoid_ops Pred tt tt).
Notation uglang := (glang_kat_ops Pred Sigma traces_tt traces_tt).
Notation lang := (@lang Pred).

Ltac fold_ugregex_type := change (@ugregex.ugregex Pred) with (@car ugregex) in *.
Ltac fold_ugregex := ra_fold ugregex_monoid_ops tt; fold_ugregex_type.

(** * Partial derivatives *)

(** reversed product *)
Notation tod e := (fun f => u_dot f e) (only parsing).

(** [pderiv a i e] returns the set of partial derivatives of [e] along
   transition [(a,i)] (since we work with KAT regular expressions,
   labels are composed of an atom together with a letter) *)
Fixpoint pderiv a i (e: ugregex): list ugregex :=
  match e with
    | u_prd _ => []
    | u_var _ j => if eqb_pos i j then [u_one _] else []
    | u_pls e f => union (pderiv a i e) (pderiv a i f)
    | u_dot e f => 
        if epsilon a e then union (map (tod f) (pderiv a i e)) (pderiv a i f)
        else map (tod f) (pderiv a i e)
    | u_itr e => map (tod (u_str e)) (pderiv a i e)
  end.

(** [epsilon] was defined in [ugregex], 
   we now to extend both notions to sets of expressions, homomorphically: *)

Definition epsilon' a (l: list ugregex): bool :=
  fold_right (fun e b => b ||| epsilon a e) false l.

Definition pderiv' a i (l: list ugregex): list ugregex :=
  fold_right (fun e => union (pderiv a i e)) [] l.


(** specification of [epsilon'] *)
Lemma epsilon'_eq a l: epsilon a (sup id l) == epsilon' a l.
Proof.
  induction l. reflexivity. simpl.
  rewrite <- IHl. unfold id. 
  rewrite <-2Bool.orb_lazy_alt. apply Bool.orb_comm.
Qed.

(** correctness of partial derivatives *)
Lemma deriv_eq a i e: deriv a i e == sup id (pderiv (set.mem a) i e).
Proof.
  induction e; simpl; fold_ugregex.
   case eqb_pos. 2: reflexivity. now rewrite sup_singleton. 
   reflexivity.
   rewrite union_app, sup_app. now apply cup_weq.
   assert (H: deriv a i e1 * e2 == sup id (map (tod e2) (pderiv (set.mem a) i e1))).
    rewrite sup_map. setoid_rewrite <-(dotsumx (X:=ugregex_monoid_ops _)).
    now apply dot_weq.
   case epsilon.
    rewrite union_app, sup_app.
    setoid_rewrite dot1x. now apply cup_weq.
    setoid_rewrite dot0x. now rewrite cupxb.
   rewrite sup_map. setoid_rewrite <-(dotsumx (X:=ugregex_monoid_ops _)).
    now apply dot_weq.
Qed.

Lemma deriv'_eq a i l: deriv a i (sup id l) == sup id (pderiv' (set.mem a) i l).
Proof.
  induction l. reflexivity. simpl (sup _ _).
  rewrite union_app, sup_app.
  apply cup_weq. apply deriv_eq. assumption.
Qed.

(** Kleene variables of an expression *)
Fixpoint vars (e: ugregex) : list _ :=
  match e with
    | u_prd _ => []
    | u_var _ i => [i]
    | u_pls e f | u_dot e f => union (vars e) (vars f)
    | u_itr e => vars e
  end.

(** partial derivatives do not increase the set of Kleene variables *)
Lemma deriv_vars a i (e: ugregex): \sup_(x\in pderiv a i e) vars x <== vars e. 
Proof.
  induction e; simpl pderiv; simpl vars. 
   case eqb_pos; apply leq_bx. 
   apply leq_bx. 
   rewrite 2union_app, sup_app. now apply cup_leq.
   setoid_rewrite union_app at 2.
   assert (H: \sup_(x\in map (tod e2) (pderiv a i e1)) vars x <== vars e1 ++ vars e2).
    rewrite sup_map. simpl vars. setoid_rewrite union_app. rewrite supcup. 
    apply cup_leq. assumption. now apply leq_supx.
   case epsilon. rewrite union_app, sup_app, H. hlattice. assumption. 
   rewrite sup_map. simpl vars. setoid_rewrite union_app. rewrite supcup. 
    apply leq_cupx. assumption. now apply leq_supx.
Qed.
 
Lemma deriv'_vars a i l: \sup_(x\in pderiv' a i l) vars x <== sup vars l.
Proof.
  induction l. reflexivity. setoid_rewrite union_app. rewrite sup_app. 
  apply cup_leq. apply deriv_vars. assumption.
Qed.


(** deriving an expression w.r.t. a letter it does not contain necessarily gives [0] *)
Lemma deriv_out a i e I: vars e <== I -> ~In i I -> deriv a i e == 0. 
Proof.
  intros He Hi. induction e; simpl deriv; simpl vars in He; fold_ugregex. 
   case eqb_spec. 2: reflexivity. intros <-. apply Hi in He as []. now left. 
   reflexivity. 
   rewrite union_app in He. 
    rewrite IHe1, IHe2 by (rewrite <-He; lattice). apply cupI. 
   rewrite union_app in He. 
    rewrite IHe1, IHe2 by (rewrite <-He; lattice). rewrite dot0x, dotx0. apply cupI. 
   rewrite IHe by assumption. apply dot0x. 
Qed.


(** we need binary relations on sets of expressions, we represent them
   as lists of pairs (this could easily be optimised) *)
Definition rel_mem (p: list ugregex * list ugregex) := existsb (eqb p).
Notation rel_insert p rel := (p::rel).
Notation rel_empty := [].
(* OPT *)
(* Definition rel_mem := trees.mem (pair_compare (list_compare compare)).  *)
(* Definition rel_insert := trees.insert (pair_compare (list_compare compare)).  *)
(* Notation rel_empty := (@trees.L _) *)

Lemma rel_mem_spec p rel: reflect (In p rel) (rel_mem p rel).
Proof.
  induction rel. constructor. tauto.
  simpl rel_mem. case eqb_spec. 
  intros <-. constructor. now left.
  case IHrel; constructor. now right. intros [?|?]; congruence.
Qed.


(** * Main loop for the on-the-fly bisimulation algorithm *)

(** [epsilon'] and [deriv'] provide us with a (generalised) DFA whose
   states are sets of generalised expressions ([list ugregex]). We
   simply try compute bisimulations in this DFA. *)

Section a.

(** we assume a set of Kleene variable, and a set of atoms; the
   following algorithm tries to compute bisimulations w.r.t. those
   sets. *)
Variable I: list positive.
Variable A: list (ord Pred -> bool).

Definition obind X Y (f: X -> option Y) (x: option X): option Y := 
  match x with Some x => f x | _ => None end.

Fixpoint ofold X Y (f: X -> Y -> option Y) (l: list X) (y: Y): option Y :=
  match l with
    | [] => Some y
    | x::q => obind (f x) (ofold f q y)
  end.

(** [loop_aux e f a todo] checks the accepting status of [e] and [f] along [a], 
   - if a mismatch is found, we can stop (a counter example has bee found)
   - otherwise, it inserts all derivatives of the pair [(e,f)] along [{a}*I] into [todo] *)
Definition loop_aux e f := 
  fun a todo => 
    if eqb_bool (epsilon' a e) (epsilon' a f) 
    then Some (fold_right (fun i => cons (pderiv' a i e, pderiv' a i f)) todo I)
    else None.

(** [ofold (loop_aux e f) A todo] does the same, for all [a\in A] *)

(** [loop n rel todo] is the main loop of the algorithm:
   it tries to prove that all pairs in [todo] are bisimilar, assuming
   that those in [rel] are bisimilar.
   - if a pair of [todo] was already in [rel], it can be skipped;
   - otherwise, its accepting status is checked, all derivatives are
     inserted in [todo], and the pair is added to [rel]
   The number of iterations is bounded by [2^n], using the [powerfix] operator. *)
Definition loop n := powerfix n (fun loop rel todo =>
  match todo with
    | [] => Some true
    | (e,f)::todo => 
      if rel_mem (e,f) rel then loop rel todo else 
        match ofold (loop_aux e f) A todo with
          | Some todo => loop (rel_insert (e,f) rel) todo
          | None => Some false
        end
    end
) (fun _ _ => None).




(** * Correctness of the main loop *)

(** [prog] is a predicate on binary relations:

   [prog rel (rel++todo)] is the invariant of the main loop *)

Definition prog R S :=
  forall e f, In (e,f) R -> sup vars (e++f) <== I /\
    forall a, In a A -> epsilon' a e = epsilon' a f /\ 
      forall i, In i I -> In (pderiv' a i e, pderiv' a i f) S.

Lemma prog_cup_x R R' S: prog R S -> prog R' S -> prog (R++R') S.
Proof. intros H H' e f Hef. apply in_app_iff in Hef as [?|?]. now apply H. now apply H'. Qed.

Lemma prog_x_leq R S S': prog R S -> S <== S' -> prog R S'.
Proof. 
  intros H H' e f Hef. apply H in Hef as [? Hef]. 
  split. assumption. split. now apply Hef. intros. now apply H', Hef. 
Qed.

Definition below_I todo := forall e f, In (e,f) todo -> sup vars (e++f) <== I.

(** specification of the inner loop *)

Lemma loop_aux_spec e f a todo todo': 
  below_I ((e,f)::todo) ->
  loop_aux e f a todo = Some todo' -> 
  epsilon' a e = epsilon' a f /\
  todo <== todo' /\
  below_I todo' /\
  forall i, In i I -> In (pderiv' a i e, pderiv' a i f) todo'.
Proof.
  unfold loop_aux. case eqb_bool_spec. 2: discriminate. intros Heps Hvars E. 
  split. assumption. injection E. clear E Heps. revert todo'. 
  induction I as [|i J IH]; simpl fold_right; intro todo'. 
   intros <-. split. reflexivity. split. intros ? ? ?. apply Hvars; now right. intros _ []. 
   intro E. destruct todo' as [|p todo']. discriminate. 
   injection E. intros H <-. clear E. apply IH in H as [H1 [H2 H3]]. clear IH. 
   split. fold_cons. rewrite <- H1. lattice.
   split. intros ? ? [E|H]. 
    injection E; intros <- <-. rewrite sup_app, 2deriv'_vars, <-sup_app. apply Hvars. now left.
    now apply H2. 
   intros b [<-|Hb]. now left. right. now apply H3. 
Qed.

Lemma fold_loop_aux_spec e f todo: forall todo',
  below_I ((e,f)::todo) ->
  ofold (loop_aux e f) A todo = Some todo' -> 
  todo <== todo' /\
  below_I todo' /\
  forall a, In a A -> epsilon' a e = epsilon' a f /\
  forall i, In i I -> In (pderiv' a i e, pderiv' a i f) todo'.
Proof.
  induction A as [|b B IH]; simpl ofold; intros todo'.
   intros Hvars H. injection H. intros <-. split. reflexivity. 
   split. intros ? ? ?. apply Hvars. now right. intros _ []. 
  unfold obind. fold_ugregex_type. case_eq (ofold (X:=ord Pred -> bool) (loop_aux e f) B todo). 
   2: discriminate. 
  intros todo'' Htodo'' Hvars Htodo'.
  apply IH in Htodo'' as [Htodo''_leq [Hvars' Htodo'']]. 2: assumption. clear IH. 
  apply loop_aux_spec in Htodo' as (Heps&Htodo'_leq&Hvars''&Htodo'). 
  split. etransitivity; eassumption. 
  split. assumption. 
  intros a [<-|Ha]. now split. 
  apply Htodo'' in Ha as [Haeps Ha]. split. assumption. 
  intros. now apply Htodo'_leq, Ha. 
  intros ? ? [E|?]. injection E; intros <- <-. apply Hvars; now left. now apply Hvars'.
Qed.

Lemma In_cons X (a: X) l: In a l -> [a]++l <== l. 
Proof. now intros ? ? [<-|?]. Qed.

(** specification of the outer loop *)

Lemma prog_loop n: forall rel todo,
  loop n rel todo = Some true ->
  prog rel (rel++todo) -> 
  below_I todo ->
  exists rel', rel++todo <== rel' /\ prog rel' rel'.
Proof.
  (* TODO: use powerfix_invariant *)
  unfold loop. rewrite powerfix_linearfix. generalize (pow2 n). clear n. intro n.
  induction n; intros rel todo Hloop Hrel Hvars. discriminate. 
  simpl in Hloop. destruct todo as [|[e f] todo]. 
   exists rel. split. now rewrite <- app_nil_end. now rewrite <-app_nil_end in Hrel. 
   revert Hloop. case rel_mem_spec. 
   intros Hef Hloop. apply IHn in Hloop as (rel'&H1&H2).
    eexists. split. 2: eassumption. 
     rewrite <- H1. rewrite <-(In_cons Hef) at 2. fold_cons. lattice. 
    eapply prog_x_leq. apply Hrel. 
     rewrite <-(In_cons Hef) at 2. fold_cons. lattice. 
    intros ? ? ?. apply Hvars. now right. 
   intros _. fold_ugregex_type. case_eq (ofold (X:=ord Pred -> bool) (loop_aux e f) A todo). 
    2: discriminate. 
   intros todo' Htodo' Hloop. 
   apply fold_loop_aux_spec in Htodo' as [Htodo' [Hvars' Hef]]. 2: assumption.
   destruct (IHn _ _ Hloop) as (rel'&Hrel'&Hrel''). 2: assumption. 
   clear - Hef Hvars Hvars' Hrel Htodo'. 
   apply (@prog_cup_x [_]). eapply prog_x_leq. 
    intros ? ? [E|[]]. injection E; intros <- <-; clear E. 
    split. apply Hvars. now left. apply Hef. lattice.
   eapply prog_x_leq. apply Hrel. rewrite <- Htodo'. fold_cons. lattice. 
   eexists. split. 2: eassumption. rewrite <-Hrel', <-Htodo'. fold_cons. lattice.
Qed.

End a.

Existing Instance lang'_weq.

(** correctness of the bisimulation proof method, at the abstract level *)

Lemma prog_correct I l rel: 
  (forall a, In (set.mem a) l) ->
  prog I l rel rel -> below_I I rel -> 
  forall e f, In (e,f) rel -> sup lang e == sup lang f.
Proof.
  intros Hl Hrel Hvars e f Hef. 
  rewrite <-2lang_sup, 2lang_lang'. 
  intro w. revert e f Hef. induction w; simpl lang'; intros e f Hef. 
  - apply Hrel in Hef as [_ Hef]. 
    rewrite 2epsilon'_eq. destruct (Hef _ (Hl a)) as [-> _]. reflexivity. 
  - destruct (fun H => In_dec H i I) as [Hi|Hi]. decide equality.
    etransitivity. apply lang'_weq. apply deriv'_eq. 
    etransitivity. 2: apply lang'_weq; symmetry; apply deriv'_eq. 
    apply IHw. apply Hrel. assumption. apply Hl. assumption. 
    clear IHw. revert w. apply lang'_weq. rewrite 2deriv_sup.
    rewrite 2sup_b. reflexivity. 
     intros f' Hf. eapply deriv_out. 2: eassumption. 
      etransitivity. 2: apply Hvars. 2: apply Hef. apply leq_xsup. apply in_app_iff. now right. 
     intros e' He. eapply deriv_out. 2: eassumption. 
      etransitivity. 2: apply Hvars. 2: apply Hef. apply leq_xsup. apply in_app_iff. now left. 
Qed.

(** * Final algorithm, correctness *)

(** the final algorithm is obtained by callign the main loop with
   appropriate arguments *)

Definition eqb_kat (e f: ugregex) :=
  let atoms := map (@set.mem _) (seq _) in
  let vars := vars (e+f) in
    loop vars atoms 1000 rel_empty [([e],[f])]%list.
(* stated as this, the algorithm is not complete: we would need to
   replace 1000 with the size of [e+f]... bzzz *)

(** correctness of the algorithm *)

Theorem eqb_kat_correct e f: eqb_kat e f = Some true -> e == f. 
Proof.
  unfold eqb_kat. intro H. apply prog_loop in H as [rel [Hef Hrel]]. 
  2: intros _ _ []. 
  2: simpl vars; intros ? ? [E|[]]; injection E; intros <- <-; 
      rewrite union_app, sup_app, 2sup_singleton; reflexivity.
  eapply prog_correct in Hrel. 
   2: intro; apply in_map, in_seq. 
   3: apply Hef; now left.
  rewrite 2sup_singleton in Hrel. assumption. 
  intros ? ? ?. now apply Hrel. 
Qed.

End l. 
