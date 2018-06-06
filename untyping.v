(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * untyping: untyping theorem for typed structures *)

(** More precisely, on the syntactic (free) models of all structures
   below Kleene algebra with converse and bottom elements.
   For more details, see "Untyping Typed Algebras and Colouring Cyclic
   Linear Logic", Damien Pous, Logical Methods in Computer Science
   8(2:13) (2012) *)

Require Import kleene syntax.
Set Implicit Arguments.

(** * Cleaning terms *)

Section clean.
Context {Sigma: cmpType}.
(* used with Sigma=letter in kat_completeness *)
Variables (s t: Sigma -> positive).
Notation expr := (expr s t).

(** more aggressive hint for level constraint resolution *)
Local Hint Extern 0 (_ << _) => solve_lower || solve_lower': typeclass_instances.

(** induction scheme for syntax.expr (in)equality:

   (since (in)equality in the syntactic model (syntax.expr) is defined
   by impredicative encoding, we need to provide the induction scheme
   by ourselves). The impredicative encoding gives it almost directly *) 
Definition expr_ind leq weq := mk_ops _ 
  (fun n m => lattice.mk_ops (expr n m) (leq n m) (weq n m) 
    (@e_pls _ _ _ _ _)
    (@e_cap _ _ _ _ _)
    (@e_neg _ _ _ _ _)
    (@e_zer _ _ _ _ _)
    (@e_top _ _ _ _ _)
  ) 
  (@e_dot _ s t) 
  (@e_one _ s t) 
  (@e_itr _ s t) 
  (@e_str _ s t) 
  (@e_cnv _ s t)
  (@e_ldv _ s t)
  (@e_rdv _ s t).

Lemma expr_ind_eval leq weq n m (e: expr n m): 
  eval (X:=expr_ind leq weq) (f':=id) (@e_var _ _ _) e = e. 
Proof. induction e; simpl; f_equal; assumption. Qed.

(** we actually provide a mutual induction principle for [leq] and [weq]  *)
Lemma expr_leq_weq_ind l leq weq (L: laws l (expr_ind leq weq)) n m (e f: expr n m): 
  (e <==_[l] f -> leq n m e f) /\ (e ==_[l] f -> weq n m e f).
Proof. 
  split; intro H; 
    rewrite <-(expr_ind_eval leq weq e), <-(expr_ind_eval leq weq f);
      apply (H _ L id). 
Qed.


(** The following predicate specifies when an expression is considered
   as "clean": it does not contain any occurrence of [0] or residuals
   ([0] has to be factored out for the following proof to work, and
   residuals cannot be handled with the following methodology) *)

Fixpoint is_clean n m (x: expr n m) :=
  match x with
  | e_one _
  | e_var _ => True
  | e_pls x y 
  | e_dot x y => is_clean x /\ is_clean y
  | e_cnv x
  | e_itr x 
  | e_str x => is_clean x
  | _ => False
  end.

(** cleaning constructors: use annihilation laws to remove all
   occurrences of [0] (but the last one, if the expression reduces to
   [0]) *)

Definition e_pls' n m (x y: expr n m) :=
  (if is_zer x then y else if is_zer y then x else x+y)%ast.

Definition e_dot' n m p (x: expr n m) (y: expr m p) :=
  (if is_zer x then 0 else if is_zer y then 0 else x * y)%ast.

Definition e_itr' n (x: expr n n) :=
  (if is_zer x then 0 else x^+)%ast.

Definition e_str' n (x: expr n n) :=
  (if is_zer x then 1 else x^*)%ast.

Definition e_cnv' n m (x: expr n m) :=
  (if is_zer x then 0 else x`)%ast.

Fixpoint clean n m (x: expr n m): expr n m :=
  match x with
  | e_zer _ _ => 0
  | e_one _ => 1
  | e_pls x y => e_pls' (clean x) (clean y)
  | e_dot x y => e_dot' (clean x) (clean y)
  | e_itr x => e_itr' (clean x)
  | e_str x => e_str' (clean x)
  | e_cnv x => e_cnv' (clean x)
  | e_var a => e_var a
  (** unused cases, ruled out later by level constraints *)
  | x => x
  end%ast.

Lemma is_zer_clean n m (x: expr n m): is_clean x -> is_zer x = false.
Proof. induction x; simpl; intuition. Qed.

(** an expression reduces either to [0] or to a clean expression *)
Lemma clean_spec n m (x: expr n m): e_level x << BOT+CKA -> clean x = 0%ast \/ is_clean (clean x).
Proof.
  induction x; simpl e_level; simpl clean; 
    unfold e_pls', e_dot', e_itr', e_str', e_cnv'; 
    simpl is_clean; try intuition discriminate_levels. 
   intro Hl. 
    destruct IHx1 as [->|IHx1]. solve_lower'. apply IHx2. solve_lower'. 
    rewrite is_zer_clean by assumption. 
    destruct IHx2 as [->|IHx2]. solve_lower'. now right. 
    rewrite is_zer_clean by assumption. right; now split.
   intro Hl. 
    destruct IHx1 as [->|IHx1]. solve_lower'. now left. 
    rewrite is_zer_clean by assumption. 
    destruct IHx2 as [->|IHx2]. solve_lower'. now left. 
    rewrite is_zer_clean by assumption. right; now split.
   intro Hl. 
    destruct IHx as [->|IHx]. solve_lower'. now left. 
    rewrite is_zer_clean by assumption. now right. 
   intro Hl. 
    destruct IHx as [->|IHx]. solve_lower'. now right.
    rewrite is_zer_clean by assumption. simpl. tauto.
   intro Hl. 
    destruct IHx as [->|IHx]. solve_lower'. now left. 
    rewrite is_zer_clean by assumption. now right.
Qed.

(** simple tactic to do a case analysis on all encountered tests, in a
   bottom-up fashion *)
Ltac destruct_tests :=
  unfold e_pls', e_dot', e_itr', e_str', e_cnv'; simpl e_level; 
  match goal with
    | |- context[is_zer ?x] => 
      lazymatch x with context[is_zer _] => fail | _ => idtac end;
      case (is_zer_spec x); trivial; destruct_tests
    | _ => idtac
  end. 

(** the cleaning function does not increase the level of the expressions *)
Lemma clean_level n m (x: expr n m): e_level (clean x) << e_level x.
Proof.
  induction x; try reflexivity; simpl clean;
    revert_prop; destruct_tests; simpl e_level; 
      intros; solve_lower' || reflexivity. 
Qed.

Lemma is_zer_level n m (x: expr n m): is_zer x -> BOT << e_level x.
Proof. case is_zer_spec. reflexivity. discriminate. Qed.

(** if an expression reduces to [0], then [0] was appearing somewhere in that expression *)
Lemma clean_0_level n m (x: expr n m): clean x = 0%ast -> BOT << e_level x.
Proof. rewrite <-clean_level. now intros ->. Qed.

(** cleaning constructors are "correct": they correspond to their syntactic counterparts *)
Lemma e_pls_weq l n m x y: `{CUP + e_level x + e_level y << l} -> @e_pls' n m x y ==_[l] x+y.
Proof. destruct_tests; intros; lattice. Qed.

Lemma e_dot_weq l n m p x y: e_level x + e_level y << l -> @e_dot' n m p x y ==_[l] x*y.
Proof. destruct_tests; symmetry. apply dot0x. apply dotx0. Qed.

Lemma e_itr_weq l n x: STR + e_level x << l -> @e_itr' n x ==_[l] x^+.
Proof. destruct_tests. intros. now rewrite itr0. Qed.

Lemma e_str_weq l n x: STR + e_level x << l -> @e_str' n x ==_[l] x^*.
Proof. destruct_tests. intros. now rewrite str0. Qed.

Lemma e_cnv_weq l n m x: CNV + e_level x << l -> @e_cnv' n m x ==_[l] x`.
Proof. destruct_tests. intros. now rewrite cnv0. Qed.

(** the cleaning function thus returns an equivalent expression (at
   any level containing the operations appearing in that expression) *)
Lemma clean_weq l n m (x: expr n m): e_level x << l -> clean x ==_[l] x. 
Proof.
  induction x; simpl e_level; simpl clean; try reflexivity; 
    rewrite ?merge_spec; intuition. 
   rewrite e_pls_weq. apply cup_weq; auto. rewrite 2clean_level. solve_lower'. 
   rewrite e_dot_weq. apply dot_weq; auto. rewrite 2clean_level. solve_lower'. 
   rewrite e_itr_weq. apply itr_weq; auto. rewrite clean_level. solve_lower'. 
   rewrite e_str_weq. apply str_weq; auto. rewrite clean_level. solve_lower'. 
   rewrite e_cnv_weq. apply cnv_weq; auto. rewrite clean_level. solve_lower'. 
Qed.

(** simple tactic to discriminate unsatisfiable constraints *)
Ltac discr_levels Hl tac :=
  repeat match goal with 
           | |- _ << _ -> _ => let Hl' := fresh "Hl" in intro Hl'; try ((rewrite Hl in Hl'; discriminate Hl') || tac Hl')
           | |- _ \/ _ => right
         end;
  unfold Reflexive, Transitive, Proper, respectful; simpl;
  unfold e_dot', e_pls', e_cnv', e_itr', e_str'. 

(** ** key lemma 1: equivalent expressions reduce to [0] simultaneously *)
Lemma clean_leq_weq_0 l: l<<BOT+CKA -> 
  forall n m (x y: expr n m), 
       (x <==_[l] y ->  clean y = 0%ast  -> clean x = 0%ast)
    /\ (x  ==_[l] y -> (clean x = 0%ast <-> clean y = 0%ast)).
Proof. 
  intros Hl. apply expr_leq_weq_ind. 
  constructor; [constructor; [constructor|..] |..]; simpl ob in *;
    discr_levels Hl idtac; intro_vars; destruct_tests;
      intuition (congruence || discriminate). 
Qed.

Corollary clean_leq_0 l: l<<BOT+CKA -> forall n m (x y: expr n m), 
  x <==_[l] y -> clean y = 0%ast -> clean x = 0%ast.
Proof. apply clean_leq_weq_0. Qed.

(** the cleaning function is idempotent *)
Lemma clean_idem n m (e: expr n m): clean (clean e) = clean e.
Proof.
  induction e; simpl; trivial; destruct_tests;
    intros; simpl; rewrite ?IHe1, ?IHe2, ?IHe; destruct_tests; congruence.
Qed.

Lemma lower_bot h k: has_bot h = false -> h << BOT + k -> h << k.
Proof. rewrite 2lower_spec. simpl. intros ->. intuition discriminate. Qed.

(** ** key lemma 2: proofs with bottom elements can be factorised
   into a preliminary cleaning phase, followed by a "clean" proof which
   does not use bottom elements laws (we move from (in)equality proofs
   at level [BOT+l] to (in)equality proofs at level [l]) *)
Lemma clean_factorise_leq_weq l: l<<BOT+CKA -> 
  forall n m (x y: expr n m), 
       (x <==_[BOT+l] y -> clean x = 0%ast \/ clean x <==_[l] clean y)
    /\ (x  ==_[BOT+l] y -> clean x ==_[l] clean y).
Proof. 
  (* TOTHINK: on pourrait se passer de [clean_idem] en faisant une
  induction plus forte, où l'on garderait les hypothèses <==_[BOT+l]
  sous-jacentes, pour appliquer directement clean_leq_0 *)
  intros Hl. apply expr_leq_weq_ind. 
  constructor; [constructor; [constructor|..] |..]; 
    simpl ob in *; discr_levels Hl ltac:(fun Hl' => apply lower_bot in Hl'; [|reflexivity]);
      intro_vars; destruct_tests; try solve [intuition (reflexivity || discriminate)].

   intros [Hx|Hxy]. now left. 
   intros [Hy|Hyz]. left. revert Hy. 
   generalize (clean_leq_0 Hl Hxy). now rewrite 2clean_idem.
   right. etransitivity; eassumption. 

   rewrite weq_spec.
    split. intros [? ?]; split; now right.
    intros [[Hx|Hx] [Hy|Hy]].
     rewrite Hx, Hy. now split. 
     generalize (clean_leq_0 Hl Hy). rewrite 2clean_idem. 
      intro Hy'. now rewrite Hx, Hy'. 
     generalize (clean_leq_0 Hl Hx). rewrite 2clean_idem. 
      intro Hx'. now rewrite Hx', Hy. 
     now split. 

   rewrite cup_spec. intuition discriminate. 

   intros; apply dotA.

   intros; apply dot1x.

   intros; apply dotx1.

   intros ? ? ? [Hx|Hxy] H'. tauto. 
   generalize (clean_leq_0 Hl Hxy). rewrite clean_idem. tauto. 
   intros ? ? ? ? [Hx|Hxy] H'. tauto. 
   destruct H' as [Hx'|Hxy']. tauto.
   generalize (clean_leq_0 Hl Hxy'). rewrite clean_idem. tauto. 
   right. apply dot_leq; tauto. 

   right. now rewrite dotplsx.

   right. now rewrite dotxpls.

   right. apply cnvdot_.

   intros; apply cnv_invol.
   
   intros ? ? [Hx|Hxy]. tauto. 
   generalize (clean_leq_0 Hl Hxy). rewrite clean_idem. tauto. 

   right. apply cnv_leq. tauto. 
   right. apply cnv_ext. 
   right. apply str_refl. 
   right. apply str_cons. 

   right. now rewrite dot1x.
   right. apply str_ind_l; intuition discriminate. 

   right. now rewrite dotx1.
   right. apply str_ind_r; intuition discriminate. 

   intros _ _. apply itr_str_l.
Qed.

Corollary clean_factorise_leq l: l<<BOT+CKA -> 
  forall n m (x y: expr n m), x <==_[BOT+l] y -> clean x = 0%ast \/ clean x <==_[l] clean y.
Proof. apply clean_factorise_leq_weq. Qed.

End clean.

(** * Untyping theorem for bottom-free structures *)

Section e.
Context {Sigma: cmpType}.
Variables (s t: Sigma -> positive).
Notation uexpr := (expr (fun _: Sigma => xH) (fun _: Sigma => xH) xH xH). 
Notation expr := (expr s t).

(** evaluation predicate, to relate untyped expressions [uexpr] to typed ones [expr] 

   this cannot be a function:
   - an untyped expressions can correspond to several typed
     expressions (e.g., [1] is mapped to all identities). 
   - an untyped expression can possibly be ill-typed so that it does
     not map to any typed expression. *)

Inductive eval: forall n m, uexpr -> expr n m -> Prop :=
| ev_one: forall n, @eval n n 1 1
| ev_pls: forall x y n m x' y', @eval n m x x' -> @eval n m y y' -> eval (x+y) (x'+y')
| ev_dot: forall x y n m p x' y', @eval n m x x' -> @eval m p y y' -> eval (x*y) (x'*y')
| ev_itr: forall x n x', @eval n n x x' -> eval (x^+) (x'^+)
| ev_str: forall x n x', @eval n n x x' -> eval (x^* ) (x'^* )
| ev_cnv: forall x n m x', @eval n m x x' -> eval (x`) (x'`)
| ev_var: forall a, eval (e_var a) (e_var a).
Arguments eval : clear implicits.

(** inversion lemmas for [eval], for all operations
   
   although the statements look straighforward, the proofs are a bit
   technical since we avoid JMeq/eq_dep axioms ; the fact that the
   types of our expressions ([ob expr_ops]) is a decidable type
   ([positive]) is crucial for that: it is decidable, so that we have
   strong elimination of dependent equalities. *)

Lemma eval_pls n m x y z: eval n m (x+y) z -> 
  exists x', eval n m x x' /\ exists y', eval n m y y' /\ z=e_pls x' y'.
Proof. 
  remember (x+y)%ast as z' eqn:E. destruct 1; try discriminate. 
  rewrite <- (f_equal ((fun n m (e: syntax.expr _ _ n m) => 
    match e in syntax.expr _ _ n m return syntax.expr _ _ n m with e_pls x _ => x | x => x end) _ _) E). 
  rewrite <- (f_equal ((fun n m (e: syntax.expr _ _ n m) => 
    match e in syntax.expr _ _ n m return syntax.expr _ _ n m with e_pls _ y => y | x => x end) _ _) E). 
  eauto. 
Qed.

Lemma eval_dot n m x y z: eval n m (x*y) z -> 
  exists p, exists x', eval n p x x' /\ exists y', eval p m y y' /\ z=e_dot x' y'.
Proof. 
  remember (x*y)%ast as z' eqn:E. destruct 1; try discriminate.
  generalize (f_equal ((fun n m e =>
    match e in syntax.expr _ _ n m return syntax.expr _ _ n xH with 
      | @e_dot _ _ _ _ p _ x _ => 
        match eqb_spec cmp_pos p xH with 
          | reflect_t H => eq_rect _ (syntax.expr _ _ _) x _ H
          | _ => e_zer _ _
        end
      | x => e_zer _ _
    end) xH xH) E). case eqb_spec. 2: congruence. 
  intro. rewrite 2cmp_eq_rect_eq. intros <-. 
  generalize (f_equal ((fun n m e =>
    match e in syntax.expr _ _ n m return syntax.expr _ _ xH m with 
      | @e_dot _ _ _ _ p _ _ x => 
        match eqb_spec cmp_pos p xH with 
          | reflect_t H => eq_rect _ (fun p => syntax.expr _ _ p _) x _ H
          | _ => e_zer _ _
        end
      | x => e_zer _ _
    end) xH xH) E). case eqb_spec. 2: congruence. 
  intro. rewrite 2cmp_eq_rect_eq. intros <-. 
  eauto 6. 
Qed.

Lemma eval_cnv n m x z: eval n m (x`) z -> exists x', eval m n x x' /\ z=e_cnv x'.
Proof.
  remember (x`)%ast as z' eqn:E. destruct 1; try discriminate. 
  rewrite <- (f_equal ((fun n m (e: syntax.expr _ _ n m) => 
    match e with e_cnv x => x | _ => e_zer _ _ end) _ _) E). 
  eauto. 
Qed.

Lemma eval_one' n m z: eval n m 1 z -> n=m.
Proof. inversion 1. assumption. Qed.

Lemma eval_itr' n m x z: eval n m (x^+) z -> n=m.
Proof. inversion 1. assumption. Qed.

Lemma eval_str' n m x z: eval n m (x^* ) z -> n=m.
Proof. inversion 1. assumption. Qed.

Lemma eval_var' n m a z: eval n m (e_var a) z -> n=s a /\ m=t a.
Proof. inversion 1. auto. Qed.

Lemma eval_one n z: eval n n 1 z -> z=e_one n.
Proof. 
  assert (G: forall m u (z: expr n m), eval n m u z -> 
    forall (H: n=m), u=e_one _ -> z = eq_rect _ (expr n) (e_one n) m H).
  intros m z' H. destruct 1; intros; try discriminate. now rewrite cmp_eq_rect_eq. 
  intro Hz. apply (G _ _ _ Hz eq_refl eq_refl). 
Qed.

Lemma eval_itr n x z: eval n n (x^+) z -> exists x', eval n n x x' /\ z = e_itr x'.
Proof. 
  assert (G: forall m u (z: expr n m), eval n m u z -> 
    forall (H: n=m) x, u=e_itr x -> 
      exists x', eval n n x x' /\ z = eq_rect _ (expr n) (e_itr x') m H).
  intros m z' H. destruct 1; intros E v Hv; try discriminate. 
  rewrite <-(f_equal ((fun n m (e: syntax.expr _ _ n m) => 
    match e in syntax.expr _ _ n m return syntax.expr _ _ n m with e_itr y => y | x => x end) _ _) Hv).
  eexists. split. eassumption. now rewrite cmp_eq_rect_eq. 
  intro Hz. apply (G _ _ _ Hz eq_refl _ eq_refl). 
Qed.

Lemma eval_str n x z: eval n n (x^* ) z -> exists x', eval n n x x' /\ z = e_str x'.
Proof. 
  assert (G: forall m u (z: expr n m), eval n m u z -> 
    forall (H: n=m) x, u=e_str x -> 
      exists x', eval n n x x' /\ z = eq_rect _ (expr n) (e_str x') m H).
  intros m z' H. destruct 1; intros E v Hv; try discriminate. 
  rewrite <-(f_equal ((fun n m (e: syntax.expr _ _ n m) => 
    match e in syntax.expr _ _ n m return syntax.expr _ _ n m with e_str y => y | x => x end) _ _) Hv).
  eexists. split. eassumption. now rewrite cmp_eq_rect_eq. 
  intro Hz. apply (G _ _ _ Hz eq_refl _ eq_refl). 
Qed.

Lemma eval_var a z: eval (s a) (t a) (e_var a) z -> z=e_var a.
Proof. 
  assert (G: forall n m u (z: expr n m), eval n m u z -> 
    forall a (Hs: s a=n) (Ht: t a=m), u=e_var a -> 
      z = eq_rect _ (fun m => expr m _) (eq_rect _ (expr _) (e_var a) m Ht) n Hs).
  intros n m u z'. destruct 1; intros b Hs Ht E; try discriminate. 
  injection E. intros ->. now rewrite 2cmp_eq_rect_eq. 
  intro Hz. apply (G _ _ _ _ Hz _ eq_refl eq_refl eq_refl). 
Qed.

(** ** key lemma 3: injectivity of typing derivations 

   an untyped expression cannot be mapper to two terms of distinct
   types, for which either the sources or the targets coincide.  in
   other words, once the sources coincide, so do the targets, and
   conversely 

   (this lemma does not hold in presence of bottom elements)
*)

Lemma eval_types n n' m m' x x' x'':
  eval n m x x' -> eval n' m' x x'' -> (n=n' <-> m=m').
Proof.
  intro H. revert n' m' x''. induction H; intros n' m' x'' H''. 
   apply eval_one' in H''. subst. reflexivity. 
   apply eval_pls in H'' as (?&?&?&?&?). eauto. 
   apply eval_dot in H'' as (?&?&?&?&?&?). erewrite IHeval1 by eassumption. eauto.
   apply eval_itr' in H''. subst. reflexivity. 
   apply eval_str' in H''. subst. reflexivity. 
   apply eval_cnv in H'' as (?&?&?). symmetry. eauto. 
   apply eval_var' in H'' as (?&?). subst. now split. 
Qed.

Lemma eval_types_l n m m' x x' x'': eval n m x x' -> eval n m' x x'' -> m=m'.
Proof. intros H H'. now apply (eval_types H H'). Qed.

Lemma eval_types_r n m m' x x' x'': eval m n x x' -> eval m' n x x'' -> m=m'.
Proof. intros H H'. now apply (eval_types H H'). Qed.

(** we deduce that the [eval] predicate is functionnal once types are fixed *)
Lemma eval_fun n m x x' x'': eval n m x x' -> eval n m x x'' -> x'=x''.
Proof.
  induction 1; intro H'.
   now apply eval_one in H'.
   apply eval_pls in H' as (?&?&?&?&->). firstorder congruence.
   apply eval_dot in H' as (q&?&?&?&?&->). 
    assert(m=q) by eauto using eval_types_l. 
    subst. firstorder congruence.
   apply eval_itr in H' as (?&?&->). firstorder congruence.
   apply eval_str in H' as (?&?&->). firstorder congruence.
   apply eval_cnv in H' as (?&?&->). firstorder congruence.
   apply eval_var in H'. congruence.
Qed.

Section l.
Variable l: level.

(** ** main lemma *)

(** we use the same trick as above to perform a mutual induction on
   the [leq/weq] predicates (unfortunately, we cannot reuse the above
   lemmas since we need to do an induction on untyped equalities.) *)

(* TODO: factorise code, possibly by introducing explicitely an
   untyped syntax (and noting that the above cleaning function doesn't
   need to be typed) *)

(* this definition is well-suited to sup-semilattices, 
   we would need to take the dual one for inf-semilattice *)
Definition u_leq x y := 
  (forall n m y', eval n m y y' -> exists x', eval n m x x' /\ x' <==_[l] y').

Definition u_weq x y := 
  (forall n m x', eval n m x x' -> exists y', eval n m y y' /\ x' ==_[l] y')
  /\ (forall n m y', eval n m y y' -> exists x', eval n m x x' /\ x' ==_[l] y').

Definition u_lattice_ops := {|
  car := uexpr;
  leq := u_leq;
  weq := u_weq;
  cup := @e_pls _ _ _ _ _;
  bot := e_zer _ _; 
  (* below: these operations are not meaningful *)
  lattice.top := e_top _ _; 
  cap := @e_cap _ _ _ _ _; 
  neg := @e_neg _ _ _ _ _
|}.

Definition u_ops := {|
  ob  := unit;
  mor n m := u_lattice_ops;
  dot n m p := @e_dot _ _ _ _ _ _;
  one n := e_one _;
  itr n := @e_itr _ _ _ _;
  str n := @e_str _ _ _ _;
  cnv n m := @e_cnv _ _ _ _ _;
  (* below: these operations are not meaningful *)
  ldv n m p := @e_ldv _ _ _ _ _ _;
  rdv n m p := @e_rdv _ _ _ _ _ _
|}.


Ltac eval_inv := repeat
  (match goal with
     | H: eval ?n ?m ?x _, H': eval ?n ?m ?x _ |- _ => apply (eval_fun H) in H'
     | H: eval ?n _ ?x _, H': eval ?n _ ?x _ |- _ => pose proof (eval_types_l H H')
     | H: eval _ ?n ?x _, H': eval _ ?n ?x _ |- _ => pose proof (eval_types_r H H')
     | H: eval _ _ _ _ |- _ => first [
       apply eval_pls in H as (?&?&?&?&?) |
       apply eval_dot in H as (?&?&?&?&?&?) |
       apply eval_itr in H as (?&?&?) |
       apply eval_str in H as (?&?&?) |
       apply eval_cnv in H as (?&?&?) |
       apply eval_one in H |
       apply eval_var in H ]
     | H: eval _ _ 1 _ |- _ => pose proof (eval_one' H)
     | H: eval _ _ (_^+) _ |- _ => pose proof (eval_itr' H)
     | H: eval _ _ (_^* ) _ |- _ => pose proof (eval_str' H)
     | H: eval _ _ ?x _, H': u_leq _ ?x |- _ => 
       pose proof H; apply H' in H as (?&?&?); clear H'
     | H: eval _ _ ?x _, H': u_weq _ ?x |- _ => 
       pose proof H; apply H' in H as (?&?&?); clear H'
     | H: eval _ _ ?x _, H': u_weq ?x _ |- _ => 
       pose proof H; apply H' in H as (?&?&?); clear H'
   end; subst).
Ltac exists_eval := 
  simpl; try split; repeat intro; eval_inv;
  eexists; (split; [repeat constructor; eassumption|]).
Ltac not_involved Hl :=
  let H := fresh in intro H; apply (lower_trans _ _ _ H) in Hl; discriminate Hl. 


Instance u_lattice_laws {Hl: l<<CKA}: lattice.laws l u_lattice_ops.
Proof.
  constructor; try not_involved Hl. constructor.
   repeat intro; solve [eauto 6].
   exists_eval. etransitivity; eassumption.
   split. 
    exists_eval; hlattice. 
    simpl. intros [? ?]. exists_eval; lattice. 
   split. 
    exists_eval. eapply cup_spec. rewrite cupC. eassumption. eapply cup_spec; eassumption.
    simpl. intros [? ?]. exists_eval; lattice. 
  (* not that [bot] would work here, but [bot] breaks the unique typing property *)
Qed.

Instance u_laws {Hl: l<<CKA}: laws l u_ops.
Proof.
  constructor; try not_involved Hl; repeat right.
  intros. apply u_lattice_laws.
  exists_eval; apply dotA.
  exists_eval; apply dot1x.
  exists_eval; apply dotx1.
  exists_eval. apply dot_leq; assumption.
  exists_eval. apply weq_leq. apply dotplsx.
  exists_eval. apply weq_leq. apply dotxpls.
  exists_eval. apply weq_leq. apply cnvdot.
  exists_eval; apply cnv_invol.
  exists_eval. apply cnv_leq; assumption.
  exists_eval. apply cnv_ext.
  exists_eval. apply str_refl.
  exists_eval. apply str_cons.
  exists_eval. apply str_ind_l; assumption.
  exists_eval. apply str_ind_r; assumption.
  exists_eval; apply itr_str_l. 
Qed.

(** type erasing function: replace all types by a constant one (here, [xH]) *)
Definition erase: forall n m, expr n m -> uexpr := 
  @syntax.eval _ s t (expr_ops _ _ l) (fun _ => xH) (@e_var _ _ _). 

Lemma eval_erase: forall n m (x: expr n m), is_clean x -> eval n m (erase x) x.
Proof.
  induction x; simpl (is_clean _); intro Hl;
    try discriminate Hl; try constructor; 
      first [apply IHx1 | apply IHx2 | apply IHx | idtac]; tauto.
Qed.

Lemma syntax_eval_id n m (e: expr n m): 
  syntax.eval (X:=u_ops) (f':=fun _ => tt) (@e_var _ _ _) (erase e) = erase e.
Proof. induction e; simpl; unfold str; simpl; repeat f_equal; assumption. Qed.

(** untyping theorem for bottom-free structures *)
Theorem erase_faithful_leq_clean n m (x y: expr n m):
  is_clean x -> is_clean y -> l<<CKA ->
  erase x <==_[l] erase y -> x <==_[l] y.
Proof.
  intros Hx Hy Hl H. 
  assert (H': u_leq (erase x) (erase y)).
   rewrite <-(syntax_eval_id x), <-(syntax_eval_id y).
   apply (H u_ops), u_laws. 
  apply eval_erase in Hx. 
  apply eval_erase in Hy. 
  apply H' in Hy as (x'&Hx'&Hxy).
  now rewrite (eval_fun Hx Hx'). 
Qed.

End l. 


(** * Extension to structures with bottom element, by factorisation *)

Lemma is_zer_erase l n m (e: expr n m): is_zer (erase l e) = is_zer e.
Proof. destruct e; reflexivity. Qed.

Lemma clean_erase h k n m (e: expr n m): clean (erase h e) = erase k (clean e).
Proof.
  induction e; simpl; 
    unfold e_pls', e_dot', e_itr', e_str', e_pls', e_cnv'; simpl in *; trivial; 
      rewrite ?IHe1, ?IHe2, ?IHe, ?is_zer_erase; 
        repeat (case is_zer; trivial).
Qed.

Lemma level_erase l n m (e: expr n m): e_level (erase l e) = e_level e.
Proof. induction e; simpl in *; congruence. Qed.

Lemma erase_0 l n m (e: expr n m): erase l e = 0%ast -> e = 0%ast. 
Proof. destruct e; discriminate || reflexivity. Qed.

(** final untyping theorem for equalities *)
Theorem erase_faithful_leq l n m (x y: expr n m):
  e_level x + e_level y << l -> l<<BOT+CKA -> erase l x <==_[l] erase l y -> x <==_[l] y.
Proof.
  (* TODO: reprendre cette preuve immonde *)
  intros Hxy Hl H. 
  rewrite <-(clean_weq x), <-(clean_weq y) by solve_lower'.
  destruct (clean_spec x) as [Hx|Hx]. rewrite <-Hl; solve_lower'. 
   rewrite Hx. rewrite <-clean_0_level in Hxy by assumption. lattice.
  destruct (clean_spec y) as [Hy|Hy]. rewrite <-Hl; solve_lower'.
   rewrite Hy. apply clean_leq_0 in H. rewrite (clean_erase l l) in H. 
   apply erase_0 in H. now rewrite H. 
   assumption. 
   now rewrite (clean_erase l l), Hy. 
  set (l' :=                    (* l \ BOT *)
    mk_level (has_cup l) false (has_cap l) (has_top l) 
             (has_str l) (has_cnv l) (has_neg l) (has_div l)).
  assert (L: l' << l). rewrite lower_spec. intuition discriminate. 
  assert (L': l << BOT+l'). rewrite lower_spec. simpl. intuition. 
  assert (G: clean x <==_[l'] clean y). 
   apply erase_faithful_leq_clean.
    assumption.
    assumption.
    rewrite <-L in Hl. apply Hl. 
    rewrite <-2(clean_erase l l'). 
    destruct (fun Hl => clean_factorise_leq Hl (e_leq_weaken H)) as [H'|H']. 
     now rewrite L.
     rewrite (clean_erase l l) in H'. apply erase_0 in H'. rewrite H' in Hx. inversion Hx. 
     assumption. 
  apply e_leq_weaken, G. 
Qed.

(** final untyping theorem for (in)equalities *)
Corollary erase_faithful_weq l n m (x y: expr n m):
  e_level x + e_level y << l -> l<<BOT+CKA -> erase l x ==_[l] erase l y -> x ==_[l] y.
Proof.
  intros Hxy Hl. rewrite 2weq_spec. 
  split; apply erase_faithful_leq; intuition solve_lower'.
Qed.

End e.
