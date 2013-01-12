(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * lsyntax: syntactic model for types structures (monoid operations) *)

Require Export positives comparisons.
Require Import Eqdep. 
Require Import monoid.
Set Implicit Arguments.
Set Asymmetric Patterns.

(** * Free syntactic model *)

Section s.

Notation I := positive.
Variable A : Set.
(* [A=positive] for normalisation tactics 
   [A=positive+lsyntax.expr (ord n)] for KAT proofs
   [A=positive+lsyntax.expr positive] for KAT computations (not yet) *)
Variables s t: A -> I.

(** residuated Kleene allegory expressions over a set [A] of
   variables, the variables being typed according to the functions [s]
   (source) and [t] (target).  

   The indexing types ([I]) are fixed to be [positive] numbers: 
   - this is convenient and efficient in practice, for reification 
   - we need a decidable type to get the untyping theorems without axioms

   Note that we include constructors for flat operations
   (cup,cap,bot,top,neg): it is not convenient to reuse [lsyntax.expr]
   here since we would need to restrict the alphabet under those nodes to 
   something like [A_(n,m) = { a: A / s a = n /\ t a = m }].
*)

(* TOTHINK: add a phantom/strong dependency on [l] on the expr type ? *)
Inductive expr: I -> I -> Type := 
| e_zer: forall n m, expr n m
| e_top: forall n m, expr n m
| e_one: forall n, expr n n
| e_pls: forall n m, expr n m -> expr n m -> expr n m
| e_cap: forall n m, expr n m -> expr n m -> expr n m
| e_neg: forall n m, expr n m -> expr n m
(* | e_not: forall n, expr n n -> expr n n *)
| e_dot: forall n m p, expr n m -> expr m p -> expr n p
| e_itr: forall n, expr n n -> expr n n
| e_str: forall n, expr n n -> expr n n
| e_cnv: forall n m, expr n m -> expr m n
| e_ldv: forall n m p, expr n m -> expr n p -> expr m p
| e_rdv: forall n m p, expr m n -> expr p n -> expr p m
| e_var: forall a, expr (s a) (t a).

(** level of an expression: the set of operations that appear in that expression *)
Fixpoint e_level n m (x: expr n m): level :=
  match x with
    | e_zer _ _ => BOT
    | e_top _ _ => TOP
    | e_one _ => MIN
    | e_pls _ _ x y => CUP + e_level x + e_level y
    | e_cap _ _ x y => CAP + e_level x + e_level y
    | e_neg _ _ x => BL + e_level x 
      (* negation is ill-defined without the other Boolean operations, 
         whence the [BL] rather than [NEG] *)
    | e_dot _ _ _ x y => e_level x + e_level y
    | e_itr _ x => STR + e_level x
    | e_str _ x => STR + e_level x
    | e_cnv _ _ x => CNV + e_level x
    | e_ldv _ _ _ x y 
    | e_rdv _ _ _ x y => DIV + e_level x + e_level y
    | e_var a => MIN
  end%level.

Section e.
Context {X: ops} {f': I -> ob X}.
Variable f: forall a, X (f' (s a)) (f' (t a)).

(** interpretation of an expression into an arbitray structure, given
   an assignation [f] of the variables (and a interpretation function
   [f'] for the types) *)

Fixpoint eval n m (x: expr n m): X (f' n) (f' m) :=
  match x with
    | e_zer _ _ => 0
    | e_top _ _ => top
    | e_one _ => 1
    | e_pls _ _ x y => eval x + eval y
    | e_cap _ _ x y => eval x ^ eval y
    | e_neg _ _ x => ! eval x
    (* | e_not _ x => eval x ^~ *)
    | e_dot _ _ _ x y => eval x * eval y
    | e_itr _ x => eval x ^+
    | e_str _ x => eval x ^*
    | e_cnv _ _ x => eval x `
    | e_ldv _ _ _ x y => eval x -o eval y
    | e_rdv _ _ _ x y => eval y o- eval x
    | e_var a => f a
  end.
End e.

Section l.
Variable l: level.

(** * (In)equality of syntactic expressions. 

   Like in [lsyntax], we use an impredicative encoding to define
   (in)equality in the free syntactic model, and we parametrise all
   definition with the level [l] at which we want to interpret the
   given expressions. *)

Definition e_leq n m (x y: expr n m) := 
  forall X (L:laws l X) f' (f: forall a, X (f' (s a)) (f' (t a))), eval f x <== eval f y.
Definition e_weq n m (x y: expr n m) := 
  forall X (L:laws l X) f' (f: forall a, X (f' (s a)) (f' (t a))), eval f x == eval f y.

(** by packing syntactic expressions and the above predicates into a
   canonical structure for flat operations, and another one for the
   other operations, we get all notations for free *)

Canonical Structure expr_lattice_ops n m := {|
  car := expr n m;
  leq := @e_leq n m;
  weq := @e_weq n m;
  cup := @e_pls n m;
  cap := @e_cap n m;
  neg := @e_neg n m;
  bot := @e_zer n m;
  top := @e_top n m
|}.

Canonical Structure expr_ops := {|
  ob  := I;
  mor := expr_lattice_ops;
  dot := e_dot;
  one := e_one;
  itr := e_itr;
  str := e_str;
  cnv := e_cnv;
  ldv := e_ldv;
  rdv := e_rdv
|}.


(** we easily show that we get a model so that we immediately benefit
   from all lemmas about the various structures *)

Global Instance expr_lattice_laws n m: lattice.laws l (expr_lattice_ops n m).
Proof.
  constructor; try right. constructor.
   intros x X L u f. reflexivity.
   intros x y z H H' X L u f. transitivity (eval f y); auto.
   intros x y. split. 
    intro H. split; intros X L u f. now apply weq_leq, H. now apply weq_geq, H.
    intros [H H'] X L u f. apply antisym; auto.
   intros Hl x y z. split. 
    intro H. split; intros X L u f; specialize (H X L u f); simpl in H; hlattice. 
    intros [H H'] X L u f. simpl. apply cup_spec; auto.
   intros Hl x y z. split. 
    intro H. split; intros X L u f; specialize (H X L u f); simpl in H; hlattice. 
    intros [H H'] X L u f. simpl. apply cap_spec; auto.
   intros x X L u f. apply leq_bx.
   intros x X L u f. apply leq_xt.
   intros Hl x y z X L u f. apply cupcap_.
   intros Hl x X L u f. apply capneg.
   intros Hl x X L u f. apply cupneg.
Qed.

Global Instance expr_laws: laws l expr_ops.
Proof.
  constructor; repeat right; repeat intro; simpl.
   apply expr_lattice_laws.
   apply dotA.
   apply dot1x.
   apply dotx1.
   apply dot_leq; auto.
   now rewrite dotplsx.
   now rewrite dotxpls.
   now rewrite dot0x.
   now rewrite dotx0.
   apply cnvdot_.
   apply cnv_invol.
   apply cnv_leq. now refine (H0 _ _ _ _).
   apply cnv_ext.
   apply str_refl.
   apply str_cons.
   apply str_ind_l. now refine (H0 _ _ _ _).
   apply str_ind_r. now refine (H0 _ _ _ _).
   apply itr_str_l. 
   apply capdotx.
   split; intros E X L f' f; intros; simpl; apply ldv_spec, (E X L f' f). 
   split; intros E X L f' f; intros; simpl; apply rdv_spec, (E X L f' f). 
Qed.

End l.


(** * Testing for particular constants *)

Definition is_zer n m (x: expr n m) :=  
  match x with e_zer _ _ => true | _ => false end.

Definition is_top n m (x: expr n m) := 
  match x with e_top _ _ => true | _ => false end.

Inductive is_case n m (k x: expr n m): expr n m -> bool -> Prop :=
| is_case_true: x=k -> is_case k x k true
| is_case_false: x<>k -> is_case k x x false.

Lemma is_zer_spec n m (x: expr n m): is_case (e_zer n m) x x (is_zer x). 
Proof. destruct x; constructor; discriminate || reflexivity. Qed.

Lemma is_top_spec n m (x: expr n m): is_case (e_top n m) x x (is_top x). 
Proof. destruct x; constructor; discriminate || reflexivity. Qed.

(** casting the type of an expression *)
Definition cast n m n' m' (Hn: n=n') (Hm: m=m') (x: expr n m): expr n' m' :=  
  eq_rect n (fun n => expr n m') (eq_rect m (expr n) x _ Hm) _ Hn.

End s.
Arguments e_var [A s t] a.
Arguments e_one [A s t] n.
Arguments e_zer [A s t] n m.
Arguments e_top [A s t] n m.

Bind Scope ast_scope with expr.
Delimit Scope ast_scope with ast.

(** additional notations, to specify explicitly at which level
   expressions are considered, or to work directly with the
   bare constructors (by opposition with the encapsulated ones, 
   through monoid.ops) *)

Notation expr_ l s t n m := (expr_ops s t l n m).
Notation "x <==_[ l ] y" := (@leq (expr_ops _ _ l _ _) x y) (at level 79): ra_scope.
Notation "x ==_[ l ] y" := (@weq (expr_ops _ _ l _ _) x y) (at level 79): ra_scope.

Infix "+" := e_pls: ast_scope.
Infix "^" := e_cap: ast_scope.
Infix "*" := e_dot: ast_scope.
Notation "1" := (e_one _): ast_scope.
Notation "0" := (e_zer _ _): ast_scope.
Notation top := (e_top _ _).
Notation "x ^+" := (e_itr x): ast_scope.
Notation "x `"  := (e_cnv x): ast_scope.
Notation "x ^*" := (e_str x): ast_scope.
Notation "! x"  := (e_neg x): ast_scope.
Notation "x -o y" := (e_ldv x y) (right associativity, at level 60): ast_scope. 
Notation "y o- x" := (e_rdv x y) (left associativity, at level 61): ast_scope. 



(** * weakening (in)equations *)
(** any equation holding at some level holds at all higher levels  *)

Lemma e_leq_weaken {h k} {Hl: h<<k} A s t n m (x y: @expr A s t n m): 
  x <==_[h] y -> x <==_[k] y. 
Proof. intros H X L f' f. eapply @H, lower_laws. Qed.

Lemma e_weq_weaken {h k} {Hl: h<<k} A s t n m (x y: @expr A s t n m): 
  x ==_[h] y -> x ==_[k] y. 
Proof. intros H X L f' f. eapply @H, lower_laws. Qed.



(** * comparing expressions syntactically  *)
Section expr_cmp.

Notation I := positive.
Context {A : cmpType}.
Variables s t: A -> I.
Notation expr := (expr s t).

(** we need to generalise the comparison function to expressions of
   distinct types because of Coq's dependent types *)
Fixpoint expr_compare n m (x: expr n m) p q (y: expr p q) :=
  match x,y with
    | e_zer _ _, e_zer _ _ 
    | e_top _ _, e_top _ _  
    | e_one _, e_one _ => Eq
    | e_var a, e_var b => cmp a b
    | e_pls _ _ x x', e_pls _ _ y y' 
    | e_cap _ _ x x', e_cap _ _ y y' => 
         lex (expr_compare x y) (expr_compare x' y')
    | e_dot _ u _ x x', e_dot _ v _ y y' 
    | e_ldv u _ _ x x', e_ldv v _ _ y y' 
    | e_rdv u _ _ x x', e_rdv v _ _ y y' => 
         lex (cmp u v) (lex (expr_compare x y) (expr_compare x' y'))
    | e_neg _ _ x, e_neg _ _ y
    | e_itr _ x, e_itr _ y
    | e_str _ x, e_str _ y
    | e_cnv _ _ x, e_cnv _ _ y => expr_compare x y
    | e_zer _ _, _       => Lt
    | _, e_zer _ _       => Gt
    | e_one _, _         => Lt
    | _, e_one _         => Gt
    | e_top _ _, _       => Lt
    | _, e_top _ _       => Gt
    | e_var _, _         => Lt
    | _, e_var _         => Gt
    | e_itr _ _, _       => Lt
    | _, e_itr _ _       => Gt
    | e_str _ _, _       => Lt
    | _, e_str _ _       => Gt
    | e_cnv _ _ _, _     => Lt
    | _, e_cnv _ _ _     => Gt
    | e_ldv _ _ _ _ _, _ => Lt
    | _, e_ldv _ _ _ _ _ => Gt
    | e_rdv _ _ _ _ _, _ => Lt
    | _, e_rdv _ _ _ _ _ => Gt
    | e_pls _ _ _ _, _   => Lt
    | _, e_pls _ _ _ _   => Gt
    | e_cap _ _ _ _, _   => Lt
    | _, e_cap _ _ _ _   => Gt
    | e_neg _ _ _, _     => Lt
    | _, e_neg _ _ _     => Gt
  end.

(** since [A] is decidable, [cast] provably acts as an identity  *)
Lemma cast_eq n m (x: expr n m) (H: n=n) (H': m=m): cast H H' x = x.
Proof. unfold cast. now rewrite 2 cmp_eq_rect_eq. Qed.

(** auxiliary lemma for [expr_compare_spec] below, using dependent equality *)
Lemma expr_compare_eq_dep n m (x: expr n m): forall p q (y: expr p q), 
  expr_compare x y = Eq -> n=p -> m=q -> 
  eq_dep (I*I) (fun x => expr (fst x) (snd x)) (n,m) x (p,q) y.
Proof.
  induction x; intros ? ? z C; destruct z; try discriminate C; 
    try (intros <- <- || intros <- _); try reflexivity;
     simpl expr_compare in C.

   apply compare_lex_eq in C as [C1 C2].
   apply IHx1, cmp_eq_dep_eq in C1; trivial. 
   apply IHx2, cmp_eq_dep_eq in C2; trivial.
   subst. reflexivity. 

   apply compare_lex_eq in C as [C1 C2].
   apply IHx1, cmp_eq_dep_eq in C1; trivial. 
   apply IHx2, cmp_eq_dep_eq in C2; trivial.
   subst. reflexivity. 

   apply IHx, cmp_eq_dep_eq in C; trivial. subst. reflexivity. 

   apply compare_lex_eq in C as [C C']. apply cmp_eq in C. subst. 
   apply compare_lex_eq in C' as [C1 C2].
   apply IHx1, cmp_eq_dep_eq in C1; trivial. 
   apply IHx2, cmp_eq_dep_eq in C2; trivial.
   subst. reflexivity. 

   apply IHx, cmp_eq_dep_eq in C; trivial. subst. reflexivity. 

   apply IHx, cmp_eq_dep_eq in C; trivial. subst. reflexivity. 

   apply IHx, cmp_eq_dep_eq in C; trivial. subst. reflexivity. 

   apply compare_lex_eq in C as [C C']. apply cmp_eq in C. subst. 
   apply compare_lex_eq in C' as [C1 C2].
   apply IHx1, cmp_eq_dep_eq in C1; trivial. 
   apply IHx2, cmp_eq_dep_eq in C2; trivial.
   subst. reflexivity. 

   apply compare_lex_eq in C as [C C']. apply cmp_eq in C. subst. 
   apply compare_lex_eq in C' as [C1 C2].
   apply IHx1, cmp_eq_dep_eq in C1; trivial. 
   apply IHx2, cmp_eq_dep_eq in C2; trivial.
   subst. reflexivity. 

   apply cmp_eq in C. subst. reflexivity. 
Qed.

Lemma expr_compare_eq n m (x y: expr n m): x=y -> expr_compare x y = Eq. 
Proof.
  intros <-. induction x; simpl expr_compare; trivial; 
  rewrite ?compare_lex_eq, ?cmp_refl; tauto.
Qed.

(** final specification of the comparison function *)
Lemma expr_compare_spec n m (x y: expr n m): compare_spec (x=y) (expr_compare x y). 
Proof. 
  generalize (fun H => expr_compare_eq_dep x y H eq_refl eq_refl) as H.
  generalize (@expr_compare_eq _ _ x y) as H'.
  case (expr_compare x y); intros H' H; constructor.
   now apply cmp_eq_dep_eq in H.
   intro E. now discriminate H'. 
   intro E. now discriminate H'. 
Qed.

(** packaging as a [cmpType]  *)
Definition expr_compare_ n m (x y: expr n m) := expr_compare x y.
Canonical Structure cmp_expr n m := mk_simple_cmp (@expr_compare_ n m) (@expr_compare_spec n m).

End expr_cmp.



(** * Packages for typed reification *)

(** according to the interpretation function [eval], (typed)
   reification has to provide a set [A] for indexing variables, and four maps:
   - [f': I -> ob X], to interpret types as written in the expressions ([I=positive])
   - [s] and [t]: A -> I, to specify the source and target types of each variable
   - [f: forall a: A, expr s t (s a) (t a)], to interpret each variable

   [A] is also fixed to be [positive], so that we can use simple and
   efficient positive maps, but the fact that [f] has a dependent type
   is not convenient.

   This is why we introduce the additionnal layer, to ease the
   definition of such maps: thanks to the definitions below, it
   suffices to provide the map [f'], and a map [f: A -> Pack X f']. *)

Record Pack (X: ops) (f': positive -> ob X) := pack {
  src: positive;
  tgt: positive;
  val: X (f' src) (f' tgt)
}.

Definition packed_eval (X: ops) (f': positive -> ob X) (f: positive -> Pack X f') := 
  eval (fun a => val (f a)) : forall n m, expr _ _ n m -> X (f' n) (f' m) . 

(** these projections are used to build the reified expressions *)
Definition src_ (X: ops) (f': positive -> ob X) (f: positive -> Pack X f') a := src (f a).
Definition tgt_ (X: ops) (f': positive -> ob X) (f: positive -> Pack X f') a := tgt (f a).


(** loading ML reification module *)
Declare ML Module "ra_reification". 
