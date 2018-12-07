(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * monoid: typed structures, from ordered monoids to residuated Kleene allegories *)

(** We define here all (typed) structures ranging from partially
   ordered monoids to residuated Kleene allegories *)

Require Export lattice.

(** * Monoid operations *)

(** The following class packages an ordered typed monoid (i.e., a
   category enriched over a partial order) together with all kinds of
   operations it can come with: iterations, converse, residuals. We
   use dummy values when working in structures lacking some
   operations.

   Like for [lattice.ops], we use a Class but we mainly exploit
   Canonical structures inference mechanism. *)

Universe M.

Class ops := mk_ops {
  ob: Type@{M};                     (** objects of the category *)
  mor: ob -> ob -> lattice.ops; (** morphisms (each homset is a partially ordered structure) *)
  dot: forall n m p, mor n m -> mor m p -> mor n p; (** composition  *)
  one: forall n, mor n n;                           (** identity *)
  itr: forall n, mor n n -> mor n n;                (** strict iteration (transitive closure) *)
  str: forall n, mor n n -> mor n n;                (** Kleene star (reflexive transitive closure) *)
  cnv: forall n m, mor n m -> mor m n;              (** converse (transposed relation) *)
  ldv: forall n m p, mor n m -> mor n p -> mor m p; (** left residual/factor/division  *)
  rdv: forall n m p, mor m n -> mor p n -> mor p m  (** right residual/factor/division *)
}.
Coercion mor: ops >-> Funclass.
Arguments ob : clear implicits.

(** Hints for simpl *)
Arguments mor {ops} n m / : simpl nomatch.
Arguments dot {ops} n m p (x y)%ra / : simpl nomatch.
Arguments one {ops} n / : simpl nomatch.
Arguments itr {ops} n (x)%ra / : simpl nomatch.
Arguments str {ops} n (x)%ra / : simpl nomatch.
Arguments cnv {ops} n m (x)%ra / : simpl nomatch.
Arguments ldv {ops} n m p (x y)%ra / : simpl nomatch.
Arguments rdv {ops} n m p (x y)%ra / : simpl nomatch.

(** Notations (note that "+" and "∩" are just specialisations of the
   notations "⊔" and "⊓", when these operations actually come
   from a monoid) *)

(**
   ∩ : \cap (company-coq) or INTERSECTION (0x2229)

   ⋅ : \cdot (company coq) or DOT OPERATOR (0x22c5)
*)

Notation "x ⋅ y" := (dot _ _ _ x y) (left associativity, at level 25, format "x ⋅ y"): ra_terms.
Notation "x + y" := (@cup (mor _ _) x y) (left associativity, at level 50): ra_terms.
Notation "x ∩ y" := (@cap (mor _ _) x y) (left associativity, at level 40): ra_terms. 
Notation "1" := (one _): ra_terms.
Notation zer n m := (@bot (mor n m)).
Notation top' n m := (@top (mor n m)) (only parsing).
Notation "0" := (zer _ _): ra_terms.
Notation "x °"  := (cnv _ _ x) (left associativity, at level 5, format "x °"): ra_terms.
Notation "x ^+" := (itr _ x)   (left associativity, at level 5, format "x ^+"): ra_terms.
Notation "x ^*" := (str _ x)   (left associativity, at level 5, format "x ^*"): ra_terms.
Notation "x -o y" := (ldv _ _ _ x y) (right associativity, at level 60): ra_terms. 
Notation "y o- x" := (rdv _ _ _ x y) (left associativity, at level 61): ra_terms. 

(** Like for [lattice.ops], we declare most projections as Opaque for
   typeclass resolution, to save on compilation time. *)
Typeclasses Opaque (* ob mor *) dot one str cnv ldv rdv.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Monoid laws (axioms) *)

(** [laws l X] provides the laws corresponding to the various
   operations of [X], provided these operations belong to the level
   [l]. For instance, the specification of Kleene star ([str]) is
   available only if the level contains [STR].

   Note that [l] indirectly specifies which lattice operations are
   available on each homset, via the field [lattice_laws]. We add
   additional properties when needed (e.g., [dotplsx_]: composition
   ([dot]) distribute over sums ([pls]), provided there are sums)

   The partially ordered categorical structure (leq,weq,dot,one) is
   always present.

   Like for [lattices.laws], some axioms end with an underscore,
   either because they can be strengthened to an equality (e.g.,
   [cnvdot_]), or because they become derivable in presence of other
   axiomes (e.g., [dotx1_]), or both (e.g., [dotplsx_]).

   Unlike for operations ([ops]), laws are actually inferred by
   typeclass resolution. *)

Class laws (l: level) (X: ops) := {
  lattice_laws:>       forall n m, lattice.laws l (X n m);
  (** po-monoid laws *)
  dotA:                forall n m p q (x: X n m) y (z: X p q), x⋅(y⋅z) ≡ (x⋅y)⋅z;
  dot1x:               forall n m (x: X n m), 1⋅x ≡ x;
  dotx1_:              CNV ≪ l \/ forall n m (x: X m n), x⋅1 ≡ x;
  dot_leq_:            DIV ≪ l \/ forall n m p, Proper (leq ==> leq ==> leq) (dot n m p);
  (** slo-monoid laws (distribution of ⋅ over + and 0) *)
  dotplsx_  `{CUP ≪ l}: DIV ≪ l \/ forall n m p (x y: X n m) (z: X m p), (x+y)⋅z ≦ x⋅z+y⋅z;
  dotxpls_  `{CUP ≪ l}: DIV ≪ l \/ CNV ≪ l \/ forall n m p (x y: X m n) (z: X p m), z⋅(x+y) ≦ z⋅x+z⋅y;
  dot0x_    `{BOT ≪ l}: DIV ≪ l \/ forall n m p (x: X m p), 0⋅x ≦ zer n p;
  dotx0_    `{BOT ≪ l}: DIV ≪ l \/ CNV ≪ l \/ forall n m p (x: X p m), x⋅0 ≦ zer p n;
  (** converse laws *)
  cnvdot_   `{CNV ≪ l}: forall n m p (x: X n m) (y: X m p), (x⋅y)° ≦ y°⋅x°;
  cnv_invol `{CNV ≪ l}: forall n m (x: X n m), x°° ≡ x;
  cnv_leq   `{CNV ≪ l}:>forall n m, Proper (leq ==> leq) (cnv n m);
  cnv_ext_  `{CNV ≪ l}: CAP ≪ l \/ forall n m (x: X n m), x ≦ x⋅x°⋅x;
  (** star laws *)
  str_refl  `{STR ≪ l}: forall n (x: X n n), 1 ≦ x^*;
  str_cons  `{STR ≪ l}: forall n (x: X n n), x⋅x^* ≦ x^*;
  str_ind_l `{STR ≪ l}: forall n m (x: X n n) (z: X n m), x⋅z ≦ z -> x^*⋅z ≦ z;
  str_ind_r_`{STR ≪ l}: DIV ≪ l \/ CNV ≪ l \/ forall n m (x: X n n) (z: X m n), z⋅x ≦ z -> z⋅x^* ≦ z;
  itr_str_l `{STR ≪ l}: forall n (x: X n n), x^+ ≡ x⋅x^*;
  (** modularity law *)
  capdotx   `{AL ≪ l}: forall n m p (x: X n m) (y: X m p) (z: X n p), (x⋅y) ∩ z ≦ x⋅(y ∩ (x°⋅z));
  (** left and right residuals *)
  ldv_spec  `{DIV ≪ l}: forall n m p (x: X n m) (y: X n p) z, z ≦ x -o y <-> x⋅z ≦ y;
  rdv_spec  `{DIV ≪ l}: forall n m p (x: X m n) (y: X p n) z, z ≦ y o- x <-> z⋅x ≦ y
}.


(** * Basic properties *)

Instance dot_leq `{laws}: forall n m p, Proper (leq ==> leq ==> leq) (dot n m p). 
Proof.
  destruct dot_leq_. 2: assumption. 
  intros n m p x x' Hx y y' Hy. 
  rewrite <-rdv_spec, Hx, rdv_spec. 
  rewrite <-ldv_spec, Hy, ldv_spec. 
  reflexivity.
Qed.

Instance dot_weq `{laws} n m p: Proper (weq ==> weq ==> weq) (dot n m p) := op_leq_weq_2.


(** ** Basic properties of the converse operation *)

Instance cnv_weq `{laws} `{CNV ≪ l} n m: Proper (weq ==> weq) (cnv n m) := op_leq_weq_1.

Lemma cnv_leq_iff `{laws} `{CNV ≪ l} n m (x y: X n m): x° ≦ y° <-> x ≦ y. 
Proof. split. intro E. apply cnv_leq in E. now rewrite 2cnv_invol in E. apply cnv_leq. Qed.
Lemma cnv_leq_iff' `{laws} `{CNV ≪ l} n m (x: X n m) y: x ≦ y° <-> x° ≦ y. 
Proof. now rewrite <- cnv_leq_iff, cnv_invol. Qed.

Lemma cnv_weq_iff `{laws} `{CNV ≪ l} n m (x y: X n m): x° ≡ y° <-> x ≡ y. 
Proof. now rewrite 2weq_spec, 2cnv_leq_iff. Qed.
Lemma cnv_weq_iff' `{laws} `{CNV ≪ l} n m (x: X n m) y: x ≡ y° <-> x° ≡ y. 
Proof. now rewrite <-cnv_weq_iff, cnv_invol. Qed.

(** simple tactic to move converse from one side to the other of an (in)equation *)
Ltac cnv_switch := first [
  rewrite cnv_leq_iff |
  rewrite cnv_leq_iff' |
  rewrite <-cnv_leq_iff' |
  rewrite <-cnv_leq_iff |
  rewrite cnv_weq_iff |
  rewrite cnv_weq_iff' |
  rewrite <-cnv_weq_iff' |
  rewrite <-cnv_weq_iff ].

Lemma cnvdot `{laws} `{CNV ≪ l} n m p (x: X n m) (y: X m p): (x⋅y)° ≡ y°⋅x°.
Proof. apply antisym. apply cnvdot_. cnv_switch. now rewrite cnvdot_, 2cnv_invol. Qed.

Lemma cnv1 `{laws} `{CNV ≪ l} n: (one n)° ≡ 1.
Proof. rewrite <- (dot1x (1°)). cnv_switch. now rewrite cnvdot, cnv_invol, dot1x. Qed.

Lemma cnvpls `{laws} `{CNV+CUP ≪ l} n m (x y: X n m): (x+y)° ≡ x°+y°.
Proof.
  apply antisym.
  cnv_switch. apply leq_cupx; cnv_switch; lattice.
  apply leq_cupx; cnv_switch; lattice.
Qed.

Lemma cnvcap `{laws} `{AL ≪ l} n m (x y: X n m): (x ∩ y)° ≡ x° ∩ y°.
Proof.
  apply antisym. 
  apply leq_xcap; apply cnv_leq; lattice.
  cnv_switch. apply leq_xcap; cnv_switch; lattice.
Qed.

Lemma cnv0 `{laws} `{CNV+BOT ≪ l} n m: (zer n m)° ≡ 0.
Proof. apply antisym; [cnv_switch|]; apply leq_bx. Qed.

Lemma cnvtop `{laws} `{CNV+TOP ≪ l} n m: (top: X n m)° ≡ top.
Proof. apply antisym; [|cnv_switch]; apply leq_xt. Qed.

Lemma cnvneg `{laws} `{CNV+BL ≪ l} n m (x: X n m): (neg x)° ≡ neg (x°).
Proof.
  apply neg_unique. 
  rewrite <-cnvpls, cupC, cupneg. now rewrite cnvtop.
  rewrite <-cnvcap, capC, capneg. now rewrite cnv0.
Qed.


(** ** Basic properties of composition *)

Lemma dotx1 `{laws} n m (x: X m n): x⋅1 ≡ x.
Proof. destruct dotx1_; trivial. cnv_switch. now rewrite cnvdot, cnv1, dot1x. Qed.

Lemma dotplsx `{laws} `{CUP ≪ l} n m p (x y: X n m) (z: X m p): (x+y)⋅z ≡ x⋅z+y⋅z.
Proof. 
  apply antisym. 2: apply leq_cupx; apply dot_leq; lattice. 
  destruct dotplsx_ as [Hl|E]. 2: apply E.
  rewrite <-rdv_spec. apply leq_cupx; rewrite rdv_spec; lattice.
Qed.

Lemma dotxpls `{laws} `{CUP ≪ l} n m p (x y: X m n) (z: X p m): z⋅(x+y) ≡ z⋅x+z⋅y.
Proof. 
  apply antisym. 2: apply leq_cupx; apply dot_leq; lattice. 
  destruct dotxpls_ as [Hl|[Hl|E]]. 
   rewrite <-ldv_spec. apply leq_cupx; rewrite ldv_spec; lattice.
   cnv_switch. rewrite cnvpls,3cnvdot,cnvpls. apply weq_leq, dotplsx. 
  apply E. 
Qed.
  
Lemma dot0x `{laws} `{BOT ≪ l} n m p (x: X m p): 0⋅x ≡ zer n p.
Proof.
  apply antisym. 2: apply leq_bx. 
  destruct dot0x_ as [Hl|E]. 2: apply E. 
  rewrite <-rdv_spec. apply leq_bx.
Qed.

Lemma dotx0 `{laws} `{BOT ≪ l} n m p (x: X p m): x⋅0 ≡ zer p n.
Proof. 
  apply antisym. 2: apply leq_bx. 
  destruct dotx0_ as [Hl|[Hl|E]]. 
   rewrite <-ldv_spec. apply leq_bx.
   cnv_switch. rewrite cnvdot,2cnv0. apply weq_leq, dot0x.
  apply E.
Qed.

Lemma dotxcap `{laws} `{CAP ≪ l} n m p (x: X n m) (y z: X m p): 
  x ⋅ (y ∩ z) ≦ (x⋅y) ∩ (x⋅z). 
Proof. apply leq_xcap; apply dot_leq; lattice. Qed.

Lemma cnv_ext `{laws} `{CNV ≪ l} n m (x: X n m): x ≦ x⋅x°⋅x.
Proof. 
  destruct cnv_ext_; trivial.
  transitivity ((x⋅1) ∩ x). rewrite dotx1. lattice.
  rewrite capdotx, <-dotA. apply dot_leq; lattice.
Qed.

Lemma capxdot `{laws} `{AL ≪ l} n m p (x: X m n) (y: X p m) (z: X p n):
  (y⋅x) ∩ z ≦ (y ∩ (z⋅x°))⋅x.
Proof. cnv_switch. now rewrite cnvdot, 2cnvcap, 2cnvdot, capdotx. Qed.


(** ** Basic properties of left division *)

(** only those properties that are required to derive [str_ind_r] out
   of divisions, see module [factor] for other properties *)

Lemma ldv_cancel `{laws} `{DIV ≪ l} n m p (x: X n m) (y: X n p): x⋅(x -o y) ≦ y.
Proof. now rewrite <-ldv_spec. Qed.

Lemma ldv_trans `{laws} `{DIV ≪ l} n m p q (x: X n m) (y: X n p) (z: X n q): 
  (x -o y)⋅(y -o z) ≦ x -o z.
Proof. now rewrite ldv_spec, dotA, 2ldv_cancel. Qed.

Lemma leq_ldv `{laws} `{DIV ≪ l} n m (x y: X n m): x ≦ y <-> 1 ≦ x -o y. 
Proof. now rewrite ldv_spec, dotx1. Qed.

Lemma ldv_xx `{laws} `{DIV ≪ l} n m (x: X n m): 1 ≦ x -o x.
Proof. now rewrite <-leq_ldv. Qed.

Instance ldv_leq `{laws} `{DIV ≪ l} n m p: Proper (leq --> leq ++> leq) (ldv n m p).
Proof. intros x x' Hx y y' Hy. now rewrite ldv_spec, <-Hx, <-Hy, <-ldv_spec. Qed.

Instance ldv_weq `{laws} `{DIV ≪ l} n m p: Proper (weq ==> weq ==> weq) (ldv n m p).
Proof. simpl. setoid_rewrite weq_spec. split; apply ldv_leq; tauto. Qed.

Lemma cnvldv `{laws} `{CNV+DIV ≪ l} n m p (x: X n m) (y: X n p): (x -o y)° ≡ y° o- x°.
Proof.
  apply from_below. intro z. 
  cnv_switch. rewrite ldv_spec.
  cnv_switch. rewrite cnvdot, cnv_invol. 
  now rewrite rdv_spec. 
Qed.


(** ** Schroeder rules  *)
Lemma Schroeder_  `{laws} `{BL+CNV ≪ l} n m p (x : X n m) (y : X m p) (z : X n p): 
  x°⋅!z ≦ !y -> x⋅y ≦ z.
Proof.
  intro E. apply leq_cap_neg in E. rewrite negneg in E. 
  apply leq_cap_neg. now rewrite capdotx, capC, E, dotx0. 
Qed.
  
Lemma Schroeder_l `{laws} `{BL+CNV ≪ l} n m p (x : X n m) (y : X m p) (z : X n p): 
  x⋅y ≦ z <-> x°⋅!z ≦ !y. 
Proof.
  split. 2: apply Schroeder_. intro.
  apply Schroeder_. now rewrite 2negneg, cnv_invol. 
Qed.


(** ** Basic properties of Kleene star *)
(** (more properties in [kleene]) *)

Lemma str_ext `{laws} `{STR ≪ l} n (x: X n n): x ≦ x^*.
Proof. now rewrite <-str_cons, <-str_refl, dotx1. Qed.

Lemma str_ind_l' `{laws} `{STR ≪ l} n m (x: X n n) (y z: X n m): y ≦ z -> x⋅z ≦ z -> x^*⋅y ≦ z.
Proof. intro E. rewrite E. apply str_ind_l. Qed.

Lemma str_ind_l1 `{laws} `{STR ≪ l} n (x z: X n n): 1 ≦ z -> x⋅z ≦ z -> x^* ≦ z.
Proof. rewrite <-(dotx1 (x^*)). apply str_ind_l'. Qed.

Instance str_leq `{laws} `{STR ≪ l} n: Proper (leq ==> leq) (str n).
Proof.
  intros x y E. apply str_ind_l1. apply str_refl. 
  rewrite E. apply str_cons.
Qed.

Instance str_weq `{laws} `{STR ≪ l} n: Proper (weq ==> weq) (str n) := op_leq_weq_1.

Lemma str_snoc `{laws} `{STR ≪ l} n (x: X n n): x^*⋅x ≦ x^*.
Proof. apply str_ind_l'. apply str_ext. apply str_cons. Qed.

Lemma str_unfold_l `{laws} `{KA ≪ l} n (x: X n n): x^* ≡ 1+x⋅x^*.
Proof. 
  apply antisym. apply str_ind_l1. lattice. 
  rewrite dotxpls. apply leq_cupx. rewrite <-str_refl. lattice.
  rewrite <-str_cons at 2. lattice.
  rewrite str_cons, (str_refl x). lattice.
Qed. 

Lemma str_itr `{laws} `{KA ≪ l} n (x: X n n): x^* ≡ 1+x^+.
Proof. rewrite itr_str_l. apply str_unfold_l. Qed.

Lemma cnvstr_ `{laws} `{CNV+STR ≪ l} n (x: X n n): x^*° ≦ x°^*.
Proof.
  cnv_switch. apply str_ind_l1. now rewrite <-str_refl, cnv1.  
  cnv_switch. rewrite cnvdot, cnv_invol. apply str_snoc. 
Qed.

Lemma str_ldv_ `{laws} `{STR+DIV ≪ l} n m (x: X m n): (x -o x)^* ≦ x -o x.
Proof. apply str_ind_l1. apply ldv_xx. apply ldv_trans. Qed.

Lemma str_ind_r `{laws} `{STR ≪ l} n m (x: X n n) (z: X m n): z⋅x ≦ z -> z⋅x^* ≦ z.
Proof. 
  destruct str_ind_r_ as [Hl|[Hl|?]]. 3: auto. 
  - rewrite <-2ldv_spec. intro E. apply str_leq in E. rewrite E. apply str_ldv_.
  - intros. cnv_switch. rewrite cnvdot, cnvstr_. 
    apply str_ind_l; cnv_switch; now rewrite cnvdot, 2cnv_invol.
Qed.

Lemma itr_move `{laws} `{STR ≪ l} n (x: X n n): x ⋅ x^* ≡ x^* ⋅ x.
Proof.
  apply antisym. 
   rewrite <-dot1x, (str_refl x), dotA. apply str_ind_r. now rewrite str_snoc at 1. 
   apply str_ind_l'. now rewrite <-str_refl, dotx1. now rewrite str_cons at 1.
Qed.

Lemma itr_str_r `{laws} `{STR ≪ l} n (x: X n n): x^+ ≡ x^* ⋅ x.
Proof. rewrite itr_str_l. apply itr_move. Qed.


(** * Subtyping / weakening *)  

(** laws that hold at any level [h] hold for all level [k ≪ h]  *)
Lemma lower_laws {h k} {X} {H: laws h X} {le: k ≪ h}: laws k X.
Proof. 
  constructor; [ intros; apply lower_lattice_laws | .. ]; 
    try solve [ apply H | intro; apply H; eauto using lower_trans ].
  right. apply dotx1. 
  right. apply dot_leq. 
  intro H'. right. intros. apply weq_leq. apply (lower_trans _ _ _ H') in le. apply dotplsx.
  intro H'. right. right. intros. apply weq_leq. apply (lower_trans _ _ _ H') in le. apply dotxpls.
  intro H'. right. intros. apply weq_leq. apply (lower_trans _ _ _ H') in le. apply dot0x.
  intro H'. right. right. intros. apply weq_leq. apply (lower_trans _ _ _ H') in le. apply dotx0.
  intro H'. right. intros. apply (lower_trans _ _ _ H') in le. apply cnv_ext.
  intro H'. right. right. apply (lower_trans _ _ _ H') in le. apply str_ind_r.
Qed.


(** * Reasoning by duality *)

(** dual monoid operations: we reverse all arrows (or morphisms), swap
   the arguments of [dot], and swap left and right residuals.

   Note that this corresponds to categorical duality, not to be
   confused with lattice duality, as defined in [lattice.dual]. *)
Definition dual (X: ops) := {|
  ob := ob X;
  mor n m := X m n;
  dot n m p x y := y⋅x;
  one := one;
  cnv n m := cnv m n;
  itr := itr;
  str := str;
  ldv := rdv;
  rdv := ldv
|}.
Notation "X ^op" := (dual X) (at level 1): ra_scope.

(** laws on a given structure can be transferred to the dual one *)
Lemma dual_laws l X (L: laws l X): laws l X^op.
Proof.
  constructor; simpl; repeat right; intros.
   apply lattice_laws.
   symmetry. apply dotA.
   apply dotx1.
   apply dot1x.
   now apply dot_leq.
   apply weq_leq, dotxpls.
   apply weq_leq, dotplsx.
   apply weq_leq, dotx0.
   apply weq_leq, dot0x.
   apply weq_leq, cnvdot.
   apply cnv_invol.
   now apply cnv_leq.
   rewrite dotA. apply cnv_ext.
   apply str_refl.
   apply str_snoc.
   now apply str_ind_r.
   now apply str_ind_l.
   apply itr_str_r.
   apply capxdot.
   apply rdv_spec. 
   apply ldv_spec. 
Qed.

(** this gives us a tactic to prove properties by categorical duality *)
Lemma dualize {h} {P: ops -> Prop} (L: forall l X, laws l X -> h ≪ l -> P X) 
  {l X} {H: laws l X} {Hl:h ≪ l}: P X^op.
Proof. eapply L. apply dual_laws, H. assumption. Qed.

Ltac dual x := apply (dualize x).

(** the following are examples of the benefits of such dualities *)
Instance rdv_leq `{laws} `{DIV ≪ l} n m p: Proper (leq --> leq ++> leq) (rdv n m p).
Proof. dual @ldv_leq. Qed.

Instance rdv_weq `{laws} `{DIV ≪ l} n m p: Proper (weq ==> weq ==> weq) (rdv n m p).
Proof. dual @ldv_weq. Qed.

Lemma cnvrdv `{laws} `{CNV+DIV ≪ l} n m p (x: X m n) (y: X p n): (y o- x)° ≡ x° -o y°.
Proof. dual @cnvldv. Qed.

Lemma dotcapx `{laws} `{CAP ≪ l} n m p (x: X m n) (y z: X p m): (y ∩ z) ⋅ x ≦ (y⋅x) ∩ (z⋅x). 
Proof. dual @dotxcap. Qed.

Lemma Schroeder_r `{laws} `{BL+CNV ≪ l} n m p (x : X n m) (y : X m p) (z : X n p): 
  x⋅y ≦ z <-> !z⋅y° ≦ !x.
Proof. dual @Schroeder_l. Qed.


(** * Functors (i.e., monoid morphisms) *)

Class functor l {X Y: ops} (f': ob X -> ob Y) (f: forall {n m}, X n m -> Y (f' n) (f' m)) := {
  fn_morphism:>     forall n m, morphism l (@f n m);
  fn_dot:           forall n m p (x: X n m) (y: X m p), f (x⋅y) ≡ f x ⋅ f y;
  fn_one:           forall n, f (one n) ≡ 1;
  fn_itr `{STR ≪ l}: forall n (x: X n n), f (x^+) ≡ (f x)^+;
  fn_str `{STR ≪ l}: forall n (x: X n n), f (x^*) ≡ (f x)^*;
  fn_cnv `{CNV ≪ l}: forall n m (x: X n m), f (x°) ≡ (f x)°;
  fn_ldv `{DIV ≪ l}: forall n m p (x: X n m) (y: X n p), f (x -o y) ≡ f x -o f y;
  fn_rdv `{DIV ≪ l}: forall n m p (x: X m n) (y: X p n), f (y o- x) ≡ f y o- f x
}.

(** generating a structure by faithful embedding *)

Lemma laws_of_faithful_functor {h l X Y} {L: laws h Y} {Hl: l ≪ h} f' f:
  @functor l X Y f' f -> 
  (forall n m x y, f n m x ≦ f n m y -> x ≦ y) ->
  (forall n m x y, f n m x ≡ f n m y -> x ≡ y) ->
  laws l X.
  intros Hf Hleq Hweq.
  assert (Hleq_iff: forall n m x y, f n m x ≦ f n m y <-> x ≦ y).
   split. apply Hleq. apply fn_leq.
  assert (Hweq_iff: forall n m x y, f n m x ≡ f n m y <-> x ≡ y).
   split. apply Hweq. apply fn_weq.
  assert (L' := @lower_laws _ _ _ L Hl).
  constructor; repeat right; intro_vars. 
   apply (laws_of_injective_morphism (f n m)); auto using fn_morphism.
   rewrite <-Hweq_iff, 4fn_dot. apply dotA. 
   rewrite <-Hweq_iff, fn_dot, fn_one. apply dot1x. 
   rewrite <-Hweq_iff, fn_dot, fn_one. apply dotx1. 
   repeat intro. apply Hleq. rewrite 2fn_dot. now apply dot_leq; apply Hleq_iff. 
   apply Hleq. now rewrite fn_cup, 3fn_dot, fn_cup, dotplsx. 
   apply Hleq. now rewrite fn_cup, 3fn_dot, fn_cup, dotxpls. 
   apply Hleq. now rewrite fn_dot, 2fn_bot, dot0x. 
   apply Hleq. now rewrite fn_dot, 2fn_bot, dotx0.
   intro. apply Hleq. now rewrite fn_cnv, 2fn_dot, 2fn_cnv, cnvdot.
   intro. rewrite <-Hweq_iff, 2fn_cnv. apply cnv_invol.
   repeat intro. apply Hleq. rewrite 2fn_cnv. now apply cnv_leq; apply Hleq_iff. 
   apply Hleq. rewrite 2fn_dot,fn_cnv. apply cnv_ext.
   intro. apply Hleq. rewrite fn_one, fn_str. apply str_refl.
   intro. apply Hleq. rewrite fn_str, fn_dot, fn_str. apply str_cons.
   intro. rewrite <-2Hleq_iff, 2fn_dot, fn_str. apply str_ind_l.
   rewrite <-2Hleq_iff, 2fn_dot, fn_str. apply str_ind_r.
   intro. apply Hweq. rewrite fn_itr, fn_dot, fn_str. apply itr_str_l.
   intro. apply Hleq. rewrite fn_cap,2fn_dot,fn_cap,fn_dot,fn_cnv. apply capdotx.
   intro. rewrite <-2Hleq_iff, fn_dot, fn_ldv. apply ldv_spec. 
   intro. rewrite <-2Hleq_iff, fn_dot, fn_rdv. apply rdv_spec. 
Qed.


(** injection from Booleans into monoids (actually a functor, although we don't need it) *)
Definition ofbool {X: ops} {n} (a: bool): X n n := if a then 1 else 0.
Global Arguments ofbool {_ _} !_ /.
(* does not respect the uniform inheritance condition *)
(* Coercion ofbool: bool >-> car. *)


(** ML modules *)
Declare ML Module "ra_common". 
Declare ML Module "ra_fold".


(** tricks for reification  *)
Lemma catch_weq `{L: laws} n m (x y: X n m): 
  (let L:=L in x <=[false]= y) -> x ≡ y.
Proof. trivial. Defined.
Lemma catch_leq `{L: laws} n m (x y: X n m): 
  (let L:=L in x <=[true]= y) -> x ≦ y.
Proof. trivial. Defined.

Ltac catch_rel := apply catch_weq || apply catch_leq.

