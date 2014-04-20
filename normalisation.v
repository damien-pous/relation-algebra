(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * normalisation: generic normalisation procedure and associated tactics *)

Require Import kleene syntax powerfix.

Set Implicit Arguments.

Section n.
Variables (s t: positive -> positive).
Notation expr := (expr s t).
Local Arguments weq {_} _ _: simpl never.
Local Arguments leq {_} _ _: simpl never.
Local Hint Extern 0 (_ << _) => solve_lower || solve_lower': typeclass_instances.
Ltac fold_expr l := ra_fold (expr_ops s t l).

(** * normalisation procedure

   We normalise expressions in such a way that:
   - sums are flattened, left-associated, ordered (without duplicates), 
     and without bottom or top elements 
   - intersections are simply cleaned w.r.t bottom and top elements
   - products are left-associated, and possibly distributed over sums
     (specified using a boolean parameter)
   - unit and annihilators are ruled out as much as possible
   - strict iterations and Kleene stars do not contain inner iterations
   - converses are pushed to the leaves
   
   Some additional simplifications are possible, we plan to integrate
   them lazily, on demand. 

   The normalisation function is defined in such a way that 
   - the level of the resulting expression cannot increase w.r.t. the
     level of the initial one, and
   - it yields an expression which is equal to the starting one, 
     *at the level of that expression* 
   (in particular unions cannot be used to simplify lonely iterations)
*)


(** ** normalising sums *)

Fixpoint insert_pls n m (x: expr n m): expr n m -> expr n m :=
  match x with
    | e_zer _ _ => fun y => y
    | e_top _ _ => fun y => top
    | e_pls x z => fun y => 
      match cmp y z with 
        | Lt => insert_pls x y+z
        | Gt => x+z+y
        | Eq => x+z
      end
    | x => fun y => 
      match cmp x y with 
        | Lt => x+y
        | Gt => y+x
        | Eq => y
      end
  end%ast.

Fixpoint pls' n m (y: expr n m): expr n m -> expr n m :=
  match y with
    | e_zer _ _ => fun x => x
    | e_top _ _ => fun y => top
    | e_pls y z => fun x => insert_pls (pls' y x) z
    | y => fun x => insert_pls x y
  end%ast.

Lemma insert_pls_level n m (x y: expr n m): e_level (insert_pls x y) << CUP+e_level x+e_level y.
Proof. 
  induction x; simpl; try case cmp_spec; 
    simpl e_level; intros; try solve_lower'. 
  rewrite IHx1. solve_lower'. 
Qed.

Lemma insert_pls_pls: forall l n m (x y: expr n m) {Hl: CUP+e_level x << l},
  insert_pls x y ==_[l] y+x.
Proof.
  assert (D: forall n m (x y: expr n m) l, CUP+e_level x << l -> 
    y+x ==_[l] match cmp x y with Lt => x+y | Gt => y+x | Eq => y end).
   intros. case cmp_spec; intros; try subst; lattice. 

  intros; symmetry; induction x; simpl e_level in *; try (apply D; solve_lower). 
   lattice. 
   lattice.
   simpl insert_pls. case cmp_spec; intros.
    subst. lattice.
    fold_expr l. rewrite <- IHx1 by solve_lower'. lattice.
    lattice.
Qed.

Lemma pls'_level n m (x y: expr n m): e_level (pls' x y) << CUP+e_level x+e_level y.
Proof.
  induction x; simpl pls'; simpl e_level;
    rewrite ?insert_pls_level, ?IHx1, ?IHx; solve_lower'. 
Qed.

Lemma pls'pls: forall l n m (x y: expr n m) {Hl: CUP+e_level x+e_level y<< l},
  pls' x y ==_[l] x+y.
Proof.
  induction x; simpl e_level; simpl pls'; intros y Hl; 
    try (subst; now rewrite insert_pls_pls by solve_lower').
  lattice.
  lattice.
  rewrite insert_pls_pls, IHx1 by (rewrite ?pls'_level; solve_lower'). lattice.
Qed.

Lemma pls'x0_level n m (x: expr n m): e_level (pls' x 0) << e_level x.
Proof. induction x; try reflexivity. simpl. now rewrite insert_pls_level, IHx1. Qed.

Lemma pls'x0 n m (x: expr n m) l `{CUP+e_level x<<l}: pls' x 0 ==_[l] x.
Proof. 
  induction x; try reflexivity. simpl pls'. simpl e_level in *.
  rewrite insert_pls_pls, IHx1. apply cupC. solve_lower'. 
  rewrite pls'x0_level. solve_lower'.
Qed.


(** ** normalising intersections 
  we simply remove zeros and tops
  (TODO: normalise like for sums, distribute over sums) *)

Definition cap' n m (x y: expr n m) :=
  if is_top x then y
  else if is_top y then x 
  else if is_zer x ||| is_zer y then e_zer _ _
  else e_cap x y.

Lemma cap'cap l n m (x y: expr n m) {Hl: CAP+e_level x+e_level y << l}: 
  cap' x y ==_[l] x^y.
Proof.
  symmetry. unfold cap'. revert Hl. 
  case is_top_spec. intros. apply captx.
  case is_top_spec. intros. apply capxt.
  case is_zer_spec. intros. apply capbx.
  case is_zer_spec. intros. apply capxb.
  reflexivity.
Qed.

Lemma cap'_level n m (x y: expr n m): e_level (cap' x y) << CAP+e_level x+e_level y.
Proof. 
  unfold cap'. 
  case is_top_spec. solve_lower'. 
  case is_top_spec. solve_lower'. 
  case is_zer_spec. solve_lower'. 
  case is_zer_spec; solve_lower'. 
Qed.



(** ** normalising products
    (without ones or zeros, left associative, and possibly distributed
    over sums) *)

(** whether we distribute the products over sums is controlled by the
   following parameter *)
Variable distribute: bool.      

Ltac case_distribute :=
  match goal with |- context[distribute] => case distribute | _ => idtac end.

(* [dot_l x y == x*y] *)
Fixpoint dot_l n m (x: expr n m): forall p, expr m p -> expr n p :=
  match x in syntax.expr _ _ n m return forall p, expr m p -> expr n p with
    | e_zer _ _ => fun p y => 0
    | e_one _ => fun p y => y
    | e_pls x1 x2 => fun p y => 
      if distribute then pls' (dot_l x1 y) (dot_l x2 y)
      else (x1+x2)*y
    | x => fun p y => x * y 
  end%ast.

(* [dot_r y x == x*y] *)
Fixpoint dot_r m p (y: expr m p): forall n, expr n m -> expr n p :=
  match y in syntax.expr _ _ m p return forall n, expr n m -> expr n p with
    | e_zer _ _ => fun n x => 0
    | e_one _ => fun n x => x
    | e_pls y1 y2 => fun n x => 
      if distribute then pls' (dot_r y1 x) (dot_r y2 x)
      else dot_l x (y1+y2)
    | e_dot y z => fun n x => dot_l (dot_r y x) z
    | y => fun n x => dot_l x y
  end%ast.

Definition dot' n m p (x: expr n m) (y: expr m p) := dot_r y x.

Lemma dot_l_level n m p (x: expr n m) (y: expr m p): 
  e_level (dot_l x y) << e_level x + e_level y.
Proof.
  revert p y. 
  induction x; intros q z; simpl dot_l; case_distribute; simpl e_level; 
    rewrite ?pls'_level, ?IHx1, ?IHx2; solve_lower'.
Qed.

Lemma dot_r_level n m p (x: expr n m) (y: expr m p): 
  e_level (dot_r y x) << e_level x + e_level y.
Proof.
  revert n x. 
  induction y; intros q z; simpl dot_r; case_distribute; simpl e_level; 
    rewrite ?pls'_level, ?dot_l_level, ?IHy1, ?IHy2; solve_lower'.
Qed.

Lemma dot'_level n m p (x: expr n m) (y: expr m p): 
  e_level (dot' x y) << e_level x + e_level y.
Proof. apply dot_r_level. Qed.

Lemma dot_l_weq l n m p (x: expr n m) (y: expr m p) {Hl: e_level x + e_level y << l}: 
  x*y ==_[l] dot_l x y.
Proof.
  revert p y Hl. 
  induction x; intros q z Hl; simpl dot_l; case_distribute; simpl e_level in Hl; try reflexivity. 
   apply dot0x. 
   apply dot1x. 
   now rewrite dotplsx, pls'pls, <-IHx1, <-IHx2 by (rewrite ?dot_l_level; solve_lower').
Qed.

Lemma dot'dot l n m p (x: expr n m) (y: expr m p) {Hl: e_level y+e_level x << l}: 
  dot' x y ==_[l] x*y.
Proof.
  symmetry. unfold dot'. revert n x Hl. 
  induction y; simpl e_level; intros q z Hl; simpl dot_r; case_distribute;
    try reflexivity; try (apply dot_l_weq; solve_lower'). 
   apply dotx0. 
   apply dotx1. 
   now rewrite dotxpls, pls'pls, <-IHy1, <-IHy2 by (rewrite ?dot_r_level; solve_lower').
   now rewrite <-dot_l_weq, <-IHy1, dotA by (rewrite ?dot_r_level; solve_lower').
Qed.



(** ** normalising converses
    by pushing them down towards the leaves *)

Fixpoint cnv' n m (x: expr n m): expr m n :=
  match x with
    | e_zer _ _ => 0
    | e_top _ _ => top
    | e_one _ => 1
    | e_pls x y => cnv' x + cnv' y
    | e_cap x y => cnv' x ^ cnv' y
    | e_neg x => ! cnv' x                        (* TODO: normalise complements *)
    | e_dot x y => dot' (cnv' y) (cnv' x) (* we need to reverse parentheses *)
    | e_ldv x y => e_rdv (cnv' x) (cnv' y)     (* TODO: normalise residuals? *)
    | e_rdv x y => e_ldv (cnv' x) (cnv' y)
    | e_itr x => cnv' x ^+
    | e_str x => cnv' x ^*
    | e_cnv x => x
    | e_var a => e_var a`
  end%ast.

Lemma cnv'_level n m (x: expr n m): e_level (cnv' x) << CNV+e_level x.
Proof. 
  induction x; simpl cnv'; simpl e_level; 
    rewrite ?dot'_level, ?pls'_level, ?cap'_level, ?IHx1, ?IHx2, ?IHx; solve_lower'.
Qed.

Lemma cnv'cnv l n m (x: expr n m) {Hl: CNV+e_level x << l}: cnv' x ==_[l] x`.
Proof.
  symmetry. induction x; simpl cnv'; simpl e_level in Hl; 
  rewrite ?dot'dot, ?e_str' by (rewrite ?cnv'_level; solve_lower').
  apply cnv0.
  apply cnvtop.
  apply cnv1.
  rewrite cnvpls. apply cup_weq; [apply IHx1|apply IHx2]; solve_lower'.
  rewrite cnvcap. apply cap_weq; [apply IHx1|apply IHx2]; solve_lower'.
  rewrite cnvneg. apply neg_weq, IHx. solve_lower'.
  rewrite cnvdot. apply dot_weq; [apply IHx2|apply IHx1]; solve_lower'.
  rewrite cnvitr. apply itr_weq, IHx. solve_lower'.
  rewrite cnvstr. apply str_weq, IHx. solve_lower'.
  apply cnv_invol.
  rewrite cnvldv. apply rdv_weq; [apply IHx1|apply IHx2]; solve_lower'. 
  rewrite cnvrdv. apply ldv_weq; [apply IHx1|apply IHx2]; solve_lower'. 
  reflexivity.
Qed.

(** ** removing toplevel iterations in an iterated sum  *)

Fixpoint remove n m (x: expr n m): expr n m :=
  match x with
    | e_itr x => x
    | e_pls x y => pls' (remove x) (remove y)
    | x => x
  end.

Definition itr' n (x: expr n n): expr n n :=
  (if is_zer x then 0
  else if is_top x then top 
  else remove x^+)%ast.

Definition str' n (x: expr n n): expr n n :=
  (if is_zer x then 1
  else if is_top x then top 
  else remove x^*)%ast.

Lemma remove_level n m (x: expr n m): e_level (remove x) << e_level x.
Proof. induction x; cbn; rewrite ?pls'_level; solve_lower'. Qed.

Lemma itr'_level n (x: expr n n): e_level (itr' x) << STR+e_level x.
Proof. 
  unfold itr'. 
  case is_zer_spec. reflexivity. 
  case is_top_spec. solve_lower'. 
  cbn. now rewrite remove_level. 
Qed.

Lemma str'_level n (x: expr n n): e_level (str' x) << STR+e_level x.
Proof. 
  unfold str'. 
  case is_zer_spec. reflexivity. 
  case is_top_spec. solve_lower'. 
  cbn. now rewrite remove_level. 
Qed.

Lemma remove_spec_dep l n m (x: expr n m):
  forall (H: n=m) {Hl: STR+e_level x << l}, (cast H eq_refl (remove x))^+ ==_[l] cast H eq_refl x^+.
Proof.
  induction x; cbn; trivial; intros H Hl. 
  - subst. cbn. rewrite itr_pls_itr, pls'pls by (rewrite 2remove_level; solve_lower').
    rewrite <-(IHx1 eq_refl), <-(IHx2 eq_refl) by solve_lower'. simpl cast. apply itr_pls_itr. 
  - now rewrite 2cast_eq, itr_invol. 
Qed.

Lemma remove_spec l n (x: expr n n) {Hl: STR+e_level x << l}:
  remove x ^+ ==_[l] x^+.
Proof. apply (remove_spec_dep _ eq_refl). Qed.

Lemma itr'itr l n (x: expr n n) {Hl: STR+e_level x << l}: 
  itr' x ==_[l] x^+.
Proof.
  symmetry. unfold itr'. revert Hl. 
  case is_zer_spec. intros. apply itr0. 
  case is_top_spec. intros. apply itrtop.
  intros. symmetry. now apply remove_spec.
Qed.

Lemma remove_spec_dep' l n m (x: expr n m): forall (H: n=m) {Hl: STR+e_level x << l}, 
  (cast H eq_refl (remove x))^* ==_[l] cast H eq_refl x^*.
Proof.
  induction x; cbn; trivial; intros H Hl. 
  - subst. simpl cast. rewrite str_pls_str. 
    rewrite <-(IHx1 eq_refl), <-(IHx2 eq_refl) by solve_lower'. 
    simpl cast. rewrite <-str_pls_str. apply str_weq. apply pls'pls. 
    rewrite 2remove_level; solve_lower'.
  - rewrite 2cast_eq. apply antisym. 
    apply str_leq. apply itr_ext. 
    apply str_ind_l1. apply str_refl. now rewrite itr_str_l, str_cons, str_trans.
Qed.

Lemma remove_spec' l n (x: expr n n) {Hl: STR+e_level x << l}:
  remove x ^* ==_[l] x^*.
Proof. apply (remove_spec_dep' _ eq_refl). Qed.

Lemma str'str l n (x: expr n n) {Hl: STR+e_level x << l}: 
  str' x ==_[l] x^*.
Proof.
  symmetry. unfold str'. revert Hl. 
  case is_zer_spec. intros. apply str0. 
  case is_top_spec. intros. apply strtop.
  intros. symmetry. now apply remove_spec'.
Qed.


(** ** global normalisation function *)

Fixpoint norm n m (x: expr n m): expr n m :=
  match x with
    | e_zer _ _ => 0
    | e_top _ _ => top
    | e_one _ => 1
    | e_pls x y => pls' (norm x) (norm y)
    | e_cap x y => cap' (norm x) (norm y)
    | e_neg x => e_neg (norm x)
    | e_dot x y => dot' (norm x) (norm y)
    | e_ldv x y => e_ldv (norm x) (norm y)
    | e_rdv x y => e_rdv (norm x) (norm y)
    | e_itr x => itr' (norm x)
    | e_str x => str' (norm x)
    | e_cnv x => cnv' (norm x)
    | e_var a => e_var a
  end%ast.

Lemma norm_level n m (x: expr n m): e_level (norm x) << e_level x.
Proof. 
  induction x; simpl norm; simpl e_level; 
    rewrite ?dot'_level, ?pls'_level, ?cap'_level, ?cnv'_level, 
      ?itr'_level, ?str'_level, ?IHx1, ?IHx2, ?IHx; solve_lower'.
Qed.
  
Lemma norm_weq l n m (x: expr n m) {Hl: e_level x << l}: norm x ==_[l] x.
Proof.
  induction x; simpl norm; simpl e_level in Hl; try reflexivity; 
    rewrite ?pls'pls, ?cap'cap, ?dot'dot, ?itr'itr, ?str'str, ?cnv'cnv, ?e_str' 
      by (rewrite ?norm_level; solve_lower').
  apply cup_weq; [apply IHx1|apply IHx2]; solve_lower'. 
  apply cap_weq; [apply IHx1|apply IHx2]; solve_lower'. 
  apply neg_weq, IHx. solve_lower'.
  apply dot_weq; [apply IHx1|apply IHx2]; solve_lower'.
  apply itr_weq, IHx. solve_lower'.
  apply str_weq, IHx. solve_lower'.
  apply cnv_weq, IHx. solve_lower'.
  apply ldv_weq; [apply IHx1|apply IHx2]; solve_lower'.
  apply rdv_weq; [apply IHx1|apply IHx2]; solve_lower'.
Qed.


(** * partial decision procedure for expressions containment [<==]

   The following function tries to prove [x <== y], for some
   expressions [x] and [y].
   - this function always terminates, but using powerfix allows us to
     write a clean code, without bothering about termination
   - this algorithm is not complete, of course. 
   - like for syntactic comparison ([syntax.expr_compare]), we need to 
     generalise the function to work on distinct expression types *)

Definition expr_leq := powerfix 100
  (fun leq tt n m (x: expr n m) p q (y: expr p q) => 
    let leq {n m} x {p q} y := leq tt n m x p q y in
    match x,y with
      | e_zer _ _, _ 
      | _, e_top _ _  
      | e_one _, e_one _ 
      | e_one _, e_str _ => true
      | e_one _, e_itr y => leq x y
      | e_var a, e_var b => eqb a b
      | e_pls x x', _ => leq x y &&& leq x' y
      | _, e_cap y y' =>  leq x y &&& leq x y'
      | e_cap x x', _ => leq x y ||| leq x' y
      | _, e_pls y y' =>  leq x y ||| leq x y'
      | @e_dot _ _ _ _ u _ x x', @e_dot _ _ _ _ v _ y y' (* split using one? *)
      | @e_ldv _  _ _ u _ _ y x', @e_ldv _ _ _ v _ _ x y' (* ldv_spec in the other cases? *)
      | @e_rdv _ _ _ u _ _ y x', @e_rdv _ _ _ v _ _ x y' => eqb u v &&& leq x y &&& leq x' y'
      | e_one _, e_ldv x y
      | e_one _, e_rdv x y
      | e_neg y, e_neg x 
      | e_itr x, e_itr y
      | e_itr x, e_str y
      | e_str x, e_str y
      | e_cnv x, e_cnv y => leq x y
      | _,_ => false
    end) (fun _ _ _ _ _ _ _ => false) tt.

Lemma expr_leq_correct_dep l: forall n m (x: expr n m) p q (y: expr p q),
  forall Hnp: n=p, forall Hmq: m=q, 
  expr_leq x y = true -> 
  e_level x + e_level y << l ->
  cast Hnp Hmq x <==_[l] y.
Proof.
  (* TODO: this proof could be factorised, using a more appropriate
     case disjunction, it's not that easy to setup, however *)
  unfold expr_leq. apply powerfix_invariant. 2: discriminate.
  intros leq IH n m x p q y Hnp Hmq H Hl.
  (** FIXME : subst here causes an effect leak *)
  destruct x; simpl e_level in Hl; repeat match goal with [ H : ?m = ?n |- _ ] => rewrite H in *; clear H end.
  - rewrite cast_eq. lattice.
  - destruct y; simpl e_level in Hl; try discriminate H. 
    + now rewrite cast_eq.
    + apply leq_xcup. apply lorb_spec in H as [H|H];
      apply (IH _ _ _ _ _ _ eq_refl eq_refl) in H; auto; solve_lower'. 
    + apply landb_spec in H as [H1 H2]. apply leq_xcap; apply IH; trivial; solve_lower'. 
  - destruct y; simpl e_level in Hl; try discriminate H; try subst. 
    + subst. rewrite cast_eq. lattice.
    + now rewrite cast_eq. 
    + subst. apply leq_xcup. apply lorb_spec in H as [H|H];
      apply (IH _ _ _ _ _ _ eq_refl eq_refl) in H; auto; solve_lower'. 
    + apply landb_spec in H as [H1 H2]. apply leq_xcap; apply IH; trivial; solve_lower'. 
    + rewrite <-itr_ext. apply IH. assumption. solve_lower'. 
    + rewrite cast_eq. apply str_refl. 
    + subst. rewrite cast_eq. apply ldv_spec. rewrite dotx1. 
      apply (IH _ _ _ _ _ _ eq_refl eq_refl H); solve_lower'. 
    + subst. rewrite cast_eq. apply rdv_spec. rewrite dot1x. 
      apply (IH _ _ _ _ _ _ eq_refl eq_refl H); solve_lower'. 
  - destruct y; simpl e_level in Hl; try discriminate H; try subst;
    try (apply landb_spec in H as [H1 H2]; apply leq_cupx;  
          [ apply (IH _ _ _ _ _ _ eq_refl eq_refl H1); solve_lower'
          | apply (IH _ _ _ _ _ _ eq_refl eq_refl H2); solve_lower' ]).
    lattice.
  - destruct y; simpl e_level in Hl; try discriminate H; try subst;
    try (rewrite cast_eq; apply leq_capx; apply lorb_spec in H as [H|H]; 
        (apply (IH _ _ _ _ _ _ eq_refl eq_refl) in H; [auto |solve_lower'])). 
    lattice. 
    rewrite cast_eq. apply landb_spec in H as [H1 H2].
     apply (IH _ _ _ _ _ _ eq_refl eq_refl) in H1; [|solve_lower'].
     apply (IH _ _ _ _ _ _ eq_refl eq_refl) in H2; [|solve_lower'].
     hlattice.
  - destruct y; simpl e_level in Hl; try discriminate H; try subst.
    + lattice.
    + apply leq_xcup. apply lorb_spec in H as [H|H];
      apply (IH _ _ _ _ _ _ eq_refl eq_refl) in H; auto; solve_lower'. 
    + apply landb_spec in H as [H1 H2]. apply leq_xcap; apply IH; trivial; solve_lower'. 
    + rewrite cast_eq. apply neg_leq. 
      apply (IH _ _ _ _ _ _ eq_refl eq_refl H). solve_lower'.
  - destruct y; simpl e_level in Hl; try discriminate H; try subst.
    + lattice.
    + apply leq_xcup. apply lorb_spec in H as [H|H];
      apply (IH _ _ _ _ _ _ eq_refl eq_refl) in H; auto; solve_lower'. 
    + apply landb_spec in H as [H1 H2]. apply leq_xcap; apply IH; trivial; solve_lower'. 
    + rewrite cast_eq. apply landb_spec in H as [H' H]. apply landb_spec in H as [H1 H2]. 
      revert H'. case eqb_spec. 2: discriminate. intros ? _. subst. 
      apply dot_leq. 
       apply (IH _ _ _ _ _ _ eq_refl eq_refl H1); solve_lower'.
       apply (IH _ _ _ _ _ _ eq_refl eq_refl H2); solve_lower'.
  - destruct y; simpl e_level in Hl; try discriminate H; try subst.
    + lattice.
    + subst. apply leq_xcup. apply lorb_spec in H as [H|H];
      apply (IH _ _ _ _ _ _ eq_refl eq_refl) in H; auto; solve_lower'. 
    + apply landb_spec in H as [H1 H2]. apply leq_xcap; apply IH; trivial; solve_lower'. 
    + rewrite cast_eq. apply itr_leq. 
      apply (IH _ _ _ _ _ _ eq_refl eq_refl H); solve_lower'.
    + rewrite cast_eq. rewrite itr_str_l, <-(str_cons y). 
      apply (IH _ _ _ _ _ _ eq_refl eq_refl) in H. 2: solve_lower'.
      simpl cast in H. now rewrite H. 
  - destruct y; simpl e_level in Hl; try discriminate H; try subst.
    + lattice.
    + subst. apply leq_xcup. apply lorb_spec in H as [H|H];
      apply (IH _ _ _ _ _ _ eq_refl eq_refl) in H; auto; solve_lower'. 
    + apply landb_spec in H as [H1 H2]. apply leq_xcap; apply IH; trivial; solve_lower'. 
    + rewrite cast_eq. apply str_leq. 
      apply (IH _ _ _ _ _ _ eq_refl eq_refl H); solve_lower'.
  - destruct y; simpl e_level in Hl; try discriminate H; try subst.
    + lattice.
    + apply leq_xcup. apply lorb_spec in H as [H|H];
      apply (IH _ _ _ _ _ _ eq_refl eq_refl) in H; auto; solve_lower'. 
    + apply landb_spec in H as [H1 H2]. apply leq_xcap; apply IH; trivial; solve_lower'. 
    + rewrite cast_eq. apply cnv_leq. 
      apply (IH _ _ _ _ _ _ eq_refl eq_refl H); solve_lower'.
  - destruct y; simpl e_level in Hl; try discriminate H; try subst.
    + lattice.
    + apply leq_xcup. apply lorb_spec in H as [H|H];
      apply (IH _ _ _ _ _ _ eq_refl eq_refl) in H; auto; solve_lower'. 
    + apply landb_spec in H as [H1 H2]. apply leq_xcap; apply IH; trivial; solve_lower'. 
    + rewrite cast_eq. apply landb_spec in H as [H' H]. apply landb_spec in H as [H1 H2]. 
      revert H'. case eqb_spec. 2: discriminate. intros ? _. subst. 
      apply ldv_leq. 
       apply (IH _ _ _ _ _ _ eq_refl eq_refl H1); solve_lower'.
       apply (IH _ _ _ _ _ _ eq_refl eq_refl H2); solve_lower'.
  - destruct y; simpl e_level in Hl; try discriminate H; try subst.
    + lattice.
    + apply leq_xcup. apply lorb_spec in H as [H|H];
      apply (IH _ _ _ _ _ _ eq_refl eq_refl) in H; auto; solve_lower'. 
    + apply landb_spec in H as [H1 H2]. apply leq_xcap; apply IH; trivial; solve_lower'. 
    + rewrite cast_eq. apply landb_spec in H as [H' H]. apply landb_spec in H as [H1 H2]. 
      revert H'. case eqb_spec. 2: discriminate. intros ? _. subst. 
      apply rdv_leq. 
       apply (IH _ _ _ _ _ _ eq_refl eq_refl H1); solve_lower'.
       apply (IH _ _ _ _ _ _ eq_refl eq_refl H2); solve_lower'.
  - destruct y; simpl e_level in Hl; try discriminate H; subst.
    + lattice.
    + apply leq_xcup. apply lorb_spec in H as [H|H]; eapply IH in H; eauto; solve_lower'. 
    + apply landb_spec in H as [H1 H2]. apply leq_xcap; apply IH; trivial; solve_lower'. 
    + apply eqb_eq in H. subst. now rewrite cast_eq. 
Qed.

(** correctness of the comparison function *)
Corollary expr_leq_correct l n m (x y: expr n m):
  expr_leq x y = true -> 
  e_level x + e_level y << l ->
  x <==_[l] y.
Proof. apply (expr_leq_correct_dep x y eq_refl eq_refl). Qed.


(** * Associated tactics *)

(** parametrised (in)equality tests, where we decide to check for an
   equality or an inequality depending on the Boolean [b]. This helps
   to factorise tactics code. *)

Definition expr_leq_or_weq (b: bool) n m (x y: expr n m) := 
  if b then expr_leq x y else eqb x y.

Lemma expr_leq_or_weq_correct b l n m (x y: expr n m):
  e_level x + e_level y << l ->
  expr_leq_or_weq b x y -> @leq_or_weq b (expr_lattice_ops _ _ l _ _) x y.
Proof.
  intros Hl H. destruct b. apply expr_leq_correct; assumption. 
  apply eqb_eq in H as <-. reflexivity. 
Qed.

End n.


(** normalisation lemma, suited for use with reification ; we use two
   "let-in" constructs to make it possible to isolate computations of
   the normal forms (using vm_compute) from the unfolding of the
   interpretation function (using "unfold" selectively) *)

Lemma ra_normalise d b `{L: laws} f' (f: positive -> Pack X f')
  n m (x y: expr _ _ n m) (Hl: e_level x + e_level y << l):
  (let x' := norm d x in let y' := norm d y in packed_eval f x' <=[b]= packed_eval f y') -> 
  packed_eval f x <=[b]= packed_eval f y.
Proof. 
  unfold packed_eval. intro H. 
  eapply leq_or_weq_weq; [symmetry.. | eassumption];  
    (eapply norm_weq; [ | eassumption]); solve_lower'.
Qed.

(** reflexivity-by-normalisation lemma, suited for use with
   reification *)

Lemma ra b `{L: laws} f' (f: positive -> Pack X f')
  n m (x y: expr _ _ n m) (Hl: e_level x + e_level y << l):
  expr_leq_or_weq b (norm true x) (norm true y) = true -> packed_eval f x <=[b]= packed_eval f y.
Proof.
  intro H. apply (ra_normalise true b). assumption. 
  intros x' y'. subst x' y'. eapply expr_leq_or_weq_correct in H.
  destruct b; apply (H _ L). 
  now rewrite 2norm_level.
Qed.

(** ** [ra]: solve goals by normalisation.
   
   In case of an inequality, the above comparison function is used, so
   that [apply antisym; ra] might solve goals which are
   not solved by [ra]. (e.g., [a+a^*+b^* == b+a^*+b^*]) *)

Ltac ra :=
  let go h L tac :=
    ra_reify h;
    let lhs:=fresh "lhs" in
    let rhs:=fresh "rhs" in
    intros ? ? ? ? lhs rhs;
    apply (@ra _ _ _ L _ _ _ _ lhs rhs);
    [ tac || fail "RelationAlgebra: invalid reification (please report)" | 
      close_by_reflection true || fail "not provable by relation algebra normalisation" ]
  in
  intros; catch_rel;
  let L:=fresh "L" in intro L;
  let l:=match type of L with laws ?l _ => l end in
  lazymatch goal with 
  | H: ?h<<l |- _ => go h L ltac:(rewrite <- H; reflexivity)
  | _ => go l L ltac:(reflexivity || destruct l; reflexivity)
  end.

(* (* vm_compute in value of h, even in presence of evars [DOES NOT WORK] *) *)
(* Ltac evm_compute h := *)
(*   (has_evar h;  *)
(*     idtac "warning: there are evar, cannot use vm_compute"; *)
(*       compute in (value of h)) *)
(*   || vm_compute in (value of h). *)

(** ** [ra_normalise/simpl]: normalise the current goal *)

Ltac ra_normalise_ distribute :=
  let go h L tac :=
    ra_reify h;
    let tenv:=fresh "tenv" in
    let env:=fresh "env" in
    let src:=fresh "src" in
    let tgt:=fresh "tgt" in
    let lhs:=fresh "lhs" in
    let rhs:=fresh "rhs" in
    intros ? ? ? ? lhs rhs;
    apply (@ra_normalise distribute _ _ _ L _ _ _ _ lhs rhs);
    [ tac; reflexivity || fail "RelationAlgebra: invalid reification (please report)" | 
      let lhs':=fresh "lhs'" in
      let rhs':=fresh "rhs'" in
      intros lhs' rhs'; 
      vm_compute in (value of lhs'), (value of rhs');
      unfold sigma_add in env, tenv;
      unfold lhs', rhs', packed_eval, eval, val, src, tgt, env, tenv, sigma_get;
      unfold leq_or_weq;
      clear tenv env src tgt lhs rhs lhs' rhs' L ]
  in
  catch_rel;
  let L:=fresh "L" in intro L;
  let l:=match type of L with laws ?l _ => l end in
  lazymatch goal with 
  | H: ?h<<l |- _ => go h L ltac:(rewrite <- H; reflexivity)
  | _ => go l L ltac:(reflexivity || destruct l; reflexivity)
  end.

(** [ra_normalise] distribut products over sums, while [ra_simpl] does not *)

Ltac ra_simpl := ra_normalise_ false.
Ltac ra_normalise := ra_normalise_ true.
