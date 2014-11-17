(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * rmx: matrices of regular expressions *)

Require Import monoid regex lset boolean sups matrix_ext normalisation.
Set Implicit Arguments.
Unset Printing Implicit Defensive.

(** [rmx n m] denote the set of [(n,m)]-matrices of regular expressions *)

Notation rmx n m := (mx regex' n m).

(** they form a Kleene algebra (with bottom element) *)
Instance rmx_lattice_laws n m: 
  lattice.laws BKA (mx_lattice_ops regex_lattice_ops n m) := mx_lattice_laws n m.
Instance rmx_laws: laws BKA (mx_ops regex_ops regex_tt) := mx_laws regex_tt.


(** * Set of variables occurring in a matrix *)

Definition mx_vars n m (M: rmx n m) := \sup_(i<n) \sup_(j<m) vars (M i j). 

Lemma mx_vars_full n m (M: rmx n m) i j: vars (M i j) <== mx_vars M. 
Proof. unfold mx_vars. do 2 erewrite <-leq_xsup by apply in_seq. reflexivity. Qed.
  

(** * Pointwise extension of [epsilon] to matrices  *)
Definition epsilon_mx := (mx_map (fun e => eps e)).

Lemma epsilon_mx_pls n m (M N: rmx n m): epsilon_mx (M+N) == epsilon_mx M + epsilon_mx N.
Proof. intros i j. apply orb_pls. Qed.

Lemma epsilon_sup I J (f: I -> regex'): eps (\sup_(i\in J) f i) == \sup_(i\in J) eps (f i).
Proof. induction J. reflexivity. simpl. fold_regex. now rewrite <-IHJ, orb_pls. Qed.

Lemma epsilon_mx_dot n m p (M: rmx n m) (N: rmx m p): 
  epsilon_mx (M*N) == epsilon_mx M * epsilon_mx N.
Proof.
  intros i j. simpl. unfold epsilon_mx, mx_map, mx_dot. 
  rewrite epsilon_sup. now setoid_rewrite andb_dot. 
Qed.

Instance epsilon_mx_weq n m: Proper (weq ==> weq) (@epsilon_mx n m).
Proof. intros M N H i j. unfold epsilon_mx, mx_map. now rewrite (H i j). Qed.

(** [epsilon_mx] commutes with Kleene star on matrices *)
Lemma epsilon_mx_str: forall n (M: rmx n n), epsilon_mx (M^*) == epsilon_mx M ^*.
Proof.
  apply (mx_str_ind' (fun n M sM => epsilon_mx sM == epsilon_mx M ^*)).
  - intros n ? ? H ? ? H'. now rewrite H, H'.  
  - intros ? i. elim (ord_0_empty i).
  - intro M. rewrite mx_str_1. intros i j.
    unfold epsilon_mx, scal_mx, mx_scal, mx_map. now rewrite str_eps. 
  - intros n m a b c d e be ec f fbe ecf He Hf. 
    unfold epsilon_mx. rewrite 2mx_map_blk, mx_str_blk. 
    fold (epsilon_mx). 
    assert (H1: epsilon_mx (a+be*c) ^*
             == (epsilon_mx a + epsilon_mx b * epsilon_mx d ^* * epsilon_mx c) ^*)
      by (unfold be; rewrite epsilon_mx_pls, 2epsilon_mx_dot, He; reflexivity). 
    apply blk_mx_weq.
    + rewrite Hf. exact H1.
    + unfold fbe, be. now rewrite 2epsilon_mx_dot, He, Hf, H1.
    + unfold ecf, ec. now rewrite 2epsilon_mx_dot, He, Hf, H1.
    + unfold ecf, be, ec. now rewrite epsilon_mx_pls, 4epsilon_mx_dot, He, Hf, H1. 
Qed.


(** * Pointwise extension of derivatives to matrices  *)
Notation deriv_mx a M := (mx_map (deriv a) M).

Lemma deriv_mx_pls a n m (M N: rmx n m): deriv_mx a (M+N) == deriv_mx a M + deriv_mx a N. 
Proof. reflexivity. Qed.

Lemma deriv_mx_dot a n m p (M: rmx n m) (N: rmx m p): 
  deriv_mx a (M*N) == deriv_mx a M * N + epsilon_mx M * deriv_mx a N. 
Proof. intros i j. setoid_rewrite deriv_sup. simpl deriv; fold_regex. apply supcup. Qed.

Instance deriv_mx_weq a n m: Proper (weq ==> weq) (@mx_map _ _ (deriv a) n m).
Proof. apply mx_map_weq. Qed.

(** [deriv_mx] commutes with Kleene star on "strict" matrices, 
   those whose epsilon matrix is empty *)
Lemma deriv_mx_str_strict a: forall n (M: rmx n n), 
  epsilon_mx M == 0 -> deriv_mx a (M^*) == deriv_mx a M * M^*.
Proof.
  refine (mx_str_ind' (fun n M sM => 
    epsilon_mx M == 0 -> deriv_mx a sM == deriv_mx a M * sM) _ _ _ _).
   intros n ? ? H ? ? H'. now rewrite H, H'. 
   intros M _ i. elim (ord_0_empty i).
   intros M _ i j. setoid_rewrite ord0_unique. symmetry. apply cupxb. 
   rename a into l. intros n m a b c d e be ec f fbe ecf He Hf HM.
   rewrite 2mx_map_blk, mx_dot_blk. 
   unfold epsilon_mx in HM. rewrite mx_map_blk in HM. apply blk_mx_0 in HM as (Ha&Hb&Hc&Hd).
   assert (Hf': epsilon_mx (a+be*c) == 0).
     rewrite epsilon_mx_pls, epsilon_mx_dot, Ha, Hc; ra. 
   specialize (He Hd). specialize (Hf Hf'). 
   unfold be in Hf. rewrite deriv_mx_pls, <-dotA, deriv_mx_dot, Hb, dot0x, cupxb in Hf.
   assert (Hecf: deriv_mx l ecf == deriv_mx l c * f + deriv_mx l d * ecf). 
     unfold ecf at 1, ec. rewrite <-dotA, deriv_mx_dot.
     rewrite He. unfold e at 2. rewrite epsilon_mx_str, Hd. 
     rewrite deriv_mx_dot, Hc. unfold ecf, ec. ra. 
   apply blk_mx_weq. 
   - rewrite Hf. unfold ecf, ec. ra.  
   - unfold fbe. rewrite deriv_mx_dot. unfold f at 2; rewrite epsilon_mx_str, Hf'.
     unfold be at 2. rewrite deriv_mx_dot. rewrite Hb.
     rewrite Hf. unfold ecf, be, ec. ra. 
   - apply Hecf.
   - rewrite deriv_mx_pls, deriv_mx_dot, He, Hecf. 
     unfold ecf at 2, ec. rewrite 2epsilon_mx_dot, Hc. 
     unfold fbe. ra. 
Qed.



(** * Pointwise predicates and operations on matrices *)

(** generic definitions ans lemmas *)
Definition mx_forall (f: _ -> Prop) n m (M: rmx n m) := forall i j, f (M i j).

Lemma mx_forall_row f n m1 m2 M11 M21:
  mx_forall f M11 -> mx_forall f M21 -> 
  mx_forall f (@row_mx _ n m1 m2 M11 M21).
Proof. repeat intro. unfold row_mx. now case ordinal.split. Qed.

Lemma mx_forall_col f n1 n2 m M11 M21:
  mx_forall f M11 -> 
  mx_forall f M21 -> 
  mx_forall f (@col_mx _ n1 n2 m M11 M21).
Proof. repeat intro. unfold col_mx. now case ordinal.split. Qed.

Lemma mx_forall_blk f n1 n2 m1 m2 M11 M12 M21 M22:
  mx_forall f M11 -> mx_forall f M12 -> 
  mx_forall f M21 -> mx_forall f M22 -> 
  mx_forall f (@blk_mx _ n1 n2 m1 m2 M11 M12 M21 M22).
Proof. intros. now apply mx_forall_col; apply mx_forall_row. Qed.

Hint Resolve mx_forall_blk mx_forall_row mx_forall_col: mx_predicates.

(** 01, simple, and pure matrices *)
Notation is_01_mx := (mx_forall is_01).
Notation is_simple_mx := (mx_forall is_simple).
Notation is_pure_mx := (mx_forall is_pure).

(** taking the pure part of a matrix *)
Definition pure_part_mx := (mx_map pure_part).


(** the above classes are preserved by supremums *)
Lemma is_01_sup I J (f: I -> regex'): 
  (forall i, List.In i J -> is_01 (f i)) -> is_01 (\sup_(i \in J) f i).
Proof. apply P_sup; now constructor. Qed.

Lemma is_simple_sup I J (f: I -> regex'): 
  (forall i, List.In i J -> is_simple (f i)) -> is_simple (\sup_(i\in J) f i).
Proof. apply P_sup; now constructor. Qed.

Lemma is_pure_sup I J (f: I -> regex'): 
  (forall i, List.In i J -> is_pure (f i)) -> is_pure (\sup_(i\in J) f i).
Proof. apply P_sup; now constructor. Qed.


(** ** 01 matrices *)

Lemma is_01_mx_zer n m: is_01_mx (0: rmx n m). 
Proof. constructor. Qed.

Lemma is_01_mx_one n: is_01_mx (1: rmx n n). 
Proof. repeat intro. simpl. unfold mx_one. case ordinal.eqb_ord; constructor. Qed.

Lemma is_01_mx_cup n m (M N: rmx n m): is_01_mx M -> is_01_mx N -> is_01_mx (M+N).
Proof. repeat intro. now constructor. Qed.

Lemma is_01_mx_dot n m p (M: rmx n m) (N: rmx m p): is_01_mx M -> is_01_mx N -> is_01_mx (M*N).
Proof. repeat intro. apply is_01_sup. now constructor. Qed.

Lemma is_01_mx_scal e: is_01 e -> is_01_mx (scal_mx e).
Proof. now repeat intro. Qed.

Lemma is_01_scal_mx M: is_01_mx M -> is_01 (mx_scal M).
Proof. intro. apply H. Qed.

Lemma is_01_mx_sub00 n1 n2 m1 m2 M: is_01_mx M -> is_01_mx (@sub00_mx _ n1 n2 m1 m2 M).
Proof. intros H i j. apply H. Qed. 

Lemma is_01_mx_sub01 n1 n2 m1 m2 M: is_01_mx M -> is_01_mx (@sub01_mx _ n1 n2 m1 m2 M).
Proof. intros H i j. apply H. Qed. 

Lemma is_01_mx_sub10 n1 n2 m1 m2 M: is_01_mx M -> is_01_mx (@sub10_mx _ n1 n2 m1 m2 M).
Proof. intros H i j. apply H. Qed. 

Lemma is_01_mx_sub11 n1 n2 m1 m2 M: is_01_mx M -> is_01_mx (@sub11_mx _ n1 n2 m1 m2 M).
Proof. intros H i j. apply H. Qed. 

Hint Resolve is_01_mx_zer is_01_mx_one is_01_mx_cup is_01_mx_dot is_01_mx_scal is_01_scal_mx
  is_01_mx_sub00 is_01_mx_sub01 is_01_mx_sub10 is_01_mx_sub11: mx_predicates.

Lemma is_01_mx_str n (M: rmx n n): is_01_mx M -> is_01_mx (M^*).
Proof. 
  revert M. induction n; intros M HM. assumption.
  simpl. unfold mx_str_build. change (S n) with (1+n)%nat. 
  ra_fold (mx_ops regex_ops regex_tt). 
  auto 13 using is_01_str with mx_predicates. 
Qed.

Lemma is_01_mx_epsilon n m (M: rmx n m): is_01_mx (epsilon_mx M).
Proof. repeat intro. apply is_01_ofbool. Qed.

Hint Resolve is_01_mx_str is_01_mx_epsilon: mx_predicates.


(** ** simple matrices *)

(** any 01 matrix is simple  *)
Lemma is_01_simple_mx n m (M: rmx n m): is_01_mx M -> is_simple_mx M.
Proof. repeat intro. now apply is_01_simple. Qed.

Hint Resolve is_01_simple_mx: mx_predicates.

Lemma is_simple_mx_var v: is_simple_mx (scal_mx (var v)). 
Proof. constructor. Qed.

Lemma is_simple_mx_pls n m (M N: rmx n m): 
  is_simple_mx M -> is_simple_mx N -> is_simple_mx (M+N).
Proof. now constructor. Qed.

Lemma is_simple_mx_dot n m p (M: rmx n m) (N: rmx m p): 
  is_01_mx M -> is_simple_mx N -> is_simple_mx (M*N).
Proof. repeat intro. apply is_simple_sup. now constructor. Qed.

Hint Resolve is_simple_mx_var is_simple_mx_pls is_simple_mx_dot: mx_predicates.


(** ** pure matrices *)

Lemma is_pure_mx_zer n m: is_pure_mx (0: rmx n m). 
Proof. constructor. Qed.

Lemma is_pure_mx_var v: is_pure_mx (scal_mx (var v)). 
Proof. constructor. Qed.

Lemma is_pure_mx_pls n m (M N: rmx n m): is_pure_mx M -> is_pure_mx N -> is_pure_mx (M+N).
Proof. now constructor. Qed.

Lemma is_pure_mx_dot n m p (M: rmx n m) (N: rmx m p): is_01_mx M -> is_pure_mx N -> is_pure_mx (M*N).
Proof. repeat intro. apply is_pure_sup. now constructor. Qed.

Lemma is_pure_pure_part_mx n m (M: rmx n m): is_pure_mx (pure_part_mx M).
Proof. repeat intro. apply is_pure_pure_part. Qed.

Hint Resolve is_pure_mx_zer is_pure_mx_var is_pure_mx_pls is_pure_mx_dot is_pure_pure_part_mx: mx_predicates.

(** ** deriving and expanding various classes of matrices *)

Lemma deriv_01_mx a n m (M: rmx n m): is_01_mx M -> deriv_mx a M == 0.
Proof. intros HM i j. apply deriv_01, HM. Qed.

Lemma expand_01_mx n m (M: rmx n m): is_01_mx M -> M == epsilon_mx M.
Proof. intros H i j. now apply expand_01. Qed.

Lemma expand_simple_mx n m (M: rmx n m): is_simple_mx M -> M == epsilon_mx M + pure_part_mx M.
Proof. intros H i j. now apply expand_simple. Qed.

Lemma epsilon_mx_pure n m (M: rmx n m): is_pure_mx M -> epsilon_mx M == 0.
Proof. intros HM i j. unfold epsilon_mx, mx_map. rewrite epsilon_pure. reflexivity. apply HM. Qed.

Lemma epsilon_deriv_pure_mx a n m (M: rmx n m): is_pure_mx M -> 
  epsilon_mx (deriv_mx a M) == deriv_mx a M.
Proof. intros H i j. apply epsilon_deriv_pure, H. Qed.


(** * From 01 row matrices to sets of ordinals, and back *)

Definition of_row n (u: rmx 1 n): ord (pow2 n) := set.of_fun (fun i => epsilon (u ord0 i)).
Definition to_row n (x: ord (pow2 n)): rmx 1 n := fun _ i => ofbool (set.mem x i). 

Lemma mem_of_row n i (u: rmx 1 n): is_01_mx u -> 
  forall j, ofbool (set.mem (of_row u) j) == u i j.
Proof.
  intros Hu j. unfold of_row. rewrite set.mem_of_fun. 
  symmetry. setoid_rewrite ord0_unique. apply expand_01, Hu.
Qed.

Lemma is_01_mx_to_row n x: is_01_mx (@to_row n x).
Proof. intros ? ?. apply is_01_ofbool. Qed.

Hint Resolve is_01_mx_to_row: mx_predicates.
