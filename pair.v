(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * pair: encoding pairs of ordinals as ordinals *)
(** more precisely, [ord n * ord m] into [ord (n*m)] *)

Require Import Lt Peano_dec Compare_dec Mult Euclid NPeano. (* TODO: se passer de NPeano? *)
Require Import ordinal.

Set Asymmetric Patterns.
Set Implicit Arguments.

(** equivalence between our Boolean strict order on [nat],
   and the standard one from the standard library  *)
Lemma ltb_lt x y: ltb x y = true <-> lt x y.
Proof.
  revert y. induction x; destruct y; simpl.
   split. discriminate. inversion 1. 
   split. intro. apply lt_0_Sn. reflexivity. 
   split. discriminate. inversion 1. 
   rewrite IHx. split. apply lt_n_S. apply lt_S_n. 
Qed.

(** auxiliary lemma *)
Lemma mk_lt n m x y: x<n -> y<m -> y*n+x < n*m. 
Proof. 
  setoid_rewrite ltb_lt. 
  intros. apply lt_le_trans with (y*n+n). apply plus_le_lt_compat. apply le_n. assumption. 
  rewrite <-mult_succ_l, (mult_comm n). apply mult_le_compat. assumption. apply le_n. 
Qed.

(** since [x] is bounded by [n], we encode the pair [(x,y)] as [y*n+x] *)
Definition mk n m (x: ord n) (y: ord m): ord (n*m).
destruct x as [x Hx]; destruct y as [y Hy].
apply Ord with (y*n+x). 
now apply mk_lt. 
Defined. 

Lemma ord_nm_lt_O_n {n m} (x: ord (n*m)): lt 0 n. 
Proof. destruct n. elim (ord_0_empty x). apply lt_0_Sn. Qed.

(** first projection, by modulo *)
Definition pi1 {n m} (p: ord (n*m)): ord n := 
  let '(divex _ x Hx _) := eucl_dev n (ord_nm_lt_O_n p) p in (Ord x (proj2 (ltb_lt _ _) Hx)).

(** second projection, by division *)
Definition pi2 {n m} (p: ord (n*m)): ord m. 
destruct (eucl_dev n (ord_nm_lt_O_n p) p) as [y x Hx Hy]. 
apply Ord with y. 
unfold gt in *.
destruct p as [p Hp]. simpl in Hy. rewrite Hy in Hp. clear p Hy.  
destruct (le_lt_dec m y) as [Hy|Hy]. 2: now apply ltb_lt. exfalso.
apply ltb_lt in Hp. apply (mult_le_compat_l _ _ n) in  Hy. 
apply (lt_le_trans _ _ _ Hp) in Hy. rewrite mult_comm in Hy. 
apply ltb_lt in Hy. rewrite leb_plus_r in Hy. discriminate. 
Defined.

Lemma euclid_unique n: lt 0 n -> 
  forall x y x' y', lt x n -> lt x' n -> y*n+x = y'*n+x' -> y=y' /\ x=x'. 
Proof.
  intros Hn x y x' y' Hx Hx' H. rewrite mult_comm, (mult_comm y') in H. split. 
   erewrite Nat.div_unique. 3: eassumption. 2: assumption. 
   rewrite H. eapply Nat.div_unique. 2: symmetry; eassumption. assumption. 
   erewrite Nat.mod_unique. 3: eassumption. 2: assumption. 
   rewrite H. eapply Nat.mod_unique. 2: symmetry; eassumption. assumption. 
Qed.

(** projections bhave as expected *)
Lemma pi1mk n m: forall x y, pi1 (@mk n m x y) = x.
Proof.
  intros [x Hx] [y Hy]. unfold pi1, mk. case eucl_dev. 
  intros y' x' Hx' H. apply eq_ord. apply euclid_unique in H as [_ ?]; auto.  
  eapply le_lt_trans. apply le_0_n. eassumption. 
  now apply ltb_lt.
Qed.

Lemma pi2mk n m: forall x y, pi2 (@mk n m x y) = y.
Proof.
  intros [x Hx] [y Hy]. unfold pi2, mk. case eucl_dev. 
  intros y' x' Hx' H. apply eq_ord. simpl. apply euclid_unique in H as [? _]; auto.  
  eapply le_lt_trans. apply le_0_n. eassumption. 
  now apply ltb_lt.
Qed.

(** surjective pairing *)
Lemma mkpi12 n m: forall p, @mk n m (pi1 p) (pi2 p) = p.
Proof.
  intros [p Hp]. unfold pi1, pi2, mk. case eucl_dev. simpl. intros y x Hx Hy. 
  apply eq_ord. simpl. now rewrite Hy. 
Qed.
