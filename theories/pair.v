(** * pair: encoding pairs of ordinals as ordinals *)
(** more precisely, [ord n * ord m] into [ord (n*m)] *)

From Stdlib Require Import Psatz PeanoNat Compare_dec Euclid.
Require Import ordinal.

Set Asymmetric Patterns.
Set Implicit Arguments.
Local Open Scope ltb_scope.

(** equivalence between our Boolean strict order on [nat],
   and the standard one from the standard library  *)
Lemma ltb_lt x y: ltb x y = true <-> lt x y.
Proof.
  revert y. induction x; destruct y; simpl.
   split. discriminate. inversion 1. 
   split. lia. trivial. 
   split. discriminate. inversion 1. 
   rewrite IHx. lia. 
Qed.

(** auxiliary lemma *)
Lemma mk_lt n m x y: x<n -> y<m -> y*n+x < n*m. 
Proof. setoid_rewrite ltb_lt. nia. Qed.

(** since [x] is bounded by [n], we encode the pair [(x,y)] as [y*n+x] *)
Definition mk n m (x: ord n) (y: ord m): ord (n*m).
destruct x as [x Hx]; destruct y as [y Hy].
apply Ord with (y*n+x). 
now apply mk_lt. 
Defined. 

Lemma ord_nm_lt_O_n {n m} (x: ord (n*m)): lt 0 n. 
Proof. destruct n. elim (ord_0_empty x). lia. Qed.

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
apply ltb_lt in Hp. abstract nia.
Defined.

Lemma euclid_unique n: lt 0 n -> 
  forall x y x' y', lt x n -> lt x' n -> y*n+x = y'*n+x' -> y=y' /\ x=x'. 
Proof.
  intros Hn x y x' y' Hx Hx' H. rewrite Nat.mul_comm, (Nat.mul_comm y') in H. split. 
   erewrite Nat.div_unique. 3: eassumption. 2: assumption. 
   rewrite H. eapply Nat.div_unique. 2: symmetry; eassumption. assumption. 
   erewrite Nat.mod_unique. 3: eassumption. 2: assumption. 
   rewrite H. eapply Nat.mod_unique. 2: symmetry; eassumption. assumption. 
Qed.

(** projections behave as expected *)
Lemma pi1mk n m: forall x y, pi1 (@mk n m x y) = x.
Proof.
  intros [x Hx] [y Hy]. unfold pi1, mk. case eucl_dev. 
  intros y' x' Hx' H. apply eq_ord. apply euclid_unique in H as [_ ?]; auto.
  nia. now apply ltb_lt.
Qed.

Lemma pi2mk n m: forall x y, pi2 (@mk n m x y) = y.
Proof.
  intros [x Hx] [y Hy]. unfold pi2, mk. case eucl_dev. 
  intros y' x' Hx' H. apply eq_ord. simpl. apply euclid_unique in H as [? _]; auto.  
  nia. now apply ltb_lt.
Qed.

(** surjective pairing *)
Lemma mkpi12 n m: forall p, @mk n m (pi1 p) (pi2 p) = p.
Proof.
  intros [p Hp]. unfold pi1, pi2, mk. case eucl_dev. simpl. intros y x Hx Hy. 
  apply eq_ord. simpl. now rewrite Hy. 
Qed.
