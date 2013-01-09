(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * ordinal: finite ordinals, sets of finite ordinals *)

Require Import List.
Require Import common comparisons.

Set Implicit Arguments.

(** * Boolean strict order on natural numbers *)

Fixpoint ltb i j := 
  match i,j with
    | O,S _ => true
    | _,O   => false
    | S i, S j => ltb i j
  end.
Notation "i < j" := (ltb i j = true).
Notation "i <= j" := (ltb j i = false).

Lemma ltb_plus_l i m n: i<m -> i<m+n.
Proof. revert i; induction m; destruct i; simpl; auto; discriminate. Qed.

Lemma ltb_plus_r i m n: i<n -> m+i<m+n.
Proof. revert i; induction m; destruct i; simpl; auto; discriminate. Qed.

Lemma leb_plus_r i n: n <= n+i.
Proof. induction n; simpl. now destruct i. assumption. Qed.

Lemma ltb_minus n m i: i<n+m -> n <= i -> i-n < m.
Proof. revert n. induction i; destruct n; simpl; auto. discriminate. Qed.

Lemma lt_n_1 a: a<1 -> a=0.
Proof. destruct a as [|[|?]]; trivial; discriminate. Qed.

Definition lt_ge_dec i n: {i<n}+{n<=i}.
Proof. case_eq (ltb i n). now left. now right. Defined.

(** * Additional induction schemes for natural numbers *)

Lemma ltb_ind (P: nat -> nat -> Prop)
  (H0: forall n, P (S n) 0)
  (HS: forall n i, P n i -> P (S n) (S i)): 
  forall n i, i<n -> P n i.
Proof. 
  induction n; intros i Hi. destruct i; discriminate. 
  destruct i. apply H0. now apply HS, IHn.
Qed.

Lemma nat_ind_2: forall P: nat -> Prop, 
  P 0 -> P 1 -> (forall n, P n -> P ((S (S n)))) -> forall n, P n.
Proof.
  intros P H0 H1 HSS.
  assert (G: forall m, P m /\ P (S m)).
   induction m. split; assumption. 
   destruct IHm as [IHm IHSm].
   split. assumption. apply (HSS m), IHm.
  intro n. destruct (G n). assumption. 
Qed.


(** * Ordinals *)
(** we use a record rather than a dependent inductive in order to
   - get slightly more efficient computations
   - get simpler proofs
   using a Boolean strict order also simplifies proofs w.r.t. using the lt
   predicate from the standard library *)
Record ord n := Ord {nat_of_ord:> nat; ord_lt: nat_of_ord<n}.
Arguments Ord [_] i _: rename.

(** zero and successor *)
Definition ord0 {n}: ord (S n) := @Ord (S n) 0 eq_refl.
Definition ordS {n} (i: ord n): ord (S n) := @Ord (S n) (S i) (ord_lt i).

(** ** ordinals as a [cmpType] *)
(** we just compare the underlying natural numbers *)
Definition eqb_ord {n} (i j: ord n) := eqb_nat i j.

Lemma eq_ord n (i j: ord n): @eq nat i j -> i=j. 
Proof. destruct i; destruct j; simpl; intro. subst. f_equal. apply UIP_cmp. Qed.

Lemma eqb_ord_spec n (i j: ord n): reflect (i=j) (eqb_ord i j).
Proof.
  unfold eqb_ord. case eqb_spec; intro E; constructor.
  apply eq_ord, E. congruence.
Qed.

Definition ord_compare {n} (i j: ord n) := nat_compare i j. 
Lemma ord_compare_spec n (i j: ord n): compare_spec (i=j) (ord_compare i j).
Proof. 
  unfold ord_compare.
  case cmp_spec; constructor; try apply eq_ord; congruence. 
Qed.

Canonical Structure cmp_ord n := mk_cmp _ (@eqb_ord_spec n) _ (@ord_compare_spec n).

(** ** basic properties  *)

(** [ord 0] is empty *)
Lemma ord_0_empty: ord 0 -> False.
Proof. intros [[|?]]; discriminate. Qed.

(** [ord 1] has only one element: 0 *)
Lemma ord0_unique: forall i: ord 1, i=ord0.
Proof. 
  intros [[|i] Hi]; apply eq_ord. reflexivity.
  destruct i; discriminate. 
Qed. 

(** induction scheme for ordinals *)
Lemma ord_ind' (P: forall n, ord n -> Prop) 
  (H0: forall n, P (S n) ord0)
  (HS: forall n i, P n i -> P (S n) (ordS i)): 
  forall n i, P n i.
Proof. 
  induction n. intro i. elim (ord_0_empty i).
  destruct i as [[|i] Hi].
   replace (Ord 0 Hi) with (@ord0 n) by now apply eq_ord. apply H0. 
   replace (Ord (S i) Hi) with (ordS (@Ord n i Hi)) by now apply eq_ord. apply HS, IHn. 
Qed.

(** ** sequence of all ordinals below [n]  *)
Fixpoint seq n: list (ord n) := 
  match n with 
    | 0 => nil
    | S n => cons ord0 (map ordS (seq n))
  end.

(** completeness of the above sequence *)
Lemma in_seq: forall {n} (i: ord n), In i (seq n).
Proof. 
  induction i using ord_ind'. now left.
  right. rewrite in_map_iff. eauto. 
Qed.


(** ** shifting ans splitting ordinals *)

(** shifting *)
Definition lshift {m n} (i: ord m): ord (m+n) := Ord i (ltb_plus_l _ _ _ (ord_lt i)).
Definition rshift {m n} (i: ord n): ord (m+n) := Ord (m+i) (ltb_plus_r _ _ _ (ord_lt i)).

(** spliting the sequence of all ordinals *)
Lemma seq_cut n m: seq (n+m) = map lshift (seq n) ++ map rshift (seq m).
Proof. 
  induction n; simpl.
   rewrite <-(map_id (seq m)) at 1. apply map_ext. 
   intros [i Hi]. apply eq_ord. reflexivity.
   rewrite IHn, map_app. f_equal. apply eq_ord. reflexivity. 
   rewrite 3map_map. f_equal; apply map_ext; intros [i Hi]; apply eq_ord; reflexivity.
Qed.

(** splitting an ordinal *)
Definition split {n m} (i: ord (n+m)): ord n + ord m :=
  match lt_ge_dec i n with
    | left Hi => inl _ (Ord _ Hi)
    | right Hj => inr _ (Ord _ (ltb_minus _ _ _ (ord_lt i) Hj))
  end.
  
Inductive split_case n m (i: ord (n+m)): ord n + ord m -> Set :=
  | split_l: forall j: ord n, i=lshift j -> split_case i (inl j)
  | split_r: forall j: ord m, i=rshift j -> split_case i (inr j).

Lemma split_spec n m (i: ord (n+m)): split_case i (split i).
Proof. 
  unfold split. case lt_ge_dec; constructor; apply eq_ord; simpl. reflexivity. 
  destruct i as [j Hj]. simpl in *. revert n m e Hj. 
  induction j; destruct n; simpl; auto. discriminate. 
  intros. f_equal. eapply IHj; eassumption.
Qed.

(** basic properties of split and shifting *)
Lemma split_lshift n m i: @split n m (lshift i) = inl i.
Proof. 
  case split_spec; intros j E. 
  f_equal. apply eq_ord. injection E. congruence. 
  exfalso. injection E. clear E. destruct i as [i Hi]. 
  simpl. intros ->. rewrite leb_plus_r in Hi. discriminate.
Qed.

Lemma split_rshift n m i: @split n m (rshift i) = inr i.
Proof. 
  case split_spec; intros j E. 
  exfalso. injection E. clear E. destruct j as [j Hj]. simpl. intros <-. 
   rewrite leb_plus_r in Hj. discriminate. 
  f_equal. apply eq_ord. symmetry. injection E. apply Plus.plus_reg_l.
Qed.

Lemma eqb_ord_lrshift n m i j: eqb_ord (@lshift n m i) (@rshift n m j) = false.
Proof. 
  destruct i as [i Hi]; destruct j as [j Hj]. unfold eqb_ord. simpl.
  case eqb_spec; trivial. intro E. rewrite E in Hi. rewrite leb_plus_r in Hi. discriminate. 
Qed.

Lemma eqb_ord_rlshift n m i j: eqb_ord (@rshift n m i) (@lshift n m j) = false.
Proof. rewrite eqb_sym. apply eqb_ord_lrshift. Qed.

Lemma eqb_ord_rrshift n m i j: eqb_ord (@rshift n m i) (@rshift n m j) = eqb_ord i j.
Proof. 
  destruct i as [i Hi]; destruct j as [j Hj]. unfold eqb_ord. simpl.
  do 2 case eqb_spec; trivial. intros E E'. elim E. eapply Plus.plus_reg_l, E'. 
  congruence. 
Qed.

Lemma split_ord0 m: @split 1 m ord0 = inl ord0. 
Proof. reflexivity. Qed. 

Lemma split_ordS m i: @split 1 m (ordS i) = inr i. 
Proof.
  case split_spec; intros j Hj.
   rewrite (ord0_unique j) in Hj. discriminate. 
  destruct i; destruct j. injection Hj. intros <-. f_equal. now apply eq_ord. 
Qed.



(** * Finite sets of ordinals as ordinals *)

(** we encode a finite subset of [ord n] as an element of [ord (2^n)], 
   using the coding of the characteristic function of the set as a 
   bitvector of length n 

   since we need to compute a little bit with these encoded sets, we
   first define the bijection on natural numbers, before encapsulating
   into ordinals. *)
Module set.

(** ** on natural numbers *)

(** [xO' i = 2*i], [xI' i = 2*i+1] *)
Fixpoint xO' i := match i with 0 => 0 | S i => S (S (xO' i)) end.
Fixpoint xI' i := match i with 0 => 1 | S i => S (S (xI' i)) end.

(** from characteristic functions to natural numbers: accumulate bits
   until a given length [(n)] is reached *)
Fixpoint of_fun' n (f: nat -> bool): nat :=
  match n with
    | 0 => 0
    | S n => if f 0
      then xI' (of_fun' n (fun i => f (S i)))
      else xO' (of_fun' n (fun i => f (S i)))
  end.

(** [od x] returns the pair [(o,y)] s.t. [x = 2*y+o]  *)
Fixpoint od x := 
  match x with 
    | O => (false,O) 
    | S O => (true,O)
    | S (S x) => let (o,x) := od x in (o,S x)
  end.

(** testing membership: read the [i]th bit, using [od] *)
(** this function is presented in such a strange way to get efficiency: 
    the partial application [mem' n x] reduces to the pattern matching function 
    that precisely corresponds to the membership function of [x]. For instance, 
    [mem' 4 {1,2}] reduces to 
    [fun i => match i with 0 | 3 => false | 1 | 2 => true | _ => assert_false end] *)
Fixpoint mem' n x := 
  match n with 
    | 0 => fun i => assert_false false
    | S n => 
      let (o,x) := od x in 
      let f := mem' n x in 
      fun i => match i with O => o | S i => f i end
  end.

(** correctness of [mem'] and [of_fun'] *)
Lemma od_xO i: od (xO' i) = (false,i).
Proof. induction i; simpl. reflexivity. now rewrite IHi. Qed.

Lemma od_xI i: od (xI' i) = (true,i).
Proof. induction i; simpl. reflexivity. now rewrite IHi. Qed.

Lemma mem_of_fun' n: forall f i, i<n -> mem' n (of_fun' n f) i = f i.
Proof.
  induction n; intros f i Hi; simpl. destruct i; discriminate.
  case_eq (f 0); intro H. 
   rewrite od_xI. destruct i. congruence. now rewrite IHn.
   rewrite od_xO. destruct i. congruence. now rewrite IHn.
Qed.

(** ** encapsulation into ordinals *)

(** bounds about the various operations *)
Lemma xO_bound: forall n i, i<n -> xO' i < double n.
Proof. now apply ltb_ind. Qed.

Lemma xI_bound: forall n i, i<n -> xI' i < double n.
Proof. now apply ltb_ind. Qed.

Lemma of_fun_bound: forall n f, of_fun' n f < pow2 n.
Proof.
  induction n; intro f. reflexivity. 
  simpl. case f.
   now apply xI_bound. 
   now apply xO_bound. 
Qed.

Lemma od_bound a: forall n, a < double n -> snd (od a) < n.
Proof.
  induction a using nat_ind_2; intros n Hn; simpl.
   destruct n; simpl. discriminate. reflexivity.
   destruct n; simpl. discriminate. reflexivity. 
  revert IHa. case od; simpl. intros o a' IH. 
  destruct n. discriminate. apply IH, Hn. 
Qed.

(** extending a Boolean function on ordinals into a function on natural numbers *)
Definition app' n (f: ord n -> bool) (i: nat) :=
  match lt_ge_dec i n with
    | left H => f (Ord i H)
    | _ => false
  end.

(** encapsulation of the various operations into ordinals *)
Definition xO n (i: ord n): ord (double n) := Ord (xO' i) (xO_bound _ _ (ord_lt i)).
Definition xI n (i: ord n): ord (double n) := Ord (xI' i) (xI_bound _ _ (ord_lt i)).
Definition mem n (x: ord (pow2 n)) (i: ord n) := mem' n x i.
Definition of_fun n (f: ord n -> bool): ord (pow2 n) := Ord (of_fun' n (app' f)) (of_fun_bound _ _). 
(** retraction from [ord n -> bool] into [ord (pow2 n)] *)
Lemma mem_of_fun n (f: ord n -> bool) i: mem (of_fun f) i = f i.
Proof.
  unfold mem, of_fun. simpl. rewrite mem_of_fun' by apply ord_lt.
  unfold app'. case lt_ge_dec. intros. f_equal. now apply eq_ord. 
  rewrite (ord_lt i). discriminate.  
Qed.

(** injectivity of the [od] function *)
Lemma od_inj a b: od a = od b -> a = b. 
Proof.
  revert b. induction a using nat_ind_2; intros [|[|b]]; simpl; 
   trivial; (try (case od; discriminate)); (try discriminate). 
  intro. f_equal. f_equal. apply IHa. revert H. 
  case od. case od. congruence.
Qed.

(** extensionality on natural numbers *)
Lemma ext' n: forall a b, 
  a<pow2 n -> b<pow2 n -> (forall i, i<n -> mem' n a i = mem' n b i) ->
  a = b. 
Proof.
  induction n; simpl; intros a b Ha Hb H. 
   rewrite lt_n_1 by assumption. now apply lt_n_1.
   apply od_inj. revert H. generalize (od_bound _ _ Ha), (od_bound _ _ Hb).
   case od. intros oa a' Ha'. 
   case od. intros ob b' Hb'. 
   intro H. f_equal. 
    apply (H 0 eq_refl). 
    apply IHn; trivial. intros i Hi. apply (H (S i) Hi). 
Qed.

(** extensionality on ordinals (i.e., with [mem_of_fun], mem/of_fun form a bijection) *)
Lemma ext n (a b: ord (pow2 n)): (forall i, mem a i = mem b i) -> a = b. 
Proof.
  intro H. apply eq_ord. eapply ext'. apply ord_lt. apply ord_lt.
  intros i Hi. apply (H (Ord i Hi)). 
Qed.

(** ** additional lemmas *)

Lemma xO_0 n: xO (@ord0 n) = @ord0 (S (double n)).
Proof. now apply eq_ord. Qed.
Lemma xO_S n (i: ord n): xO (ordS i) = ordS (ordS (xO i)).
Proof. now apply eq_ord. Qed.
Lemma xI_0 n: xI (@ord0 n) = ordS (@ord0 (double n)). 
Proof. now apply eq_ord. Qed.
Lemma xI_S n (i: ord n): xI (ordS i) = ordS (ordS (xI i)).
Proof. now apply eq_ord. Qed.

Lemma mem_xO_0 n (f: ord (pow2 n)): @mem (S n) (xO f) ord0 = false.
Proof. unfold mem. simpl. now rewrite od_xO. Qed.
Lemma mem_xO_S n (f: ord (pow2 n)) i: @mem (S n) (xO f) (ordS i) = mem f i.
Proof. unfold mem. simpl. now rewrite od_xO. Qed.
Lemma mem_xI_0 n (f: ord (pow2 n)): @mem (S n) (xI f) ord0 = true.
Proof. unfold mem. simpl. now rewrite od_xI. Qed.
Lemma mem_xI_S n (f: ord (pow2 n)) i: @mem (S n) (xI f) (ordS i) = mem f i.
Proof. unfold mem. simpl. now rewrite od_xI. Qed.

End set.

