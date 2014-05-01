(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * matrix: constructing matrices over the various typed structures 
   
   Given an [l]-monoid structure, we build an [l]-monoid of matrices
   above it.  This works whenever we have unions and bottom elements
   ([BSL<<l]) for structures without residuals; to build residuals, we
   moreover need intersections and top elements ([BDL<<l]).
   
   We do these constructions once and forall, thanks to our
   first-class level constraints.

   We can build rectangular matrices, and not only square ones, thanks
   to our typed structures: [MX n m] denotes the set of [(n,m)]-matrices. *)

Require Export comparisons.
Require Import kleene sums normalisation.

(** A matrix of size [(n,m)] over a set [X] is just a curried function
   from indices ([ord n * ord m]) to [X] *)
Definition mx X n m := ord n -> ord m -> X.

(** * [(n,m)]-matrices as a lattice *)

(** when X is a lattice, matrix lattice operations and laws are
   obtained for free, by two successive pointwise liftings of X *)

Canonical Structure mx_lattice_ops (X: lattice.ops) n m := 
  lattice.mk_ops (mx X n m) leq weq cup cap neg bot top.

Instance mx_lattice_laws `{L: lattice.laws} n m: lattice.laws l (mx_lattice_ops X n m).
Proof. apply pw_laws. Qed.

(** supremums (or sums) are computed pointwise *)
Lemma mx_sup `{X: lattice.ops} n m I J (f: I -> mx X n m) i j:
  (\sup_(x\in J) f x) i j = \sup_(x\in J) f x i j.
Proof. apply (f_sup_eq (fun x: mx X n m => x i j)); now f_equal. Qed.

Section d.

Context {X: Type}.
Notation mx := (mx X).

(** ** scalar (1,1)-matrices *)

Definition scal_mx x: mx 1 1 := fun _ _ => x.
Definition mx_scal (M: mx 1 1) := M ord0 ord0.

(** ** block matrix operations *)

(** following ssreflect methodology, we decompose the standard block
   matrix construction, with four quadrants, into two constructions,
   for column and line block matrices. *)

Definition col_mx {n1 n2 m} (M1: mx n1 m) (M2: mx n2 m): mx (n1+n2) m :=
  fun i j => 
    match split i with
      | inl i1 => M1 i1 j
      | inr i2 => M2 i2 j
    end.
Definition row_mx {n m1 m2} (M1: mx n m1) (M2: mx n m2): mx n (m1+m2) :=
  fun i j => 
    match split j with
      | inl j1 => M1 i j1
      | inr j2 => M2 i j2
    end.

Definition blk_mx {n1 n2 m1 m2} (A: mx n1 m1) (B: mx n1 m2) (C: mx n2 m1) (D: mx n2 m2) :=
  col_mx (row_mx A B) (row_mx C D).

Definition tsub_mx {n1 n2 m} (M: mx (n1+n2) m): mx n1 m :=
  fun i j => M (lshift i) j.
Definition bsub_mx {n1 n2 m} (M: mx (n1+n2) m): mx n2 m :=
  fun i j => M (rshift i) j.
Definition lsub_mx {n m1 m2} (M: mx n (m1+m2)): mx n m1 :=
  fun i j => M i (lshift j).
Definition rsub_mx {n m1 m2 }(M: mx n (m1+m2)): mx n m2 :=
  fun i j => M i (rshift j).

Definition sub00_mx {n1 n2 m1 m2} (M: mx (n1+n2) (m1+m2)) := tsub_mx (lsub_mx M).
Definition sub01_mx {n1 n2 m1 m2} (M: mx (n1+n2) (m1+m2)) := tsub_mx (rsub_mx M).
Definition sub10_mx {n1 n2 m1 m2} (M: mx (n1+n2) (m1+m2)) := bsub_mx (lsub_mx M).
Definition sub11_mx {n1 n2 m1 m2} (M: mx (n1+n2) (m1+m2)) := bsub_mx (rsub_mx M).

End d.

(** all block matrix operations are monotone *)

Instance col_mx_leq `{L: lattice.laws} n1 n2 m: Proper (leq ==> leq ==> leq) (@col_mx X n1 n2 m).
Proof. 
  intros ? ? H ? ? H' i j. unfold col_mx. 
  case split_spec; intros ? ->. apply H. apply H'. 
Qed.
Instance col_mx_weq `{L: lattice.laws} n1 n2 m: Proper (weq ==> weq ==> weq) (@col_mx X n1 n2 m)
  := op_leq_weq_2.

Lemma col_mx_leq_iff `{L: lattice.laws} n1 n2 m M1 M2 N1 N2: 
  @col_mx X n1 n2 m M1 M2 <== col_mx N1 N2 <-> M1<==N1 /\ M2<==N2.
Proof.
  split. unfold col_mx. intro H. split; intros i j.
  generalize (H (lshift i) j). now rewrite split_lshift. 
  generalize (H (rshift i) j). now rewrite split_rshift. 
  intros [? ?]. now apply col_mx_leq.
Qed.

Instance row_mx_leq `{L: lattice.laws} n m1 m2: Proper (leq ==> leq ==> leq) (@row_mx X n m1 m2).
Proof. 
  intros ? ? H ? ? H' i j. unfold row_mx. 
  case split_spec; intros i' ->. apply H. apply H'.
Qed.
Instance row_mx_weq `{L: lattice.laws} n m1 m2: Proper (weq ==> weq ==> weq) (@row_mx X n m1 m2)
  := op_leq_weq_2.

Lemma row_mx_leq_iff `{L: lattice.laws} n m1 m2 M1 M2 N1 N2: 
  @row_mx X n m1 m2 M1 M2 <== row_mx N1 N2 <-> M1<==N1 /\ M2<==N2.
Proof.
  split. unfold row_mx. intro H. split; intros i j.
  generalize (H i (lshift j)). now rewrite split_lshift. 
  generalize (H i (rshift j)). now rewrite split_rshift. 
  intros [? ?]. now apply row_mx_leq.
Qed.

Instance blk_mx_leq `{L: lattice.laws} n1 n2 m1 m2: 
  Proper (leq ==> leq ==> leq ==> leq ==> leq) (@blk_mx X n1 n2 m1 m2).
Proof. do 12 intro. now apply col_mx_leq; apply row_mx_leq. Qed.

Instance blk_mx_weq `{L: lattice.laws} n1 n2 m1 m2:
  Proper (weq ==> weq ==> weq ==> weq ==> weq) (@blk_mx X n1 n2 m1 m2).
Proof. do 12 intro. now apply col_mx_weq; apply row_mx_weq. Qed.


Lemma blk_mx' `{L: lattice.laws} {n1 n2 m1 m2} A B C D: 
  @blk_mx X n1 n2 m1 m2 A B C D == row_mx (col_mx A C) (col_mx B D).
Proof. 
  intros i j. unfold blk_mx, row_mx, col_mx. 
  case split; case split; intros; reflexivity. 
Qed.

Lemma to_col_mx `{L: lattice.laws} {n1 n2 m} (M: mx X (n1+n2) m):
  M == col_mx (tsub_mx M) (bsub_mx M).
Proof.
  intros i j. unfold col_mx, tsub_mx, bsub_mx.
  now case split_spec; intros i' ->.
Qed.

Lemma to_row_mx `{L: lattice.laws} {n m1 m2} (M: mx X n (m1+m2)):
  M == row_mx (lsub_mx M) (rsub_mx M).
Proof.
  intros i j. unfold row_mx, lsub_mx, rsub_mx.
  now case split_spec; intros i' ->.
Qed.

Lemma to_blk_mx `{L: lattice.laws} {n1 n2 m1 m2} (M: mx X (n1+n2) (m1+m2)):
  M == blk_mx (sub00_mx M) (sub01_mx M) (sub10_mx M) (sub11_mx M).
Proof. rewrite to_row_mx at 1. rewrite to_col_mx at 1 2. reflexivity. Qed.

Lemma col_mx_cup `{L: lattice.laws} n1 n2 m M M' N N': 
  @col_mx X n1 n2 m (M\cup M') (N\cup N') == col_mx M N \cup col_mx M' N'.
Proof. intros i j. unfold col_mx. simpl. case split; reflexivity. Qed.

Lemma row_mx_cup `{L: lattice.laws} n m1 m2 M M' N N': 
  @row_mx X n m1 m2 (M\cup M') (N\cup N') == row_mx M N \cup row_mx M' N'.
Proof. intros i j. unfold row_mx. simpl. case split; reflexivity. Qed.



(** * [(n,m)]-matrices as a monoid *)

(** when [X] is at least an idempotent semiring ([BSL]), the set of matrices
   has a monoid structure *)

(** Note: since the underlying monoid ([X]) is typed a priori, we
   could do a much more general matrix construction, using heavily
   dependent types. We do not need it since we actually construct
   matrices on [bool], [Prop], and [regex], which are all flat
   monoids.  Therefore, we simply fix a object [u] of [X], and we
   construct matrices on [X u u]. ([u] will be instantiated with the
   unique objects of the aformentioned models.) *)

Section m.
Variable X: ops.
Variable u: ob X.
Notation U := (car (@mor X u u)).
Notation mx := (mx U).

(** identity matrix  *)
Definition mx_one n: mx n n := 
  fun i j => ofbool (eqb_ord i j).

(** matrix product  *)
Definition mx_dot n m p (M: mx n m) (N: mx m p): mx n p := 
  fun i k => \sum_(j<m) M i j * N j k.
Local Infix "**" := (mx_dot _ _ _) (at level 40).

(** left and right residuals (using infimums, as explained above)  *)
Definition mx_ldv n m p (M: mx n m) (N: mx n p): mx m p := 
  fun j k => \inf_(i<n) (M i j -o N i k).

Definition mx_rdv n m p (M: mx m n) (N: mx p n): mx p m := 
  fun k j => \inf_(i<n) (N k i o- M j i).

(** transposed matrix (note that the elements are also transposed) *)
Definition mx_cnv n m (M: mx n m): mx m n :=
  fun i j => M j i `.

(** Kleene star of a matrix, defined inductively, by block matrix constructions *)

(** we follow standard textbooks and papers, except that we define
   first an auxiliary function, which we iterate to get the final
   matrix construction: this allows us to state easily that the actual
   block decomposition used doesn't matter [matrix_ext.mx_str_blk] *)

Definition mx_str_build n m 
  (sn: mx n n -> mx n n) (sm: mx m m -> mx m m) 
  (M: mx (n+m) (n+m)): mx (n+m) (n+m) :=
  let a := sub00_mx M in
  let b := sub01_mx M in
  let c := sub10_mx M in
  let d := sub11_mx M in
  let e := sm d in
  let be:= b**e in
  let ec:= e**c in
  let f := sn (a \cup be**c) in
  let fbe := f**be in
  let ecf := ec**f in
    blk_mx f fbe ecf (e \cup ecf**be).

Fixpoint mx_str n: mx n n -> mx n n :=
  match n with
    | O => fun M => M
    | S n => mx_str_build 1 n (fun M => scal_mx (mx_scal M ^*)) (mx_str n)
  end.

(** strict iteration is derived from Kleene star *)
Definition mx_itr n M := M ** mx_str n M.

(** packing all operations as a canonical structure *)
Canonical Structure mx_ops := 
  mk_ops nat _ mx_dot mx_one mx_itr mx_str mx_cnv mx_ldv mx_rdv.

End m.



(** ** matrices form a BSL-monoid *)

(** we prove that the matrix constructions are correct in two steps:
   we first get the BSL-structure (idempotent semirings), and then we
   add the laws corresponding to the other operations. This allows us
   to benefit from tools about idempotent semirings for the latter
   proofs, notably for Kleene star. *)

Section bsl.
Context `{L: laws} `{Hl: BSL<<l} {u: ob X}.
Notation U := (car (@mor X u u)).
Notation mx := (mx U).

Import lset.Fix.

(** matrix product is associative *)
Lemma mx_dotA n m p q (M: mx n m) N (P: mx p q): M*(N*P) == (M*N)*P.
Proof.
  intros i j. simpl. unfold mx_dot.
  setoid_rewrite dotxsum. rewrite sup_swap. 
  apply sup_weq; trivial. intro. rewrite dotsumx. 
  apply sup_weq; trivial. intro. apply dotA.
Qed.

(** and admits identities as left and right units *)
Lemma mx_dot1x n m (M: mx n m): 1*M == M.
Proof.
  intros i j. simpl. unfold mx_dot, mx_one. apply antisym.
   apply leq_supx. intros i' _. case eqb_ord_spec; simpl.
    intros <-. apply weq_leq, dot1x.
    intros _. rewrite dot0x. apply leq_bx.
   rewrite <- (leq_xsup _ _ i) by apply in_seq. 
   rewrite eqb_refl. simpl. now rewrite dot1x.
Qed.

Lemma mx_dotx1 n m (M: mx m n): M*1 == M.
Proof.
  intros i j. simpl. unfold mx_dot, mx_one. apply antisym.
   apply leq_supx. intros i' _. case eqb_ord_spec; simpl.
    intros <-. apply weq_leq, dotx1.
    intros _. rewrite dotx0. apply leq_bx.
   rewrite <- (leq_xsup _ _ j) by apply in_seq. 
   rewrite eqb_refl. simpl. now rewrite dotx1.
Qed.

(** matrix product is monotone *)
Lemma mx_dot_leq n m p: Proper (leq ==> leq ==> leq) (mx_dot X u n m p).
Proof. 
  intros ? ? H ? ? H' i j. apply sup_leq; trivial. intro k.
  apply dot_leq. apply H. apply H'.
Qed.

(** matrix product distributes over the sup-semilattice structure *)

Import lset.Fix.

Lemma mx_dotplsx_ n m p (M N: mx n m) (P: mx m p): (M+N)*P <== M*P+N*P.
Proof. intros i j. simpl. unfold mx_dot. setoid_rewrite dotplsx. now rewrite supcup. Qed.

Lemma mx_dotxpls_ n m p (M N: mx m n) (P: mx p m): P*(M+N) <== P*M+P*N.
Proof. intros i j. simpl. unfold mx_dot. setoid_rewrite dotxpls. now rewrite supcup. Qed.

Lemma mx_dot0x_ n m p (P: mx m p): (zer n m)*P <== 0.
Proof. 
  intros i j. simpl. unfold mx_dot. setoid_rewrite dot0x. 
  apply leq_supx. intros. apply leq_bx. 
Qed.

Lemma mx_dotx0_ n m p (P: mx p m): P*(zer m n) <== 0.
Proof. 
  intros i j. simpl. unfold mx_dot. setoid_rewrite dotx0. 
  apply leq_supx. intros. apply leq_bx. 
Qed.

(** packing everything, we get a [BSL]-monoid structure *)
Local Instance mx_bsl_laws: laws BSL (mx_ops X u).
Proof. 
  constructor; try discriminate; repeat right. 
  intros. apply lower_lattice_laws.
  exact mx_dotA.
  exact mx_dot1x. 
  exact mx_dotx1. 
  exact mx_dot_leq.
  exact mx_dotplsx_.
  exact mx_dotxpls_.
  exact mx_dot0x_.
  exact mx_dotx0_.
Qed.

(** ** properties of block matrix multiplication *)

Lemma mx_dot_colx n1 n2 m p (M1: mx n1 m) (M2: mx n2 m) (N: mx m p):
  col_mx M1 M2 * N == col_mx (M1*N) (M2*N).
Proof. intros i j. simpl. unfold mx_dot, col_mx. now case split_spec; intros i' ->. Qed.

Lemma mx_dot_xrow n m1 m2 p (M1: mx n m1) (M2: mx n m2) (N: mx p n):
  N * row_mx M1 M2 == row_mx (N*M1) (N*M2).
Proof. intros i j. simpl. unfold mx_dot, row_mx. now case split_spec; intros i' ->. Qed.

Lemma mx_dot_colrow n1 n2 m p1 p2 (M1: mx n1 m) (M2: mx n2 m) (N1: mx m p1) (N2: mx m p2):
  col_mx M1 M2 * row_mx N1 N2 == blk_mx (M1*N1) (M1*N2) (M2*N1) (M2*N2).
Proof. now rewrite mx_dot_colx, 2mx_dot_xrow. Qed.

Lemma mx_dot_rowcol n m1 m2 p (M1: mx n m1) (M2: mx n m2) (N1: mx m1 p) (N2: mx m2 p):
  row_mx M1 M2 * col_mx N1 N2 == M1*N1 + M2*N2.
Proof.
  intros i j. setoid_rewrite sup_cut. unfold row_mx, col_mx. 
  setoid_rewrite split_lshift. setoid_rewrite split_rshift. reflexivity. (* LONG *)
Qed.

Lemma mx_dot_blk n1 n2 m1 m2 p1 p2 
  (M11: mx n1 m1) (M12: mx n1 m2) (M21: mx n2 m1) (M22: mx n2 m2)
  (N11: mx m1 p1) (N12: mx m1 p2) (N21: mx m2 p1) (N22: mx m2 p2):
  blk_mx M11 M12 M21 M22 * blk_mx N11 N12 N21 N22 == 
  blk_mx (M11*N11+M12*N21) (M11*N12+M12*N22) (M21*N11+M22*N21) (M21*N12+M22*N22).
Proof.
  setoid_rewrite blk_mx' at 2. setoid_rewrite mx_dot_colrow.
  now rewrite 4mx_dot_rowcol.
Qed.

Lemma one_blk_mx n m: (1: mx (n+m) (n+m)) == blk_mx 1 0 0 1.
Proof.
  intros i j. unfold blk_mx, col_mx, row_mx. 
  case split_spec; intros [i' Hi] ->; case split_spec; intros [j' Hj] ->.
   reflexivity.
   simpl. unfold mx_one. now setoid_rewrite eqb_ord_lrshift.
   simpl. unfold mx_one. now setoid_rewrite eqb_ord_rlshift.
   simpl. unfold mx_one. now setoid_rewrite eqb_ord_rrshift.
Qed.

End bsl.


(** ** matrices have a converse if the underlying monoid has one  *)

Section cbsl.
Context `{L: laws} `{Hl: BSL+CNV<<l} {u: ob X}.
Notation U := (car (@mor X u u)).
Notation mx := (mx U).

Canonical Structure lset_ops A := lattice.mk_ops (list A)
  (fun h k => forall a, List.In a h -> List.In a k)
  (fun h k => forall a, List.In a h <-> List.In a k)
  (@app A) (@app A) (assert_false id) (@nil A) (@nil A).

Lemma mx_cnvdot_ n m p (M: mx n m) (N: mx m p): (M*N)` <== N`*M`.
Proof. intros i j. setoid_rewrite cnvsum. now setoid_rewrite cnvdot. Qed.

Lemma mx_cnv_invol n m (M: mx n m): M`` == M.
Proof. intros i j. apply cnv_invol. Qed.

Lemma mx_cnv_leq n m: Proper (leq ==> leq) (mx_cnv X u n m).
Proof. intros ? ? H i j. apply cnv_leq, H. Qed.

Lemma mx_cnv_ext n m (M: mx n m): M <== M*M`*M.
Proof. 
  intros i j. simpl. unfold mx_dot, mx_cnv. setoid_rewrite dotsumx. 
  rewrite <- (leq_xsup _ _ i) by apply in_seq. 
  rewrite <- (leq_xsup _ _ j) by apply in_seq. 
  apply cnv_ext.
Qed.

End cbsl.

(** ** matrices have a Kleene star if the underlying monoid has one  *)

Section ka.
Context `{L: laws} `{Hl: BKA<<l} {u: ob X}.
Notation U := (car (@mor X u u)).
Notation mx := (mx U).

Existing Instance mx_bsl_laws.


Section build.

(** *** properties of the auxiliary [mx_str_build] functional   *)

(** we prove a slightly more general property about the auxiliary
   [mx_str_build] functionnal, so that we can reuse these proofs to
   establish properties of Kleene star on arbitrary block matrices *)

Variables (n m: nat) (sn: mx n n -> mx n n) (sm: mx m m -> mx m m).
Notation s := (mx_str_build X u n m sn sm).

(** we want to show that the auxiliary [mx_str_build] functionnal
   preserves some invariants ; this is easier to state with the
   following definition *)

Definition transfers (P: forall {p}, mx p p -> mx p p -> Prop) := 
  (forall M, P M (sn M)) -> 
  (forall M, P M (sm M)) -> 
  (forall M, P M (s  M)).

(** dedicated tactic to unfold [mx_str_build] without losing the
   sharing between the various expressions *)
Ltac unfold_s M :=
  set (a := sub00_mx M);
  set (b := sub01_mx M);
  set (c := sub10_mx M);
  set (d := sub11_mx M);
  set (e := sm d);
  set (f := sn (a + (b*e)*c));
  change (s M) with (blk_mx f (f*(b*e)) ((e*c)*f) (e+((e*c)*f)*(b*e))).

(** [mx_str_build] preserves the left star unfolding axiom *)
Lemma mx_str_build_unfold_l: transfers (fun n M sM => 1+M*sM <== sM).
Proof.
  intros Hf He M. rewrite (to_blk_mx M) at 1. unfold_s M.
  specialize (Hf (a+b*e*c)). specialize (He d). fold e in He. fold f in Hf.
  clearbody a b c d e f. clear - He Hf L Hl. apply leq_cupx.
  
  (* TODO: optimize the line below *)
  rewrite one_blk_mx. apply blk_mx_leq; hlattice. 

  rewrite mx_dot_blk. apply blk_mx_leq. 
  rewrite <- Hf at 3. ra.
  rewrite <- Hf at 3. ra. 
  rewrite <- He at 2. ra. 
  rewrite <- He at 5 6. ra.
Qed.

(** [mx_str_build] preserves the left induction rule for star *)
Lemma mx_str_build_ind_l: transfers (fun n M sM => forall p (N: mx n p), M*N <== N -> sM*N <== N).
Proof.
  intros Hf He M p N. rewrite (to_blk_mx M) at 1. unfold_s M. 
  rewrite (to_col_mx N). set (h := tsub_mx N). set (k:= bsub_mx N).
  specialize (Hf (a+b*e*c) p h). specialize (He d p k). fold e in He. fold f in Hf.  
  clearbody a b c d e f h k. clear - He Hf L Hl. 
  rewrite 2blk_mx', 2mx_dot_rowcol, 4mx_dot_colx. setoid_rewrite <-col_mx_cup.
  setoid_rewrite col_mx_leq_iff. rewrite 2cup_spec. intros [[Ha Hb] [Hc Hd]].
  specialize (He Hd). revert Hf.
  rewrite 2dotplsx, 4cup_spec, <-!dotA. intro Hf. apply apply in Hf;
  repeat split; repeat (trivial; rewrite ?Ha, ?Hb, ?Hc, ?Hd, ?He, ?Hf).
Qed.

(** [mx_str_build] preserves the right induction rule for star *)
Lemma mx_str_build_ind_r: transfers (fun n M sM => forall p (N: mx p n), N*M <== N -> N*sM <== N).
Proof.
  intros Hf He M p N. rewrite (to_blk_mx M) at 1. unfold_s M. 
  rewrite (to_row_mx N). set (h := lsub_mx N). set (k:= rsub_mx N).
  specialize (Hf (a+b*e*c) p h). specialize (He d p k). fold e in He. fold f in Hf.  
  clearbody a b c d e f h k. clear - He Hf L Hl. unfold blk_mx.
  rewrite 2mx_dot_rowcol, 4mx_dot_xrow. setoid_rewrite <-row_mx_cup.
  setoid_rewrite row_mx_leq_iff. rewrite 2cup_spec. intros [[Ha Hb] [Hc Hd]].
  specialize (He Hd). revert Hf.
  rewrite 2dotxpls, 4cup_spec, !dotA. intro Hf. apply apply in Hf;
  repeat split; repeat (trivial; rewrite ?Ha, ?Hb, ?Hc, ?Hd, ?He, ?Hf).
Qed.

End build.

(** *** packing everything by induction to get properties of the
   Kleene star matrix construction *)

Lemma mx_str_unfold_l n (M: mx n n): 1 + M * mx_str _ _ _ M <== mx_str _ _ _ M.
Proof.
  induction n. intro i; elim (ord_0_empty i).
  simpl mx_str. apply (mx_str_build_unfold_l 1); trivial. 
  intros N i j. simpl. unfold mx_dot, scal_mx, mx_one.
  simpl. setoid_rewrite ord0_unique. simpl. now rewrite cupxb, <-str_unfold_l.
Qed.

Lemma mx_str_refl n (M: mx n n): 1 <== mx_str _ _ _ M.
Proof. rewrite <-mx_str_unfold_l. apply leq_xcup. now left. Qed.

Lemma mx_str_cons n (M: mx n n): M * mx_str _ _ _ M <== mx_str _ _ _ M.
Proof. rewrite <-mx_str_unfold_l at 2. apply leq_xcup. now right. Qed.

Lemma mx_str_ind_l n m (M: mx n n) (N: mx n m): M * N <== N -> mx_str _ _ _ M * N <== N.
Proof.
  revert m N. induction n. intros ? ? _ i; elim (ord_0_empty i).
  simpl mx_str. apply (mx_str_build_ind_l 1); trivial. clear M IHn.
  intros M p N H i j. simpl. unfold mx_dot, scal_mx. 
  simpl. setoid_rewrite ord0_unique. rewrite cupxb. 
  apply str_ind_l. rewrite <-(H ord0 j) at 2.
  apply weq_geq. apply cupxb.
Qed.

Lemma mx_str_ind_r n m (M: mx n n) (N: mx m n): N * M <== N -> N * mx_str _ _ _ M <== N.
Proof.
  revert m N. induction n. intros ? ? _ ? i; elim (ord_0_empty i).
  simpl mx_str. apply (mx_str_build_ind_r 1); trivial. clear M IHn.
  intros M p N H i j. simpl. unfold mx_dot, scal_mx. 
  simpl. setoid_rewrite ord0_unique. rewrite cupxb. 
  apply str_ind_r. rewrite <-(H i ord0) at 2.
  apply weq_geq. apply cupxb.
Qed.

End ka.



(** * Exported matrix construction

   Matrices on [X] form an [l]-monoid provided that 
   1/ [X] is an [l]-monoid, and
   2/ [l] is rich enough (i.e., it contains at least [BSL], 
      and [BDL] if [l] has residuals )
   
   We express the latter constraint using the following definition *)

Definition mx_level l := (if has_div l then BDL+l else BSL+l)%level.

Lemma mx_div_level l : DIV << l -> mx_level l << l -> BDL+DIV << l.
Proof.
  rewrite 3lower_spec. unfold mx_level. simpl. 
  case (has_div l). simpl. tauto. intuition discriminate. 
Qed.

Local Hint Extern 0 (_ << _) => solve_lower': typeclass_instances.

(* NOTE: the following instance could alternatively be stated as:
   Instance mx_laws {l h X} {L: laws l X} {Hl: mx_level h<<l} u: laws h (mx_ops X u).
   
   We don't do this because we want inferred laws instances to be
   closed (evar free) and "maximal", the inferred instance has the
   maximal possible level. *)

Instance mx_laws `{L: laws} `{Hl: mx_level l<<l} u: laws l (mx_ops X u) |1.
Proof.
  assert (Hl': BSL<<l). revert Hl. unfold mx_level. case has_div; intro; solve_lower.  
  constructor; repeat right. 
  intros. apply pw_laws.
  exact mx_dotA.
  exact mx_dot1x. 
  exact mx_dotx1. 
  exact mx_dot_leq.
  exact mx_dotplsx_.
  exact mx_dotxpls_.
  exact mx_dot0x_.
  exact mx_dotx0_.
  intro. apply mx_cnvdot_. 
  intro. apply mx_cnv_invol.
  intro. apply mx_cnv_leq.
  apply mx_cnv_ext.
  (* TODO: improve constraint resolution *)
  intro. apply (mx_str_refl (Hl:=lower_mergex _ _ _ Hl' H)).
  intro. apply (mx_str_cons (Hl:=lower_mergex _ _ _ Hl' H)). 
  intro. apply (mx_str_ind_l (Hl:=lower_mergex _ _ _ Hl' H)). 
  apply (mx_str_ind_r (Hl:=lower_mergex _ _ _ Hl' H)).
  reflexivity.
  intros Hl'' n m p M N O i j. simpl. unfold mx_dot, mx_cnv.
  apply (lower_mergex _ _ _ Hl'') in Hl'. clear Hl Hl''.
  rewrite capsupx. setoid_rewrite capxsup. setoid_rewrite dotxsum. 
  apply sup_leq; trivial. intro i'. rewrite <- (leq_xsup _ _ i) by apply in_seq. apply capdotx.
  intro Hl''. pose proof (mx_div_level _ Hl'' Hl). clear Hl Hl' Hl''. 
   intros. simpl. unfold mx_ldv, mx_dot. 
    setoid_rewrite sup_spec. setoid_rewrite inf_spec. setoid_rewrite ldv_spec. 
    clear. split; auto using in_seq. 
  intro Hl''. pose proof (mx_div_level _ Hl'' Hl). clear Hl Hl' Hl''. 
   intros. simpl. unfold mx_rdv, mx_dot. 
    setoid_rewrite sup_spec. setoid_rewrite inf_spec. setoid_rewrite rdv_spec. 
    clear. split; auto using in_seq. 
Qed.
