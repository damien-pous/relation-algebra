(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * matrix_ext: additional properties of matrices *)

Require Import kleene normalisation ordinal sups.
Require Export matrix.
Set Implicit Arguments.


(** * [mx_scal] is an homomorphism  *)

Instance mx_scal_leq `{lattice.laws}: Proper (leq ==> leq) (@mx_scal X).
Proof. intros ? ? H'. apply H'. Qed.
Instance mx_scal_weq `{lattice.laws}: Proper (weq ==> weq) (@mx_scal X) := op_leq_weq_1.

Lemma mx_scal_zer `{lattice.laws}: mx_scal bot == bot.
Proof. reflexivity.  Qed.

Lemma mx_scal_one `{laws} n: mx_scal 1 == one n.
Proof. reflexivity.  Qed.

Lemma mx_scal_pls `{lattice.laws} (M N: mx X 1 1): 
  mx_scal (M \cup N) == mx_scal M \cup mx_scal N.
Proof. reflexivity.  Qed.

Lemma mx_scal_dot `{laws} `{BOT+CUP<<l} u (M N: mx (X u u) 1 1): 
  mx_scal (M * N) == mx_scal M * mx_scal N.
Proof. apply cupxb. Qed.

Lemma mx_scal_str `{laws} `{BKA<<l} u (M: mx (X u u) 1 1): 
  mx_scal (M^*) == mx_scal M ^*.
Proof. 
  apply str_weq. unfold mx_scal, sub00_mx, tsub_mx, lsub_mx. simpl. 
  setoid_rewrite ord0_unique. apply cupxb. 
Qed.

(** * [scal_mx] preserves inclusions/equalities  *)

Instance scal_mx_leq `{lattice.laws}: Proper (leq ==> leq) (@scal_mx X).
Proof. now repeat intro. Qed.
Instance scal_mx_weq `{lattice.laws}: Proper (weq ==> weq) (@scal_mx X) := op_leq_weq_1.

(** * extracting components of block matrices *)

Lemma mx_tsub_col `{lattice.laws} n1 n2 m M1 M2:
  tsub_mx (@col_mx X n1 n2 m M1 M2) == M1.
Proof. intros i j. unfold tsub_mx, col_mx. now rewrite split_lshift. Qed.
Lemma mx_bsub_col `{lattice.laws} n1 n2 m M1 M2:
  bsub_mx (@col_mx X n1 n2 m M1 M2) == M2.
Proof. intros i j. unfold bsub_mx, col_mx. now rewrite split_rshift. Qed.
Lemma mx_lsub_row `{lattice.laws} n m1 m2 M1 M2:
  lsub_mx (@row_mx X n m1 m2 M1 M2) == M1.
Proof. intros i j. unfold lsub_mx, row_mx. now rewrite split_lshift. Qed.
Lemma mx_rsub_row `{lattice.laws} n m1 m2 M1 M2:
  rsub_mx (@row_mx X n m1 m2 M1 M2) == M2.
Proof. intros i j. unfold rsub_mx, row_mx. now rewrite split_rshift. Qed.

Lemma mx_sub00_blk `{lattice.laws} n1 n2 m1 m2 a b c d:
  sub00_mx (@blk_mx X n1 n2 m1 m2 a b c d) == a.
Proof. setoid_rewrite mx_tsub_col. apply mx_lsub_row. Qed. 
Lemma mx_sub01_blk `{lattice.laws} n1 n2 m1 m2 a b c d:
  sub01_mx (@blk_mx X n1 n2 m1 m2 a b c d) == b.
Proof. setoid_rewrite mx_tsub_col. apply mx_rsub_row. Qed. 
Lemma mx_sub10_blk `{lattice.laws} n1 n2 m1 m2 a b c d:
  sub10_mx (@blk_mx X n1 n2 m1 m2 a b c d) == c.
Proof. setoid_rewrite mx_bsub_col. apply mx_lsub_row. Qed. 
Lemma mx_sub11_blk `{lattice.laws} n1 n2 m1 m2 a b c d:
  sub11_mx (@blk_mx X n1 n2 m1 m2 a b c d) == d.
Proof. setoid_rewrite mx_bsub_col. apply mx_rsub_row. Qed. 


(** sub-matrices of the empty matrix are empty *)
Lemma blk_mx_0 `{laws} u n1 n2 m1 m2 a b c d: @blk_mx (X u u) n1 n2 m1 m2 a b c d == 0 -> 
  a==0 /\ b==0 /\ c==0 /\ d==0.
Proof. 
  intro Z. split; [|split; [|split]]. 
  rewrite <-(mx_sub00_blk a b c d). intros ? ?. apply Z.
  rewrite <-(mx_sub01_blk a b c d). intros ? ?. apply Z.
  rewrite <-(mx_sub10_blk a b c d). intros ? ?. apply Z.
  rewrite <-(mx_sub11_blk a b c d). intros ? ?. apply Z.
Qed.


(** * Kleene star of a block matrix *)
Section h.
Context `{L:laws} `{Hl:BKA<<l} (u: ob X).

Local Instance mx_bka_laws: laws BKA (mx_ops X u) := mx_laws (L:=lower_laws) _.

Lemma mx_str_blk' n m (M: mx (X u u) (n+m) (n+m)): 
  M^* == mx_str_build X u n m (mx_str _ _ _) (mx_str _ _ _) M.
Proof. 
  apply str_unique'. 
   apply mx_str_build_unfold_l; apply mx_str_unfold_l. 
   apply mx_str_build_ind_l; intros ? ? ?; apply mx_str_ind_l. 
Qed.

(** general result *)
Lemma mx_str_blk n1 n2 
  (a: mx (X u u) n1 n1) (b: mx (X u u) n1 n2) 
  (c: mx (X u u) n2 n1) (d: mx (X u u) n2 n2):
  let e := d^* in
  let f := (a+(b*e)*c)^* in
  blk_mx a b c d ^* == blk_mx f (f*(b*e)) ((e*c)*f) (e+(e*c*f)*(b*e)).
Proof.
  intros e f. rewrite mx_str_blk'. unfold mx_str_build.
  ra_fold (mx_ops X). now rewrite mx_sub00_blk, mx_sub01_blk, mx_sub10_blk, mx_sub11_blk.
Qed.

(** specialisation to trigonal block matrices *)
Lemma mx_str_trigonal n1 n2 
  (a: mx (X u u) n1 n1) (b: mx (X u u) n1 n2) 
                        (d: mx (X u u) n2 n2):
  blk_mx a b 0 d ^* == blk_mx (a^*) (a^**(b*d^*)) 0 (d^*).
Proof. rewrite mx_str_blk. apply blk_mx_weq; ra. Qed.

(** and to diagonal block matrices *)
Lemma mx_str_diagonal n1 n2 
  (a: mx (X u u) n1 n1) (d: mx (X u u) n2 n2):
  blk_mx a 0 0 d ^* == blk_mx (a^*) 0 0 (d^*).
Proof. rewrite mx_str_trigonal. apply blk_mx_weq; trivial; ra. Qed.


Lemma mx_str_1 (M: mx (X u u) 1 1): M^* == scal_mx (mx_scal M ^*).
Proof.
  intros i j. setoid_rewrite ord0_unique. simpl.  
  unfold mx_str_build, blk_mx, col_mx, row_mx, ordinal.split; simpl. 
  unfold mx_scal, scal_mx, mx_dot, sub00_mx, tsub_mx, lsub_mx; simpl. 
  setoid_rewrite ord0_unique. ra. 
Qed.

(** * induction schemes for proving properties of the Kleene star of a matrix *)
(** (used to show that epsilon and derivatives commute with matrix star in [rmx]) *)

Lemma mx_str_ind (P: forall n, mx (X u u) n n -> mx (X u u) n n -> Prop): 
  (forall n, Proper (weq ==> weq ==> iff) (P n)) ->
  (forall M, P O M M) -> 
  (forall M, P _ M (scal_mx (mx_scal M ^*))) -> 
  (forall n m,
    (forall M, P n M (M^*)) -> 
    (forall M, P m M (M^*)) -> 
     forall M, P _ M (mx_str_build _ _ n m (fun M => M^*) (fun M => M^*) M)) ->
  forall n M, P n M (M^*). 
Proof.
  intros HP HO H1 Hplus n M. induction n as [|n IHn].  
   apply HO.
   change (M^*) with (mx_str _ _ _ M). unfold mx_str, mx_str_build. ra_fold (mx_ops X). 
   setoid_rewrite <-mx_str_1.
   revert M; refine (Hplus (S O) n _ _); intro M. 
   rewrite mx_str_1. apply H1. 
   apply IHn. 
Qed.

Lemma mx_str_ind' (P: forall n, mx (X u u) n n -> mx (X u u) n n -> Prop): 
  (forall n, Proper (weq ==> weq ==> iff) (P n)) ->
  (forall M, P O M M) -> 
  (forall M, P _ M (scal_mx (mx_scal M ^*))) -> 
  (forall n m a b c d,
    let e := d^* in
    let be := b*e in
    let ec := e*c in
    let f := (a+be*c)^* in
    let fbe := f*be in
    let ecf := ec*f in
    P m d e -> 
    P n (a+be*c) f -> 
    P _ (blk_mx a b c d) (blk_mx f fbe ecf (e+ecf*be))) ->
  forall n M, P n M (M^*). 
Proof.
  intros HP HO H1 Hplus. apply (mx_str_ind P HP HO H1). 
  intros n m Hn Hm M. rewrite (to_blk_mx M) at 1. now apply Hplus. 
Qed. 

End h.


(** * pointwise extension of a funcion to matrices *)

Definition mx_map X Y (f: X -> Y) n m (M: mx X n m): mx Y n m := fun i j => f (M i j).

Instance mx_map_leq {X Y: lattice.ops} {f: X -> Y}
  {Hf: Proper (leq ==> leq) f} n m: Proper (leq ==> leq) (@mx_map _ _ f n m).
Proof. intros M N H i j. apply Hf, H. Qed.

Instance mx_map_weq {X Y: lattice.ops} {f: X -> Y}
  {Hf: Proper (weq ==> weq) f} n m: Proper (weq ==> weq) (@mx_map _ _ f n m).
Proof. intros M N H i j. apply Hf, H. Qed.

Lemma mx_map_blk {X Y l} {HY: lattice.laws l Y} (f: X -> Y) n1 n2 m1 m2 a b c d:
  mx_map f (@blk_mx _ n1 n2 m1 m2 a b c d) == 
  blk_mx (mx_map f a) (mx_map f b) (mx_map f c) (mx_map f d).
Proof. 
  intros i j. unfold mx_map, blk_mx, col_mx, row_mx. 
  case split; case split; reflexivity. 
Qed.

Lemma mx_map_scal {X Y} (f: X -> Y) x: mx_map f (scal_mx x) = scal_mx (f x). 
Proof. reflexivity. Qed.

Lemma scal_mx_map {X} {Y: lattice.ops} (f: X -> Y) M: f (mx_scal M) = mx_scal (mx_map f M). 
Proof. reflexivity. Qed.

(** * `functional' matrices, with exactly one [z] per line, and [0] everywhere else *)

Definition mx_fun {X: lattice.ops} n m f z: mx X n m := 
  fun x y => if eqb_ord y (f x) then z else bot. 

Lemma mx_dot_fun `{laws} `{BSL<<l} u n m f z p (M: mx (X u u) m p) i j: 
  (mx_fun (n:=n) f z * M) i j == z * M (f i) j.
Proof.
  simpl. unfold mx_dot. apply antisym. 
  apply leq_supx. intros j' _. unfold mx_fun. case eqb_ord_spec.
   intros ->. ra.
   intros _. ra. 
  rewrite <- (leq_xsup _ _ (f i)). 2: apply in_seq.
  unfold mx_fun. now rewrite eqb_refl.
Qed.

Lemma mx_dot_kfun1 `{laws} `{BSL<<l} u n m i p (M: mx (X u u) m p): 
  (mx_fun (n:=n) (fun _ => i) 1 * M) == fun _ j => M i j.
Proof. intros j k. rewrite mx_dot_fun. apply dot1x. Qed.

Lemma mx_map_fun {X Y: lattice.ops} {l} {HY: lattice.laws l Y} n m f z g: 
  g bot == bot -> mx_map g (@mx_fun X n m f z) == @mx_fun Y n m f (g z).
Proof. intros Hg i j. unfold mx_map, mx_fun. now case eqb_ord. Qed.

