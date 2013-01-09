(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * kat_tac: decision tactics for KA, KAT, and KAT with Hoare hypotheses *)

Require Import boolean ugregex_dec kat_reification kat_untyping kat_completeness. 

(** * corollary of kat_untyping and kat_completeness:
    one can decide typed KAT by reasoning about untyped languages *)

Section j.
Notation Sigma := positive.
Variable Pred: nat.
Variables src tgt: Sigma -> positive.

Corollary kat_untype_weq n m (e f: gregex Pred src tgt n m): gerase e == gerase f <-> e == f. 
Proof.
  split.
   intro H. apply kat_complete_weq. 
   rewrite 2untype_glang.
   now apply traces.restrict_weq. 
  apply gerase_weq. 
Qed.

End j.

(** we can thus refine the reification lemma provided in [kat_reification] *)
Corollary kat_weq_dec `{L: laws} f' fs fp n m (e f: @kat_expr X f' fs n m): 
  e_level e + e_level f << BKA ->
  (let v := vars (e_pls e f) in 
    eqb_kat (gerase (to_gregex v n m e)) (gerase (to_gregex v n m f)) = Some true) -> 
  eval fp n m e == eval fp n m f.
Proof.
  intros Hl H. apply to_gregex_weq. assumption. 
  apply kat_untype_weq, eqb_kat_correct, H.
Qed.



(** * [kat] tactic, for Kleene algebra with tests *)

(** the [kat] tactic solves KAT (in)equalities; it proceeds as follows:

   0. possibly convert inequalities into equalities, using
      [leq_iff_cup];
   1. look for the kat structure and laws, by calling typeclass
      resolution using ([catch_kat_weq]);
   2. call the ML reification tactic
      -> the equivalence will be checked in OCaml, an a 
         counter-example will be displayed if it does not hold
      -> this will otherwise produce a sequence of let-in's for the
         various reification ingredients
   3. introduce those ingredients and apply the above reification lemma
   4. close the two generated subgoals by reflexivity (the first one
      corresponds to checking that reified terms did no include
      forbidden constructions - it should never fail unless there is a 
      bug in reification; the second one corresponds to the
      execution of the Coa KAT decision algorithm - it should never fail 
      since the equation was already checked in OCaml) *)

Lemma catch_kat_weq {X} {L: laws X} n m (x y: X n m): 
  (let L:=L in x == y) -> x == y.
Proof. trivial. Qed.

(** parametrised tactic to do the work share by [ka], [kat], and [hkat]
    [b] indicates whether we are in KAT (true) or KA (false) *)
Ltac pre_dec b :=
  let L := fresh "L" in intro L; (* L is the kat laws instance *)
  let tenv := fresh "tenv" in
  let env := fresh "env" in
  let penv := fresh "penv" in
  let lhs := fresh "lhs" in
  let rhs := fresh "rhs" in
  ra_kat_reify b; intros tenv env penv ? ? lhs rhs; 
  apply (@kat_weq_dec _ L tenv env penv _ _ lhs rhs); [
    (reflexivity || fail 1 "Bug in KAT reification, please report") |
    (close_by_reflection (Some true) || 
        fail 1 "Not a KAT theorem, but no counter-example can be displayed. Please report.") ].

(** [kat] tactic *)
Ltac kat := 
  intros; rewrite ?leq_iff_cup; 
    (apply catch_kat_weq || fail "could not find a KAT structure"); 
    pre_dec true.



(** * [ka] tactic, for Kleene algebra *)

(** we use the fact that any Kleene algebras with bottom faithfully
   embed into KAT, using trivial tests *)
(* TODO: sync with conservativity once we got it *)
Module bka_to_kat.
Definition ops (X: monoid.ops) := mk_ops X (fun _ => bool_lattice_ops) (fun _ => ofbool). 
Lemma laws `{monoid.laws} `{BKA<<l}: kat.laws (ops X).
Proof.
  constructor. 
  apply lower_laws. 
  intro. apply lower_lattice_laws. 
  intro. constructor; try discriminate. 
  apply ofbool_leq. 
  apply op_leq_weq_1.
  intros _ ? ?. apply orb_pls. 
  intros _. reflexivity. 
  intros ?. reflexivity. 
  intros ? ? ?. apply andb_dot. 
Qed.
End bka_to_kat.

(** the tactic is really similar to [kat], except that we catch the
   KAT laws using the lemma below, exploiting the above embedding *)
Lemma catch_ka_weq {X l} {L: monoid.laws l X} {Hl: BKA<<l} n m (x y: X n m): 
  (let L:=@bka_to_kat.laws l X L Hl in @weq (@kar (bka_to_kat.ops X) n m) x y) -> x == y.
Proof. trivial. Qed.

Ltac ka := 
  intros; rewrite ?leq_iff_cup; 
    (apply catch_ka_weq || fail "could not find a KA structure");
    pre_dec false.



(** * [hkat] tactic, for KAT with Hoare hypotheses *)

(** Hypotheses of the shape [x == 0], called "Hoare hypotheses", can
   be eliminated in KAT.

   In other words, the Horn theory of KAT restricted to the clauses
   wher all hypotheses have the above shape, reduces to the equational
   theory of KAT, and is thus decidable.

   Moreover, some other kinds of hypotheses can be transformed into
   Hoare ones, and hypotheses of the shape [[c];p == [c]] can also be
   eliminated.

   All in all, a non-trivial class of hypotheses can be handled in
   practice.

   We perform such an elimination of hypotheses to obtain the [hkat]
   tactic below.

   For more details, see Chris Hardin and Dexter Kozen. "On the
   elimination of hypotheses in Kleene algebra with tests".
   TR2002-1879, Computer Science Department, Cornell University, October 2002

 *)


(** converting various kinds of hypotheses to Hoare ones *)
Lemma ab_to_hoare `{L: laws} {n} (b c: tst n): b == c -> [b\cap !c \cup !b\cap c] <== 0.
Proof. intro H. rewrite H. kat. Qed.

Lemma ab'_to_hoare `{L: laws} {n} (b c: tst n): b <== c -> [b\cap !c] <== 0.
Proof. intro H. rewrite H. kat. Qed.

(* note: les quatre implications suivantes ne sont complètes que pour p=q *)
Lemma bpqc_to_hoare `{L: laws} {n m} (b: tst n) (c: tst m) p q: 
  [b]*p <== q*[c] -> [b]*p*[!c] <== 0.
Proof. intro H. rewrite H. kat. Qed.

Lemma pbcq_to_hoare `{L: laws} {n m} (b: tst n) (c: tst m) p q: 
  p*[b] <== [c]*q -> [!c]*p*[b] <== 0.
Proof. rewrite <-dotA. dual @bpqc_to_hoare. Qed.

Lemma qpc_to_hoare `{L: laws} {n m} (c: tst m) (p q: X n m): 
  q <== p*[c] -> q*[!c] <== 0.
Proof. intro H. rewrite H. kat. Qed.

Lemma qcp_to_hoare `{L: laws} {n m} (c: tst m) (p q: X m n):
  q <== [c]*p -> [!c]*q <== 0.
Proof. dual @qpc_to_hoare. Qed.

(* TOTHINK: comprendre modulo A, et peut-être revenir aux cas complets
   (note: les deux dernières sont équivalentes aux deux premières, 
          mais pas prises dans le cas complet) *)

Lemma cp_c `{L: laws} {n} (c: tst n) (p: X n n): 
  [c]*p == [c] -> p == [!c]*p+[c].
Proof. intro H. rewrite <-H. kat. Qed.

Lemma pc_c `{L: laws} {n} (c: tst n) (p: X n n): 
  p*[c] == [c] -> p == p*[!c]+[c].
Proof. dual @cp_c. Qed.


(** merging Hoare hypotheses *)
Lemma join_leq `{lattice.laws} `{CUP<<l} (x y z: X):  x<==z -> y<==z -> x\cup y<==z. 
Proof. rewrite cup_spec. tauto. Qed.

(** eliminating Hoare hypotheses ; [u] and [v] are intended to be the
   universal expressions of the appropriate type *)
Lemma elim_hoare_hypotheses_weq `{L: laws} {n m p q} (u: X n p) (v: X q m) (z: X p q) (x y: X n m):
  z <== 0 -> x+u*z*v == y+u*z*v -> x==y.
Proof. rewrite leq_xb_iff. intro Hz. now rewrite Hz, dotx0, dot0x, 2cupxb. Qed.

Lemma elim_hoare_hypotheses_leq `{L: laws} {n m p q} (u: X n p) (v: X q m) (z: X p q) (x y: X n m):
  z <== 0 -> x <== y+u*z*v -> x<==y.
Proof. intro Hz. now rewrite Hz, dotx0, dot0x, cupxb. Qed.

(** tactic used to aggregate Hoare hypotheses: convert hypotheses into
   Hoare ones using the above lemas, then merge them into a single one *)
Ltac aggregate_hoare_hypotheses :=
  repeat 
    match goal with
      | H: _ == _ |- _ => 
        apply ab_to_hoare in H || 
        (rewrite (cp_c _ _ H); clear H) || 
        (rewrite (pc_c _ _ H); clear H) || 
        apply weq_spec in H as [? ?]
    end;
  repeat
    match goal with
      | H: _ <== _ |- _ => 
        apply ab'_to_hoare in H || 
        apply bpqc_to_hoare in H || 
        apply pbcq_to_hoare in H || 
        apply qcp_to_hoare in H ||
        apply qpc_to_hoare in H
      | H: _ <== 0,  H': _ <== 0 |- _ => 
        apply (join_leq _ _ _ H') in H; clear H'
    end.

(** final [hkat] tactic: aggregate Hoare hypotheses, possibly
   transform inequalities into equalities, get the alphabet to
   construct the universal expression, eliminate Hoare hypotheses
   using the above lemma, and finally call the [kat] tactic *)
Ltac hkat :=
  intros; aggregate_hoare_hypotheses; rewrite ?leq_iff_cup; 
  (apply catch_kat_weq || fail "could not find a KAT structure"); 
  let L := fresh "L" in intro L;
  let u := fresh "u" in 
  ((ra_get_kat_alphabet; intro u; 
    eapply (elim_hoare_hypotheses_weq (u^*) (u^*)); [eassumption|])
  || fail "typed hkat is not supported yet"); 
  subst u; revert L; pre_dec true.
