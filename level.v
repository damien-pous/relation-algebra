(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * level: tuples of Booleans identifying a point in the algebraic hierarchy  *)

Require Import common.

(** a level specifies which relation algebra operations are considered

   the interpretation in the model of binary relations is given on the
   right-hand side. *)
Record level := mk_level {
  has_cup: bool;                (** set theoretic union *)
  has_bot: bool;                (** empty relation *)
  has_cap: bool;                (** set theoretic intersection *)
  has_top: bool;                (** full relation *)
  has_str: bool;                (** reflexive transitive closure *)
  has_cnv: bool;                (** converse, or transpose *)
  has_neg: bool;                (** Boolean negation *)
  has_div: bool                 (** residuals, or factors *)
}.
Bind Scope level_scope with level.
Delimit Scope level_scope with level.

(** dual level, for symmetry arguments related to lattices *)
Definition dual l := mk_level
  (has_cap l)
  (has_top l)
  (has_cup l)
  (has_bot l)
  (has_str l)
  (has_cnv l)
  (has_neg l)
  (has_div l).

(** * Level constraints *)

(** [lower k k'], or [k << k'], denotes the fact that there are less 
   operations/axioms at level [k] than at level [k'] *)
Class lower (k k': level) := mk_lower:
  let 'mk_level a  b  c  d  e  f  g  h  := k in
  let 'mk_level a' b' c' d' e' f' g' h' := k' in
  is_true (a<<<a'&&& b<<<b' &&& c<<<c' &&& d<<<d' 
           &&& e<<<e' &&& f<<<f' &&& g<<<g' &&& h <<< h').
Infix "<<" := lower (at level 79): ra_scope.
Arguments lower _ _: simpl never.

Local Open Scope ra_scope.

(** alternative specifiaction of [h << k] *)
Lemma lower_spec h k: h<<k <->
  (has_cup h -> has_cup k) /\
  (has_bot h -> has_bot k) /\
  (has_cap h -> has_cap k) /\
  (has_top h -> has_top k) /\
  (has_str h -> has_str k) /\
  (has_cnv h -> has_cnv k) /\
  (has_neg h -> has_neg k) /\
  (has_div h -> has_div k).
Proof.
  destruct h; destruct k. unfold lower.
  rewrite !landb_spec, !le_bool_spec. reflexivity. 
Qed.  

(** [<<] is a preorder *)
Instance lower_refl: Reflexive lower.
Proof. intro. setoid_rewrite lower_spec. tauto. Qed.  

Instance lower_trans: Transitive lower.
Proof. intros h k l. setoid_rewrite lower_spec. tauto. Qed.

(** * Merging levels *)

(** merging two levels: taking the union of their supported operations *)
Definition merge h k := mk_level
  (has_cup h ||| has_cup k)
  (has_bot h ||| has_bot k)
  (has_cap h ||| has_cap k)
  (has_top h ||| has_top k)
  (has_str h ||| has_str k)
  (has_cnv h ||| has_cnv k)
  (has_neg h ||| has_neg k)
  (has_div h ||| has_div k).
Infix "+" := merge: level_scope.
Arguments merge _ _: simpl never.

(** [merge] is a supremum for the [<<] preorder *)
Lemma merge_spec h k l: h+k<<l <-> h<<l /\ k<<l.
Proof. setoid_rewrite lower_spec. setoid_rewrite lorb_spec. tauto. Qed.

Lemma lower_xmerge h k l: l<<h \/ l<<k -> l << (h + k).
Proof. 
  assert (C:= merge_spec h k (h+k)). 
  intros [E|E]; (eapply lower_trans; [eassumption|]); apply C, lower_refl.
Qed.

Lemma lower_mergex h k l: h<<l -> k<<l -> h+k << l.
Proof. rewrite merge_spec. tauto. Qed.

Instance merge_lower: Proper (lower ==> lower ==> lower) merge.
Proof. intros h k H h' k' H'. apply lower_mergex; apply lower_xmerge; auto. Qed.

(** * Tactics for level constraints resolution *)

(** simple but efficient tactic, this is the one used by default, we
   give it as a hint for maximally inserted arguments (typeclasses
   resolution) *)
Ltac solve_lower := solve 
  [ exact eq_refl               (* trivial constraint (on closed levels) *)
  | eassumption                 (* context assumption *)
  | repeat 
    match goal with
      | H: ?h << ?l , H': ?k << ?l |- _ << ?l => 
        (* merge assumptions about [l] *)
        apply (lower_mergex h k l H) in H'; clear H
      | H: ?k << ?l |- ?h << _ => 
        (* use assumptions by transitivity *)
        apply (lower_trans h k l eq_refl H)
    end ] || fail "could not prove this entailment".
Hint Extern 0 (_ << _) => solve_lower: typeclass_instances.

(** heavier and more complete tactic, which we use in a selfdom way *)
Ltac solve_lower' := solve [
  (repeat
    match goal with 
      H: _ + _ << _ |- _ => apply merge_spec in H as [? ?]
    end); 
  (repeat apply lower_mergex); 
  auto 100 using lower_xmerge, lower_refl ] || fail "could not prove this entailment".

(** tactic used to discriminate unsatisfiable level constraint *)
Ltac discriminate_levels := solve [
  intros; repeat discriminate || 
    match goal with
      | H: _ + _ << _ |- _ => apply merge_spec in H as [? ?]
    end ].

(** * Concrete levels *)
Section levels.
Notation "1" := true.
Notation "0" := false.
(** atoms *)
Definition MIN := mk_level 0 0 0 0 0 0 0 0.
Definition CUP := mk_level 1 0 0 0 0 0 0 0.
Definition BOT := mk_level 0 1 0 0 0 0 0 0.
Definition CAP := mk_level 0 0 1 0 0 0 0 0.
Definition TOP := mk_level 0 0 0 1 0 0 0 0.
Definition STR := mk_level 0 0 0 0 1 0 0 0.
Definition CNV := mk_level 0 0 0 0 0 1 0 0.
Definition NEG := mk_level 0 0 0 0 0 0 1 0.
Definition DIV := mk_level 0 0 0 0 0 0 0 1.
Local Open Scope level_scope.
(** points of particular interest (i.e., corresponding to standard
    mathematical structures) *)
Definition SL  := CUP.
Definition DL  := Eval compute in CUP+CAP.
Definition BSL := Eval compute in SL+BOT.
Definition BDL := Eval compute in DL+BOT+TOP.
Definition BL  := Eval compute in BDL+NEG.
Definition KA  := Eval compute in SL+STR.
Definition AA  := Eval compute in DL+STR.
Definition AL  := Eval compute in CAP+CNV.
Definition DAL := Eval compute in DL+CNV.
Definition BKA := Eval compute in KA+BOT.
Definition CKA := Eval compute in KA+CNV.
End levels.

(* sanity checks for the [solve_lower] tactic *)
(*
Goal forall l, CUP<<l -> AL<<l -> CNV+CUP<<l.
intros. solve_lower || fail "bad". Abort.
Goal forall l, KA<<l -> AL<<l -> CNV+CUP<<l.
intros. solve_lower || fail "bad". Abort.
Goal forall l, CAP<<l -> AL<<l -> CNV+CUP<<l.
intros. Fail solve_lower. Abort.
*)
