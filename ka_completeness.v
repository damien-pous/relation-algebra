(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * ka_completeness: completeness of Kleene algebra *)
(** We mostly follow Dexter Kozen's proof:
   A completeness theorem for Kleene algebras and the algebra of regular events. 
   Information and Computation, 110(2):366-390, May 1994.

   We proceed as follows:

   1. convert regular expressions into matricial NFA with epsilon
      transitions, using a simple and compositional 
      construction (Thompson).

   2. remove epsilon transitions (algebraically, using Kleene star on
      matrices to compute their reflexive transitive closure)

   3. determinise matricial NFA using the powerset construction
      (without performing the "accessible" subsets optimisation, for
      the sake of simplicity)

   4. exploit decidability of DFA language inclusion to conclude (this
      is where our proof slightly differs from that of Kozen: he first
      minimises the DFA, and then compare them up to isomorphism)

   Again, the implicit underlying algorithm is not efficient ; we
   don't care since this is not the one we execute in the end.  *)

Require Import kleene sums matrix_ext lset boolean lang nfa regex bmx rmx normalisation.
Require dfa.
Set Implicit Arguments.
Unset Printing Implicit Defensive.

(** locally prevent [simpl] from unfolding relation algebra projections *)
Local Arguments lattice.car {_}: simpl never.
Local Arguments lattice.weq {_} _ _: simpl never.
Local Arguments lattice.leq {_} _ _: simpl never.
Local Arguments lattice.cup {_} _ _: simpl never.
Local Arguments lattice.bot {_}: simpl never.
Local Arguments monoid.mor {_} _ _: simpl never.
Local Arguments monoid.one {_} _: simpl never.
Local Arguments monoid.dot {_} _ _ _ _ _: simpl never.
Local Arguments monoid.str {_} _ _: simpl never.

(** * 1. constructing eNFA out of regular expressions (Thompson) *)

(** Thompson construction is straightfoward once we have block matrix operations *)

(** ** construction *)

Module Thompson.

(** empty automaton for [0] *)
Definition zer := @mk 0 0 0 0.
(** one state automaton for [1] *)
Definition one := @mk 1 1 0 1.
(** two states automata for variables *)
Definition cst e := @mk (1+1) 
  (row_mx 1 0) 
  (blk_mx 1 (scal_mx e) 0 1) 
  (col_mx 0 1).
(** for [pls], we take the disjoint union of the two automata *)
Definition pls e f := mk 
  (row_mx e^u f^u) 
  (blk_mx e^M 0 0 f^M) 
  (col_mx e^v f^v).
(** for [dot], we take the disjoint union, and we add epsilon
   transitions from accepting states of the first automaton to starting
   states of the second one *)
Definition dot e f := mk 
  (row_mx e^u 0) 
  (blk_mx e^M (e^v*f^u) 0 f^M) 
  (col_mx 0 f^v).
(** strict iteration is obtained simply by adding epsilon transitions
   from accepting states to initial ones *)
Definition itr e := mk e^u (e^M+e^v*e^u) e^v.
(** Kleene star is derived from the other operations *)
Definition str e := pls one (itr e).

(** summing up all together, we get the final construction *)
Fixpoint enfa (e: regex'): t :=
  match e with
    | r_zer => zer
    | r_one => one
    | r_var _ => cst e
    | r_pls e f => pls (enfa e) (enfa f)
    | r_dot e f => dot (enfa e) (enfa f)
    | r_str e => str (enfa e)
  end.

(** ** correctness *)

(** algebraic correcteness of each construction *)

Lemma eval_zer: eval zer == 0.
Proof. reflexivity. Qed.

Lemma eval_cst e: eval (cst e) == e.
Proof. 
  set (o:=eval (cst e)). vm_compute in o; subst o. ra_normalise. 
  rewrite str1. ra.
Qed.

Lemma eval_one: eval one == 1.
Proof. set (o:=eval one). vm_compute in o; subst o. ra. Qed.

Lemma eval_pls e f: eval (pls e f) == eval e + eval f.
Proof.
  destruct e as [n u M v]. destruct f as [m s N t]. simpl. 
  rewrite <-mx_scal_pls. apply mx_scal_weq.
  rewrite mx_str_diagonal.
  setoid_rewrite mx_dot_rowcol. rewrite dotplsx. 
  rewrite <-2dotA, 2mx_dot_rowcol. ra.
Qed.

Lemma eval_dot e f: eval (dot e f) == eval e * eval f.
Proof.
  destruct e as [n u M v]. destruct f as [m s N t]. simpl. 
  rewrite <-mx_scal_dot. apply mx_scal_weq.
  rewrite mx_str_trigonal. setoid_rewrite mx_dot_rowcol. rewrite dotplsx. 
  rewrite <-dotA, mx_dot_rowcol. ra. 
Qed.

Lemma eval_itr e: eval (itr e) == eval e ^+.
Proof.
  rewrite itr_str_l. destruct e as [n u M v]. simpl.
  rewrite <-mx_scal_str, <-mx_scal_dot. apply mx_scal_weq. 
  rewrite str_pls. rewrite <-3dotA, <-str_dot. ra. 
Qed.

Lemma eval_str e: eval (str e) == eval e ^*.
Proof. unfold str. now rewrite eval_pls, eval_one, eval_itr, str_itr. Qed.

(** algebraic correcteness of the global construction *)

Theorem correct e: eval (enfa e) == e.
Proof.
  induction e; simpl enfa.
   apply eval_zer.
   apply eval_one.
   rewrite eval_pls. now apply cup_weq.
   rewrite eval_dot. now apply dot_weq.
   rewrite eval_str. now apply str_weq.
   apply eval_cst.
Qed.

(** the produced matricial automaton actually is an NFA with epsilon
   transitions (i.e., the transition matrix is simple, and starting and
   accepting vectors are 01) *)

Lemma is_enfa e: is_enfa (enfa e).
Proof. 
  Opaque Peano.plus.
  unfold is_enfa. induction e; simpl; intuition auto with mx_predicates. 
  Transparent Peano.plus.
Qed.

End Thompson.


(** * 2. removing espilon-transitions *)

(** again, this is straightfoward once we have the Kleene algebra of matrices *)

(** ** construction *)

Definition nfa e := 
  let e := Thompson.enfa e in
  let J := epsilon_mx e^M ^* in
  mk e^u (J * pure_part_mx e^M) (J * e^v).

(** ** correctness *)

Theorem eval_nfa e: eval (nfa e) == e.
Proof.
  rewrite <- (Thompson.correct e) at 2. unfold nfa. simpl. 
  set (f := Thompson.enfa e). set (J := epsilon_mx f^M). apply mx_scal_weq.
  rewrite (@expand_simple_mx _ _ f^M) at 2 by apply Thompson.is_enfa.
  rewrite str_pls. rewrite <-dotA, (dotA _ (J^*)). rewrite <-str_dot. apply dotA. 
Qed.

(** the produced matricial automaton is actually a NFA (i.e., the
   transition matrix is pure, and starting and accepting vectors are 01) *)

Lemma is_nfa_nfa e: is_nfa (nfa e).
Proof.
  generalize (Thompson.is_enfa e).
  unfold nfa, is_nfa, is_enfa. simpl. 
  intuition auto with mx_predicates.
Qed.


(** * 3. determinisation *)

(** we use the standard powerset construction, and we exploit the
   bijection we defined in [ordinals] between the powerset on [ord n]
   ([ord n -> bool]) and [ord (pow2 n)]. This allows us to index
   states of the determinised automaton in a seemless way. *)

Section det.

(** ** construction *)

(** we slightly generalise the construction, by specifying a finite
   subset of letters which have to be considered whether or not the
   NFA mention them. This allows us in the sequel to handle easily the
   case where the compared automata have different alphabets. *)

(** list of letters to include *)
Variable vars': list sigma.

(** NFA to determinise  *)
Variable nfa: nfa.t.
Hypothesis Hnfa: is_nfa nfa.

Notation n := (n nfa). 
Notation u := nfa^u. 
Notation M := nfa^M.
Notation v := nfa^v.

(** alphabet of the generated DFA: those appearing in [M], plus the
   imposed ones *)
Notation vars := (mx_vars M \cup vars').

(** (unlabelled) transition matrix of the NFA, restricted to [a] *)
Let T_ a := epsilon_mx (deriv_mx a M).
(** transition matrix of the NFA restricted to [a] *)
Let M_ a: rmx _ _ := fun i j => var a * T_(a) i j.
(** decoding matrix, establishing the link between the state of the
   determinised automaton (i.e., sets of states), with those of the starting one.
   We exploit for this the aforementioned bijection ;
   [X_(x,i)] holds iff [i\in x]. *)
Let X: rmx (pow2 n) n := fun x i => ofbool (set.mem x i).

(** determinised automaton:
   - the initial state is the set of intial states
   - the transition function is obtained by reading the transition
     matrix in a "parallel" way:
     along [a], the set [x] maps to the set [{j / i -a-> j for some i\in x}].
     this computation is performed matricially.
   - the accepting states are those containing at least one accepting state
     again, this computation is done matricially, using the decoding matrix [X].
  *)
Definition det := dfa.mk
  (of_row u)
  (fun x a => of_row (to_row x * T_(a)))
  (fun j => epsilon ((X * v) j ord0))
  vars.


(** ** correctness *)

(** the correctness is establish by using the bisimulation rule, to
   let the decoding matrix [X] go through [u * M^* * v]:
   denoting by [(u',M',v')] the determinised automaton, 
   we easily deduce [u*M^**v == u'*M'^**v']
   from [u==u'*X], [X*M == M'*X], and [X*v == v']. *)

Lemma det_uX: u == det^u * X.
Proof.
  intros i j. simpl. rewrite mx_dot_fun, dot1x. 
  symmetry. apply mem_of_row, Hnfa. 
Qed.

Lemma M_sum: M == \sum_(a\in vars) M_(a). 
Proof.
  intros i j. simpl. rewrite (@expand' (M i j) (mx_vars M ++vars')).
    2: apply leq_xcup; left; apply mx_vars_full.
  rewrite epsilon_pure by apply Hnfa. 
  setoid_rewrite cupbx. setoid_rewrite mx_sup.
  apply sup_weq. 2: reflexivity. 
  intro a. now rewrite <-epsilon_deriv_pure by apply Hnfa.
Qed.

Lemma det_MX: X * M^* == det^M^* * X.
Proof.
  apply str_move.
  rewrite M_sum. simpl. rewrite dotxsum, dotsumx. apply sup_weq. 2: reflexivity. 
  intros a x j. 
  rewrite mx_dot_fun. unfold X. 
  rewrite (mem_of_row ord0) by (unfold T_; auto with mx_predicates). 
  unfold weq. simpl. 
  setoid_rewrite dotxsum. apply sup_weq. 2: reflexivity. 
  intro j'. unfold M_, T_, epsilon_mx, mx_map.
  now rewrite 2dotA, dot_ofboolx.
Qed.

Lemma det_Xv: X*v == det^v.
Proof. 
  intros x j. simpl. setoid_rewrite ord0_unique. apply expand_01.
  apply is_01_mx_dot. intros ? ?. apply is_01_ofbool. apply Hnfa.
Qed.

(** algebraic correctness of determinisation *)
Theorem eval_det: eval det == eval nfa.
Proof.
  apply mx_scal_weq. 
  rewrite det_uX. 
  rewrite <-(dotA _ X), det_MX. 
  rewrite <-(dotA _ _ v), <-(dotA _ X), det_Xv.
  now rewrite dotA.
Qed.

End det.

(** * Kleene theorem as a corollary *)

(** summing up the above three constructions, we can build DFA out of
   a regular expression *)

Definition dfa vars e := det vars (nfa e).

Corollary eval_dfa vars e: nfa.eval (dfa vars e) == e.
Proof. setoid_rewrite eval_det. apply eval_nfa. apply is_nfa_nfa. Qed.

(** since the Kleene algebra of matrices allows us to compute a
   regular expression out of any finite automaton, we obtain Kleene
   theorem as a consequence:

  ``the languages recognised by a regular expression are those
  recognised by a (deterministic) finite automaton''.  *)

Theorem Kleene: forall l: lang' sigma, 
  (exists e: regex, l == regex.lang e) <-> (exists A: dfa.t, l == dfa.lang A (dfa.u A)).
Proof.
  intro l. setoid_rewrite <-nfa.dfa.eval_lang. setoid_rewrite <-dfa.reroot_id. 
  split. 
   intros [e He]. exists (dfa [] e). rewrite eval_dfa. assumption.
   intros [A HA]. exists (nfa.eval A). assumption.
Qed.


(** * 4. algebraic correctness of language inclusion checking for DFA *)

(** rather than minimising DFA, and comparing them up to isomorphism,
   we take a shorter path here, by focusing on language inclusion
   rather than equivalence, and by avoiding minimisation and
   isomophisms 

   Our goal is to prove that for any two DFA [A] and [B], 
   
     [dfa.lang A <== dfa.lang B] entails [eval A <== eval B]

   (The premisse is a language inclusion, while the conclusion is a KA
   derivation.) The corresponding result on language equivalence and KA
   equality follows easily.

   We use the same kind of trick as in Kozen's minimisation proof,
   except that we consider the matrix of language inclusions rather
   than the matrix of the Mihyll-Nerode relation. *)

Section E.

Variables A B: dfa.t.

(** thanks to the previous generalisation of the determinisation
 construction, we can assume w.l.o.g. that [vars A <== vars B]. This
 is required by our reduction of language inclusion to language
 emptiness ([dfa.lang_incl_dec]), but also to prove Lemma [R_M] below *)
Hypothesis Hvars: dfa.vars A <== dfa.vars B.

(** language inclusion matrix: 
   [R_(j,i)] holds iff [dfa.lang A i <== dfa.lang B j] 
   (Note that this matrix goes from [B] to [A].) *)
Definition R: rmx (n B) (n A) := fun j i => ofbool (dfa.lang_incl_dec _ _ Hvars i j).

(** the algebraic proof is quite similar to that of determinisation: we use the
   bisimulation rule for inclusions, with [R]:
   from [A^u <== B^u * R], [R * A^M <== B^M * R], and [R * A^v <== B^v],
   we deduce [A^u*A^M^**A^v <== B^u*B^M^**B^v] 

   the second and third hypotheses always hold, while the first one
   holds only if the language of [A] is contained in that of [B].

*)

Lemma R_v: R * A^v <== B^v. 
Proof.
  intros j i'. apply leq_supx. intros i _. simpl. clear i'. 
  setoid_rewrite <-andb_dot. apply ofbool_leq, le_bool_spec.
  setoid_rewrite Bool.andb_true_iff.  setoid_rewrite is_true_sumbool. 
  intros [H]. exact (H nil). 
Qed.

Lemma R_M: R * A^M^* <== B^M^* * R.
Proof.                          (* this proof also requires Hvars *)
  apply str_move_l.
  setoid_rewrite dotxsum. setoid_rewrite dotsumx. apply sup_leq'. exact Hvars.
  intros a Ha j i'. apply leq_supx. intros i _. 
  rewrite mx_dot_fun. setoid_rewrite <-dot_ofboolx.  
  unfold mx_fun. case eqb_spec. 2: ra. 
  intros ->. apply dot_leq. 2: reflexivity. apply ofbool_leq, le_bool_spec. 
  setoid_rewrite is_true_sumbool. intros H w Hw. apply (H (cons a w)). now split. 
Qed.

Hypothesis HAB: regex.lang (eval A) <== regex.lang (eval B).
Lemma R_u: A^u <== B^u * R. 
Proof. 
  intros z i. simpl. rewrite mx_dot_fun, dot1x. unfold mx_fun. clear z. 
  case eqb_ord_spec. 2: intro; apply leq_bx. 
  intros ->. apply epsilon_reflexive. unfold R.
  rewrite sumbool_true. reflexivity. 
  rewrite <-2dfa.eval_lang, <-2dfa.reroot_id. exact HAB. 
Qed.

(** algebraic correctness of language inclusion test *)
Theorem dfa_complete_leq: eval A <== eval B.
Proof. 
  apply mx_scal_leq. 
  rewrite R_u. 
  rewrite <-(dotA _ R), R_M.
  rewrite <-2dotA, R_v. 
  now rewrite dotA.
Qed.

End E.

(** * Completeness of KA *)

(** summing up all together, we obtain completeness of KA for language
   inclusion *)

Corollary ka_complete_leq: forall e f, lang e <== lang f -> e <== f.
Proof. 
  intros e f. 
  rewrite <-(eval_dfa nil e), <-(eval_dfa (dfa.vars (dfa nil e)) f). 
  apply dfa_complete_leq. lattice.
Qed. 

(** and thus for language equivalence *)

Corollary ka_complete_weq: forall e f, lang e == lang f -> e == f.
Proof. intros e f. rewrite 2weq_spec. now split; apply ka_complete_leq. Qed. 

(** since languages form a model of KA, the converse directions
   trivially hold, so that we actually have equivalences *)

Corollary ka_correct_complete_leq: forall e f, lang e <== lang f <-> e <== f.
Proof. split. apply ka_complete_leq. apply lang_leq. Qed. 

Corollary ka_correct_complete_weq: forall e f, lang e == lang f <-> e == f.
Proof. split. apply ka_complete_weq. apply lang_weq. Qed. 

(** * Decidability of KA *)

(** as additional corollaries, we obtain decidability of (in)equations
   in Kleene algebra *)

Corollary ka_leq_dec: forall e f: regex', {e<==f} + {~(e<==f)}.
Proof.
  assert(G: forall e f: regex',
    let A := dfa [] e in
    let B := dfa (dfa.vars A) f in
      dfa.lang A (dfa.u A) <== dfa.lang B (dfa.u B) <-> e<==f).
   intros e f A B. 
   rewrite <-2nfa.dfa.eval_lang, <-2dfa.reroot_id.
   rewrite ka_correct_complete_leq. 
   unfold A, B. now rewrite 2eval_dfa.
  intros. eapply sumbool_iff. apply G. apply dfa.lang_incl_dec. lattice.
Qed.  

Corollary ka_weq_dec: forall e f: regex', {e==f} + {~(e==f)}.
Proof.
  intros e f. destruct (ka_leq_dec e f). destruct (ka_leq_dec f e). 
   left. now apply antisym.
   right. rewrite weq_spec. tauto.  
   right. rewrite weq_spec. tauto.  
Qed.
