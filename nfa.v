(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * nfa: Non-deterministic Finite Automata *)

Require Import positives comparisons.
Require Import kleene regex rmx sums matrix_ext prop normalisation.
Require dfa.
Set Implicit Arguments.
Unset Printing Implicit Defensive.

(** * Matricial (non deterministic) finite automata *)

(** transitions are labelled with regular expressions *)
Record t := mk {
  n: nat; 
  u: rmx 1 n;
  M: rmx n n;
  v: rmx n 1 
}.
Notation "x ^u" := (u x) (at level 2, left associativity).
Notation "x ^M" := (M x) (at level 2, left associativity).
Notation "x ^v" := (v x) (at level 2, left associativity).

(** formal evaluation of matricial automata into regular expressions *)
Definition eval A := mx_scal (A^u * A^M^* * A^v).
Arguments eval !_ /.

(** two important classes of automata: 
   - NFA, for which transitions are labelled by sums of letters, and
   - NFA with epsilon-transitions, where the sums may also include [1] *)

Definition is_nfa  e := is_01_mx e^u /\ is_pure_mx e^M   /\ is_01_mx e^v.
Definition is_enfa e := is_01_mx e^u /\ is_simple_mx e^M /\ is_01_mx e^v.

(** characterisation of epsilon for automata with a pure transition matrix *)
Lemma epsilon_eval n u (M: rmx n n) v: is_pure_mx M -> 
  (epsilon (mx_scal (u*M^**v))  <->  epsilon (mx_scal (u*v))).
Proof.
  intro HM. rewrite 2epsilon_iff_reflexive_eps. 
  rewrite 2(scal_mx_map (fun e => eps e)). 
  rewrite 3epsilon_mx_dot, epsilon_mx_str, (epsilon_mx_pure HM).
  now rewrite str0, dotx1. 
Qed.

(** characterisation of derivatives for NFA *)
Lemma deriv_eval a n u (M: rmx n n) v: is_01_mx u -> is_pure_mx M -> is_01_mx v ->
 deriv a (mx_scal (u*M^**v))  ==  mx_scal (u*epsilon_mx (deriv_mx a M)*M^**v).
 (* NB: we use epsilon_mx because [deriv_mx a M] is not necessarily a 01 matrix, 
        even if it is equal to such a matrix *)
Proof.
  intros Hu HM Hv. 
  rewrite (scal_mx_map (deriv a)). apply mx_scal_weq. 
  rewrite 2deriv_mx_dot, deriv_mx_str_strict. 2: apply epsilon_mx_pure; assumption. 
  rewrite <-expand_01_mx by assumption. 
  rewrite (deriv_01_mx _ Hu), (deriv_01_mx _ Hv), epsilon_deriv_pure_mx by assumption.
  ra.
Qed.

(** * Language of a NFA *)
(** (operationally, not through evaluation into regular expressions) *)
Fixpoint lang n (M: rmx n n) v u w: Prop := 
  match w with 
    | nil => epsilon (mx_scal (u * v))
    | cons a w => lang M v (u * epsilon_mx (deriv_mx a M)) w
  end.
(* NB: like above, we have to use [epsilon_mx] because [u * deriv_mx a M] is 
   only equal to a 01-matrix *)

(** the language of the NFA is that obtained by evaluation into regular expressions *)
Theorem eval_lang n u M v (H: is_nfa (@mk n u M v)):
  regex.lang (mx_scal (u * M^* * v)) == lang M v u.
Proof.
  unfold regex.lang. intro w. revert u H. induction w; intros u H. 
   unfold derivs. now rewrite epsilon_eval by apply H.
   unfold derivs. setoid_rewrite <- IHw. 
   clear IHw. revert w. apply lang_weq, deriv_eval; apply H. 
   split. 2: apply H. apply is_01_mx_dot. apply H. apply is_01_mx_epsilon.
Qed. 


(** additional bureaucratic lemmas *)
Instance lang_leq n (M: rmx n n) v: Proper (leq ==> leq) (lang M v).
Proof. 
  intros u u' H w. revert u u' H; induction w; intros u u' H; unfold lang; fold lang.
  now rewrite H. 
  apply IHw. now rewrite H. 
Qed.

Instance lang_weq n (M: rmx n n) v: Proper (weq ==> weq) (lang M v) := op_leq_weq_1.

Instance lang_weq' n (M: rmx n n) v: Proper (weq ==> eq ==> iff) (lang M v).
Proof. intros ? ? H ? ? <-. now apply lang_weq. Qed.

Lemma lang_empty n (u: rmx 1 n) M v: u==0 -> lang M v u == bot.
Proof. 
  intros Hu w. revert Hu. induction w; intro Hu. simpl; fold_regex. 
  rewrite Hu, dot0x. intuition. 
  simpl. rewrite <-IHw by assumption. now rewrite Hu, dot0x.
Qed.


(** * Injection of DFA into NFA  *)
Module dfa.

(** injection into NFA *)
Definition to_nfa (A: dfa.t): t := mk 
  (mx_fun (fun _ => dfa.u A) 1)
  (\sum_(a\in dfa.vars A) mx_fun (fun x => dfa.M A x a) (var a))
  (fun i _ => ofbool (dfa.v A i)).

(** injected DFA are indeed NFA *)
Lemma is_nfa_nfa A: is_nfa (to_nfa A). 
Proof. 
  split. intros ? ?. simpl. unfold mx_fun. case eqb_ord; constructor. 
  split. intros ? ?. simpl. rewrite mx_sup. apply is_pure_sup. 
   intros. unfold mx_fun. case eqb_ord; constructor.
  intros ? ?. apply is_01_ofbool. 
Qed.


(** evaluation at a given state, into regular expressions *)
Notation "A @ i" := (eval (to_nfa (dfa.reroot A i))) (at level 1).


(** the language of a DFA coincides with that of the underlying NFA *)
Theorem nfa_lang A i: dfa.lang A i == 
  lang ((to_nfa A)^M) ((to_nfa A)^v) (mx_fun (fun _ => i) 1).
Proof.
  intro w. revert i. induction w; intro i; simpl. 
  - rewrite epsilon_iff_reflexive_eps. rewrite (scal_mx_map (fun e => eps e)).
    change (mx_dot regex_ops regex_tt) with (@dot (mx_ops regex_ops regex_tt)).
    rewrite (mx_dot_kfun1 (X:=regex_ops)).
    unfold mx_map, mx_scal. rewrite <-epsilon_iff_reflexive_eps. case dfa.v; reflexivity.
  - rewrite IHw. clear IHw.
    change (mx_dot regex_ops regex_tt) with (@dot (mx_ops regex_ops regex_tt)).
    rewrite (mx_dot_kfun1 (X:=regex_ops)). unfold mx_fun, epsilon_mx, mx_map. 
    setoid_rewrite mx_sup. setoid_rewrite deriv_sup. setoid_rewrite epsilon_sup. split. 
    + intros [Ha H]. eapply lang_leq. 2: apply H. clear w H. 
      intros _ j. rewrite <-(leq_xsup _ _ a Ha). 
      case eqb_ord. 2: apply leq_bx. 
      simpl. now rewrite eqb_refl.
    + intros H. split. case (List.in_dec (cmp_dec _) a (dfa.vars A)) as [Ha|Ha]. assumption. 
       apply lang_empty in H. elim H. clear H. 
       intros o j. apply sup_b. intros b Hb. case eqb_ord. 2: reflexivity. 
       simpl. case eqb_spec; simpl. 2: reflexivity. 
       intros <-.  elim (Ha Hb).       
      eapply lang_leq. 2: apply H. clear w H.
      intros _ j. apply leq_supx. intros b _. 
      case eqb_spec. 2: intros; ra. 
      intros ->. simpl. case eqb_spec; simpl. 2: intro; lattice.
      intros <-. now rewrite eqb_refl.
Qed.

(** the language of the DFA is that obtained by evaluation into regular expressions *)
Corollary eval_lang A i: regex.lang A@i == dfa.lang A i.
Proof. setoid_rewrite eval_lang. 2: apply is_nfa_nfa. now rewrite nfa_lang. Qed.

End dfa.

Coercion dfa.to_nfa: dfa.t >-> t.
