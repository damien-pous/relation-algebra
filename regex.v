(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * regex: the (flat) model of regular expressions *)

Require Import syntax kleene boolean lang lset sums normalisation.
Set Implicit Arguments.

(** We consider regular expressions over the alphabet of positive
   numbers

   (It would be nicer to keep the alphabet as a parameter, since we
   need to instantiate it with a more structured type in
   [kat_completeness]; it's however realy painful to do so, since this
   model is used thoroughly through several files (rmx, nfa,
   ka_completeness) and this would prevent us from using modules to
   structure the namespace. The current solution consists in
   retracting into positives the structured type used in
   [kat_completness], using [denum].)

*)

Definition sigma := positive.

(** the inductive type of regular expressions *)
Inductive regex := 
| r_zer 
| r_one 
| r_pls(e f: regex)
| r_dot(e f: regex)
| r_str(e: regex)
| r_var(a: sigma).

(** strict iteration is a derived operation *)
Definition r_itr e := r_dot e (r_str e).

(** inclusion into relational expressions  *)
Fixpoint to_expr (e: regex): expr_(BKA) (fun _ => xH) (fun _ => xH) xH xH := 
  match e with
    | r_zer => 0
    | r_one => 1
    | r_pls e f => to_expr e + to_expr f
    | r_dot e f => to_expr e * to_expr f
    | r_str e => to_expr e ^*
    | r_var a => e_var a
  end.

(** * Regular expressions form a Kleene algebra *)
(** ** Operations *)

(** we inherit the preorder and the equivalence relation from generic
   expressions *)
Definition r_leq e f := to_expr e <==_[BKA] to_expr f.
Definition r_weq e f := to_expr e ==_[BKA] to_expr f.

(** structures for regular expression operations *)
Canonical Structure regex_lattice_ops := {|
  car := regex;
  leq := r_leq;
  weq := r_weq;
  cup := r_pls;
  bot := r_zer;
  cap := assert_false r_pls;
  top := assert_false r_zer;
  neg := assert_false id
|}.

(** we use singleton type for the object(s), since this is a flat structure *)
CoInductive regex_unit := regex_tt.
Canonical Structure regex_ops := {|
  ob  := regex_unit;
  mor n m := regex_lattice_ops;
  dot n m p := r_dot;
  one n := r_one;
  itr n := r_itr;
  str n := r_str;
  cnv n m := assert_false r_str;
  ldv n m p := assert_false r_dot;
  rdv n m p := assert_false r_dot
|}.

(** shorthand fore [regex], when a morphism is required *)
Notation regex' := (regex_ops regex_tt regex_tt).
Definition var a: regex' := r_var a.

(** folding regular expressions to expose canonical preojections *)
Ltac fold_regex := ra_fold regex_ops regex_tt.


(** ** Laws *)
(** laws are inherited for free, by faithful embedding into general expressions *)

Instance regex_laws: laws BKA regex_ops.
Proof.
  apply (laws_of_faithful_functor (f:=fun _ _: regex_unit => to_expr)).
  constructor; try discriminate; trivial. 
  intros. constructor; try discriminate; trivial; now intros ???. 
  intros. symmetry. apply itr_str_l. 
  tauto. tauto.
Qed.

Instance regex_lattice_laws: lattice.laws BKA regex_lattice_ops. 
Proof. exact (@lattice_laws _ _ regex_laws regex_tt regex_tt). Qed.


(** * Predicates on regular expressions: 01, simple, pure *)

(** 01 regular expressions are those not containing variables, 
   they reduce either to [0] or to [1]  *)
Inductive is_01: regex' -> Prop := 
| is_01_zer: is_01 0
| is_01_one: is_01 1
| is_01_pls: forall e f, is_01 e -> is_01 f -> is_01 (e+f)
| is_01_dot: forall e f, is_01 e -> is_01 f -> is_01 (e*f)
| is_01_str: forall e, is_01 e -> is_01 (e^*).

(** simple regular expressions are those reducing to a sum of variables, possibly plus [1]
   (actually a bit less, since, e.g., [0*a*b] reduces to [0] but is forbidden) *)
Inductive is_simple: regex' -> Prop := 
| is_simple_zer: is_simple 0
| is_simple_one: is_simple 1
| is_simple_var: forall a, is_simple (var a)
| is_simple_pls: forall e f, is_simple e -> is_simple f -> is_simple (e+f)
| is_simple_dot: forall e f, is_01 e -> is_simple f -> is_simple (e*f)
| is_simple_str: forall e, is_01 e -> is_simple (e^*).

(** pure regular expressions are those without star, which reduce to a sum of variables 
   (same thing as above) *)
Inductive is_pure: regex' -> Prop := 
| is_pure_zer: is_pure 0
| is_pure_var: forall a, is_pure (var a)
| is_pure_pls: forall e f, is_pure e -> is_pure f -> is_pure (e+f)
| is_pure_dot: forall e f, is_01 e -> is_pure f -> is_pure (e*f).

(** [ofbool] produces 01 expressions *)
Lemma is_01_ofbool b: is_01 (ofbool b). 
Proof. case b; constructor. Qed.

(** any 01 expression is simple *)
Lemma is_01_simple e: is_01 e -> is_simple e.
Proof. induction 1; now constructor. Qed.



(** * Coalgebraic structure of regular expressions *)

(** ** epsilon membership  *)
Fixpoint epsilon (e: regex') :=
  match e with 
    | r_one 
    | r_str _ => true
    | r_pls e f => epsilon e || epsilon f
    | r_dot e f => epsilon e && epsilon f
    | e => false
  end%bool.
Notation eps e := (@ofbool regex_ops regex_tt (epsilon e)).

(** ** derivatives *)
Fixpoint deriv a (e: regex'): regex' := 
match e with
  | r_zer | r_one => 0
  | r_pls e f => deriv a e + deriv a f
  | r_dot e f => deriv a e * f + eps e * deriv a f
  | r_str e => deriv a e * (e: regex')^*
  | r_var b => ofbool (eqb_pos a b)
end.

(** word derivatives *)
Fixpoint derivs w e := 
  match w with
    | nil => e
    | cons a w => derivs w (deriv a e)
  end.

(** set of variables appearing in a regular expression *)
Fixpoint vars (e: regex') := 
match e with
  | r_zer | r_one => nil
  | r_pls e f | r_dot e f => app (vars e) (vars f)
  | r_str e => vars e
  | r_var a => cons a nil
end.

(** ** fundamental expansion theorem  *)

Theorem expand' (e: regex') A: vars e <== A -> 
  e == eps e + \sum_(a\in A) var a * deriv a e. 
Proof. 
  induction e; simpl vars; intro HA; simpl deriv; fold_regex. 
  + rewrite sup_b, cupxb; ra. 
  + rewrite sup_b, cupxb; ra.
  + apply cup_spec in HA as [HA1 HA2]. 
    simpl epsilon. setoid_rewrite orb_pls. 
    setoid_rewrite dotxpls. rewrite supcup. 
    rewrite IHe1 at 1 by assumption. 
    rewrite IHe2 at 1 by assumption. simpl. fold_regex. ra.    
  + apply cup_spec in HA as [HA1 HA2]. 
    setoid_rewrite dotxpls. rewrite supcup. 
    rewrite IHe1 at 1 by assumption. rewrite dotplsx.
    rewrite IHe2 at 1 by assumption. rewrite dotxpls.
    rewrite dotxsum, dotsumx.
    simpl epsilon. rewrite andb_dot. 
    setoid_rewrite dot_ofboolx. setoid_rewrite dotA. 
    ra. 
  + specialize (IHe HA). clear HA. 
    simpl epsilon. setoid_rewrite dotA. rewrite <-dotsumx.
    set (f := \sum_(i\in A) var i * deriv i e) in *. clearbody f. 
    rewrite IHe. case epsilon; ra_normalise; rewrite ?str_pls1x; apply str_unfold_l. 
  + setoid_rewrite cupbx. apply antisym. 
    rewrite <- (leq_xsup _ _ a) by (apply HA; now left). 
    rewrite eqb_refl. ra. 
    apply leq_supx. intros b _. case eqb_spec; try intros <-; ra. 
Qed.

Corollary expand e: e == eps e + \sup_(a\in vars e) var a * deriv a e.
Proof. apply expand'. reflexivity. Qed.

(* not used currently ; can easily be proved directly *)
Corollary deriv_cancel a e: var a * deriv a e <== e.
Proof. 
  rewrite (@expand' e ([a]++vars e)) at 2 by lattice.
  simpl. fold_regex. ra.
Qed.


(** ** monotonicity of [epsilon] *)
(** trick to prove that epsilon is monotone: show that it's an
   evaluation into the boolean KA *)
Lemma epsilon_eval e: epsilon e = 
  eval (X:=bool_ops) (f':=fun _ => bool_tt) (fun _ => false) (to_expr e).
Proof. induction e; simpl; trivial; now rewrite IHe1, IHe2. Qed.

Instance epsilon_leq: Proper (leq ==> leq) epsilon.
Proof. intros e f H. rewrite 2epsilon_eval. apply H. apply lower_laws. Qed.
Instance epsilon_weq: Proper (weq ==> eq) epsilon := op_leq_weq_1.



(** ** monotonicity of derivation *)

(** we first need induction scheme for leq/weq *)

Definition re_ind leq weq := mk_ops regex_unit 
  (fun _ _ => lattice.mk_ops regex' leq weq r_pls r_pls id r_zer r_zer) 
  (fun _ _ _ => r_dot) 
  (fun _ => r_one) 
  (fun _ => r_itr) 
  (fun _ => r_str) 
  (fun _ _ => assert_false r_str)
  (fun _ _ _ => assert_false r_dot)
  (fun _ _ _ => assert_false r_dot).

Lemma re_ind_eval leq weq (e: regex'): 
  eval (X:=re_ind leq weq) (f':=fun _ =>regex_tt) var (to_expr e) = e. 
Proof. induction e; simpl in *; reflexivity || congruence. Qed.

Lemma leq_ind leq weq (L: laws BKA (re_ind leq weq)) (e f: regex'): e <== f -> leq e f.
Proof. 
  intro H. rewrite <-(re_ind_eval leq weq e), <-(re_ind_eval leq weq f). apply (H _ L). 
Qed.

(** monotonicity of [deriv] *)
Instance deriv_leq a: Proper (leq ==> leq) (deriv a).
Proof.
  intros e f. apply (@leq_ind 
  (fun e f => e <== f /\ deriv a e <== deriv a f) 
  (fun e f => e == f /\ deriv a e == deriv a f)).
  constructor; simpl; (try discriminate); (repeat intros _); (repeat right); 
    fold_regex; repeat intros _.
   constructor; simpl; (try discriminate); fold_regex; intros. 
   - constructor. intro. split; reflexivity. 
     intros ? ? ? [? ?] [? ?]; split; etransitivity; eassumption. 
   - rewrite 2weq_spec. tauto.
   - rewrite 2cup_spec. tauto. 
   - right. fold_regex.  split; apply leq_bx.
   - split. apply dotA. rewrite andb_dot. ra. 
   - split. apply dot1x. ra. 
   - split. apply dotx1. ra. 
   - intros x x' [Hx Hx'] y y' [Hy Hy']. split. now apply dot_leq.
     simpl; fold_regex. rewrite Hx', Hy', Hy. now rewrite Hx. 
   - split. ra. rewrite orb_pls. ra. 
   - split; ra. 
   - split; ra.
   - split; ra. 
   - split. apply str_refl. lattice.
   - split. apply str_cons. rewrite str_unfold_l. case epsilon; ra. 
   - intros x z [H H']. split. now apply str_ind_l.
     apply str_ind_l in H. rewrite <-dotA, H, dot1x. hlattice.
   - intros x z [H H']. split. now apply str_ind_r.
     apply cup_spec in H' as [H1 H2]. rewrite dotA, H2. ra_normalise. 
     now apply str_ind_r.
   - split. apply itr_str_l. reflexivity.
Qed.

Instance deriv_weq a: Proper (weq ==> weq) (deriv a) := op_leq_weq_1.

Instance derivs_leq w: Proper (leq ==> leq) (derivs w).
Proof. induction w; intros e f H. apply H. apply IHw, deriv_leq, H. Qed.

Instance derivs_weq w: Proper (weq ==> weq) (derivs w) := op_leq_weq_1.


(** ** deriving and expanding 01 regular expressions *)

Lemma deriv_01 a e: is_01 e -> deriv a e == 0.
Proof. 
  induction 1; simpl deriv; fold_regex. 
   reflexivity.
   reflexivity. 
   rewrite IHis_01_1, IHis_01_2. apply cupI. 
   rewrite IHis_01_1, IHis_01_2. ra.
   rewrite IHis_01. apply dot0x.
Qed.

Lemma expand_01 e: is_01 e -> e == eps e.
Proof.
  intro H. rewrite (expand e) at 1. 
  rewrite sup_b. apply cupxb. 
  intros. rewrite deriv_01 by assumption. apply dotx0. 
Qed.


(** ** `pure part' of a regular expression *)

Fixpoint pure_part (e: regex'): regex' :=
  match e with
    | r_pls e f => pure_part e + pure_part f
    | r_dot e f => eps e * pure_part f
    | r_str _ | r_one | r_zer => 0
    | r_var _ => e
  end.

Lemma is_pure_pure_part e: is_pure (pure_part e).
Proof. induction e; simpl pure_part; constructor; trivial. apply is_01_ofbool. Qed.


(** ** expanding simple regular expressions *)

Lemma str_eps e: eps e ^* == 1.
Proof. case epsilon. apply str1. apply str0. Qed.

(* à dériver de [expand] ? *)
Lemma expand_simple e: is_simple e -> e == eps e + pure_part e.
Proof.
  induction 1; simpl; fold_regex.
   lattice.
   lattice.
   lattice.
   rewrite orb_pls. rewrite IHis_simple1 at 1. rewrite IHis_simple2 at 1. lattice.
   rewrite andb_dot. rewrite (@expand_01 e) at 1 by assumption. 
    rewrite IHis_simple at 1. ra. 
   rewrite cupxb. rewrite (@expand_01 e) at 1 by assumption. apply str_eps. 
Qed.


(** ** epsilon, derivatives, and expansion of pure regular expressions *)

Lemma epsilon_pure e: is_pure e -> epsilon e = false.
Proof. 
  induction 1; trivial. simpl. 
  now rewrite IHis_pure1. 
  simpl. rewrite IHis_pure. now case epsilon.
Qed.


Lemma epsilon_deriv_pure a e: is_pure e -> eps (deriv a e) == deriv a e.
Proof.
  induction 1; simpl; fold_regex. 
  reflexivity. 
  rewrite <-expand_01. reflexivity. apply is_01_ofbool. 
  rewrite orb_pls. now apply cup_weq.
  rewrite orb_pls, 2andb_dot, IHis_pure. 
  rewrite deriv_01 by assumption. case (epsilon e); simpl; fold_regex; ra.
Qed.

Lemma expand_pure e A: is_pure e -> vars e <== A -> e == \sum_(a \in A) var a * deriv a e .
Proof.
  intros He HA. rewrite (expand' e HA) at 1. 
  rewrite epsilon_pure by assumption. apply cupbx.  
Qed.


(** additional properties *)

Lemma deriv_sup a I J (f: I -> regex'):
  deriv a (\sup_(i\in J) f i) = \sup_(i\in J) deriv a (f i). 
Proof. apply f_sup_eq; now f_equal. Qed.

Lemma epsilon_reflexive e: epsilon e -> 1 <== e.
Proof. intro H. rewrite (expand e), H. lattice. Qed.



(** * Language interpretation of regular expressions  *)

(** ** language of a regular expression, coalgebraically *)

Definition lang e: lang' sigma := fun w => epsilon (derivs w e).

Instance lang_leq: Proper (leq ==> leq) lang.
Proof. intros e f H w. unfold lang. now rewrite H. Qed.

Instance lang_weq: Proper (weq ==> weq) lang := op_leq_weq_1.

(** (internal) characterisation of [epsilon] *)
Lemma epsilon_iff_reflexive_eps (e: regex'): epsilon e <-> 1 <== eps e.
Proof. 
  case epsilon. intuition. intuition. discriminate. 
  apply lang_leq in H. specialize (H [] eq_refl). discriminate.
Qed.


(** ** [lang] is a KA morphism *)

(** to prove that [lang] is a morphism, we characterise it
   inductively, as the unique morphism such that [lang (e_var i)] is
   the language reduced to the letter [i], ([eq [i]]) *)

Notation elang e := (eval (f':=fun _=>lang_tt) (fun i => eq [i]) (to_expr e)).

(** language characterisation of [epsilon]  *)
Lemma epsilon_iff_lang_nil e: epsilon e <-> (elang e) []. 
Proof. 
 induction e; simpl.  
  firstorder discriminate. 
  firstorder. 
  setoid_rewrite Bool.orb_true_iff. now apply cup_weq.
  setoid_rewrite Bool.andb_true_iff. setoid_rewrite lang_dot_nil. now apply cap_weq.
  split. now exists O. reflexivity. 
  firstorder discriminate. 
Qed.

(** regular expression derivatives precisely correspond to language derivatives *)
Lemma eval_deriv a e: elang (deriv a e) == lang_deriv a (elang e).
Proof.
  induction e; simpl deriv; simpl eval; fold_regex; fold_lang.  
  - reflexivity. 
  - now rewrite lang_deriv_1.
  - rewrite lang_deriv_pls. now apply cup_weq. 
  - generalize (epsilon_iff_lang_nil e1). case epsilon; intro He1. 
     setoid_rewrite dot1x. 
     setoid_rewrite lang_deriv_dot_1. 2: now apply He1. 
     now rewrite <- IHe1, <- IHe2. 
     setoid_rewrite dot0x.
     setoid_rewrite lang_deriv_dot_2. 2: clear -He1; intuition discriminate. 
     rewrite <- IHe1. apply cupxb. 
  - rewrite lang_deriv_str. now rewrite <- IHe.
  - case eqb_spec. intros <- w. compute. split. now intros <-. now intro E; injection E. 
    intros D w. compute. split. intros []. intro E. apply D. injection E. congruence. 
Qed.

(** we deduce that both notions of language coincide: [lang] is the
   unique morphism from the coalgebra of regular expressions to the
   final coalgebra of languages *)
Theorem lang_eval e: lang e == elang e.
Proof.
  unfold lang. intro w. revert e. induction w as [|a w IH]; intro e; simpl derivs.
  - apply epsilon_iff_lang_nil.
  - rewrite IH. apply eval_deriv. 
Qed.

(** as a consequence, [lang] is a KA morphism *)
Corollary lang_0: lang 0 == bot.
Proof. now rewrite lang_eval. Qed.

Corollary lang_1: lang 1 == 1.
Proof. now rewrite lang_eval. Qed.

Corollary lang_var i: lang (var i) == eq [i].
Proof. now rewrite lang_eval. Qed.

Corollary lang_pls e f: lang (e+f) == lang e \cup lang f.
Proof. now rewrite 3lang_eval. Qed.

Corollary lang_sup I J (f: I -> _): lang (sup f J) == \sup_(i\in J) lang (f i).
Proof. apply f_sup_weq. apply lang_0. apply lang_pls. Qed.

Corollary lang_dot e f: lang (e*f) == lang e * lang f.
Proof. now rewrite 3lang_eval. Qed.

Corollary lang_itr e: lang (e^+) == lang e^+.
Proof. rewrite 2lang_eval. simpl (elang _). symmetry. apply itr_str_l. Qed.
