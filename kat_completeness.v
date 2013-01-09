(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * kat_completeness: completeness of Kleene algebra with tests *)

(** We closely follow Dexter Kozen and Frederick Smith' proof:
   Kleene algebra with tests: Completeness and decidability. 
   In Proc. CSL'96, vol. 1258 of LNCS, pages 244-259, 1996. Springer-Verlag.

   The only difference is that we do the proof directly for _typed_ KAT.

   (We cannot easily exploit an untyping theorem, like we do in the
   case of KA: although the untyping theorem holds for KAT, it
   actually follows from typed completeness - at least we did not find
   an alternative way of proving it)

   The proof can be summarised as follows:
   one exhibits a function [hat: gregex n m -> gregex n m] such that:
   1. forall x, KAT |- hat x == x 
   2. forall x, G(hat x) == R(hat x), where 
      . G(y) is the typed guarded strings interpretation of y
      . R(y) is the language interpretation of y, seen as a regular expression
   (the concrete coercions will be specified later on)

   From these properties, it follows that for all x,y: gregex n m, we have
           G(x) == G(y)
 =>    G(hat x) == G(hat y)          (1, and G is a model)
 =>    R(hat x) == R(hat x)          (2)
 => KA |- hat x == hat y             (KA completeness)
 => KA |- hat x == hat y : n -> m    (untyping theorem for KA)
 => KAT|- hat x == hat y : n -> m    (KA theorems hold in KAT)
 => KAT|-     x == y : n -> m        (1, and transitivity)
   
   (the converse is immediate, G being a model) *)

Require Import denum lset sums normalisation.
Require Import kat ka_completeness untyping.
Require Import regex gregex lsyntax syntax lang glang boolean atoms.
Set Implicit Arguments.

(** abbreviations: [R] is the module about regular expressions, while
   [G] is the module about generalised regular expressions *)
Module R := regex.
Module G := gregex.

Section s.
Notation Sigma := positive.
Variable pred: nat.
Variables src tgt: Sigma -> positive.
Notation gregex := (gregex_kat_ops pred src tgt).
Notation Atom := (ord (pow2 pred)).
Notation gword := (trace Atom).
Notation glang := (tglang_kat_ops pred src tgt). 
Notation g_atom n a := (@g_prd pred src tgt n (@atom pred a)).
Notation test := (lsyntax.expr (ord pred)).

(** * 1. Definition of the [hat] function, and correctness *)

(** ** externally guarded terms *)

(** the hat function is defined by induction on the structure of its
   argument, but it actually produces formal sums of "externally
   guarded terms", defined by the following inductive *)

Inductive guard: positive -> positive -> Type :=
| g_pred: forall {n} (a: Atom), guard n n
| g_elem: forall n m (a: Atom) (e: gregex n m) (b: Atom), guard n m.
Notation guards n m := (list (guard n m)).

(** externally guarded terms, and sums of such terms can be converted
   back to [gregex] in the obvious way *)
Definition geval n m (x: guard n m) :=
  match x with 
    | g_pred n a => g_atom n a
    | g_elem n m a e b => g_atom n a * e * g_atom m b
  end.
Notation teval := (sup (@geval _ _)).

(** ** inductive cases for the [hat] function *)

(** *** predicates *)

(** a predicate is mapped to the set of atoms under which it is satisfied *)
Definition g_prd' n p: guards n n  := 
  map g_pred (filter (fun a => lsyntax.eval (set.mem a) p) (seq (pow2 pred))).

Lemma teval_prd n (p: tst n): teval (g_prd' n p) == inj p. 
Proof.
  unfold g_prd'. rewrite sup_map. unfold geval. 
  setoid_rewrite <-inj_sup. apply inj_weq.
  symmetry. apply decomp_expr.
Qed.

(** *** unit *)

(** accordingly, [1] is simply mapped to the set of all atoms *)
Definition g_one' n := g_prd' n (@lsyntax.e_top _).

Lemma teval_one n: teval (g_one' n) == 1. 
Proof. unfold g_one'. rewrite teval_prd. apply inj_top. Qed.

(** *** letters *)

(** a Kleene variable [i] is mapped to the sum of all [f*i*g], for f,g
   arbitrary atoms *)

Definition g_var' i := \sup_(f<_) \sup_(g<_) [g_elem f (g_var i) g].

Lemma sum_atoms n: \sup_(i<pow2 pred) g_atom n i == 1.
Proof.
  rewrite <- teval_one. unfold g_one', g_prd'. rewrite sup_map.
  apply sup_weq. reflexivity. 
  induction seq. reflexivity. now apply (cup_weq [_] [_]).
Qed.

Lemma teval_var i: teval (g_var' i) == g_var i.
Proof.
  unfold g_var'. rewrite sup_sup. setoid_rewrite sup_sup.
  setoid_rewrite sup_singleton. unfold geval.
  setoid_rewrite <-dotxsum. setoid_rewrite <-dotA. rewrite <-dotsumx.
  setoid_rewrite sum_atoms. ra. 
Qed.

(** *** composition *)

(** composition is defined by a kind of coalesced product: we take all
   products such that the post-guard of the former element coincides
   with the pre-guard of the latter *)

(** [g_dot1 x y] tries to compose two externally guarded terms *)
Definition g_dot1 n m (x: guard n m): forall p, guard m p -> guards n p  := 
  match x with
    | g_pred _ a => fun p y => 
      match y with 
        | g_pred _ b       => if eqb a b then [g_pred a] else []
        | g_elem _ _ b e c => if eqb a b then [g_elem b e c] else []
      end
    | g_elem _ _ a e b => fun p y => 
      match y with 
        | g_pred _ c => fun e => if eqb b c then [g_elem a e b] else []
        | g_elem _ _ c f d => fun e => if eqb b c then [g_elem a (e*g_atom _ b*f) d] else []
      end e
  end.

(** [g_dot' h k] does the composition of two lists of externally guarded terms *)
Definition g_dot' n m p (h: guards n m) (k: guards m p) := 
  \sup_(x\in h) \sup_(y\in k) g_dot1 x y.

(** the correctness of this construction relies on the following two lemma *)
Lemma empty_atom_dot n a b: a<>b -> g_atom n a * g_atom n b == 0.
Proof. 
  intros. setoid_rewrite <-inj_cap.
  rewrite (empty_atom_cap H). apply inj_bot. 
Qed.

Lemma idem_atom_dot n a: g_atom n a * g_atom n a == g_atom n a.
Proof. setoid_rewrite <-inj_cap. now rewrite capI. Qed.

(** correctness of [g_dot1] *)
Lemma geval_dot n m p (x: guard n m) (y: guard m p): teval (g_dot1 x y) == geval x * geval y.
Proof.
  destruct x as [? a|? ? a e b]; destruct y as [? c|? ? c f d]; unfold g_dot1; 
    (case eqb_spec; [intros <-|intro E]); unfold geval; rewrite ?sup_singleton; unfold sup.
  - now rewrite idem_atom_dot.
  - symmetry. apply (empty_atom_dot _ E). 
  - now rewrite 2dotA, idem_atom_dot.
  - rewrite 2dotA, (empty_atom_dot _ E). ra.
  - now rewrite <-3dotA, idem_atom_dot.
  - rewrite <-2dotA, (empty_atom_dot _ E). ra.
  - transitivity (g_atom _ a*(e*(g_atom _ b*g_atom _ b)*f)*g_atom _ d). 2:ra. 
    now rewrite idem_atom_dot.
  - transitivity (g_atom _ a*(e*(g_atom _ b*g_atom _ c)*f)*g_atom _ d). 2:ra. 
    rewrite (empty_atom_dot _ E). ra.
Qed.

(** correctness of [g_dot'] *)
Lemma teval_dot n m p (x: guards n m) (y: guards m p):
  teval (g_dot' x y) == teval x * teval y.
Proof.
  unfold g_dot'. rewrite sup_sup. setoid_rewrite sup_sup.
  setoid_rewrite geval_dot. 
  rewrite dotsumx. now setoid_rewrite dotxsum. 
Qed.


(** *** Kleene star *)

(** Kleene star is defined by induction on the list of externally
   guarded terms, see Kozen and Smith' paper *)

Definition fst n m (x: guard n m) := match x with g_pred _ a | g_elem _ _ a _ _ => a end.
Definition lst n m (x: guard n m) := match x with g_pred _ a | g_elem _ _ _ _ a => a end.
Definition g_inner_dot n m (x: guard n m): forall p, guard m p -> gregex n p :=
  match x with
    | g_pred _ a => fun p y => 
      match y with 
        | g_pred _ b       => 0
        | g_elem _ _ b e c => if eqb a b \cap eqb a c then e else 0
      end
    | g_elem _ _ a e b => fun p y => 
      match y with 
        | g_pred _ c => fun e => if eqb a b \cap eqb b c  then e else 0
        | g_elem _ _ c f d => fun e => if eqb b c \cap eqb a d then e*g_atom _ b*f else 0
      end e
  end.

Definition xitr n m (r: guard n m) q' :=
  let rq' := g_dot' [r] q' in
  let a := fst r in
  let p := sup (@g_inner_dot _ _ r _) q' in
    g_dot' ([g_elem a (p*(g_atom _ a*p)^*) a]++g_one' _) rq'.

Fixpoint g_str' n (x: guards n n) := 
  match x with
    | [] => g_one' _
    | r::q => 
      let q' := g_str' q in
      q' ++ g_dot' q' (xitr r q')
  end.

(** the correctness of this construction is substantially more involved than for the other ones *)

Lemma geval_fst n m (r: guard n m): geval r == g_atom _ (fst r) * geval r. 
Proof.
  destruct r.
   simpl fst; unfold geval. now rewrite idem_atom_dot. 
   simpl fst; unfold geval. now rewrite 2dotA, idem_atom_dot.
Qed.

Lemma geval_lst n m (r: guard n m): geval r == geval r * g_atom _ (lst r). 
Proof.
  destruct r.
   simpl fst; unfold geval. now rewrite idem_atom_dot. 
   simpl fst; unfold geval. now rewrite <-3dotA, idem_atom_dot.
Qed.

Definition dirac n m: gregex n m.
case (eqb_pos_spec n m). intros <-. exact 1. intros _. exact 0. 
Defined.

Lemma dirac_refl n: dirac n n = 1.
Proof.
  unfold dirac. case eqb_pos_spec. 2: congruence. 
  intro. now rewrite cmp_eq_rect_eq. 
Qed.

Lemma teval_inner_dot n m p (x: guard n m) (y: guard m p):
  dirac n p + g_atom _ (fst x) * g_inner_dot x y * g_atom _ (fst x) == 
  dirac n p + ofbool (eqb (fst x) (lst y)) * geval x * geval y.
Proof.
  unfold g_inner_dot.
  revert p y. destruct x as [n a|n m a e b]; destruct y as [p c|p q c f d];
    simpl fst; simpl lst; simpl geval. 
   rewrite dirac_refl. case eqb. 2: ra. ra_normalise. 
    setoid_rewrite <-inj_cap. rewrite <-inj_top, <-inj_cup. apply inj_weq. lattice. 
   case eqb_spec; intro E. subst. case eqb_spec; intro E'. subst. 
    simpl. ra_normalise. now rewrite idem_atom_dot.
    ra. 
    simpl. ra_normalise. rewrite <-(dotA _ (g_atom p a)). 
    rewrite empty_atom_dot by assumption. ra.
   case eqb_spec; intro E. subst. case eqb_spec; intro E'. subst. 
    simpl. ra_normalise. now rewrite <-3dotA, idem_atom_dot.
    ra. 
    simpl. case eqb_spec; intro E'. subst. ra_normalise. 
     rewrite <-dotA. rewrite empty_atom_dot by congruence. ra.
     ra. 
   case eqb_spec; intro E. subst. case eqb_spec; intro E'. subst. 
    simpl. ra_normalise. now rewrite <-(dotA _ (g_atom p c) (g_atom p c)), idem_atom_dot.
    ra. 
    simpl. case eqb_spec; intro E'. subst. 
     ra_normalise. rewrite <-(dotA _ (g_atom p b) (g_atom p c)), empty_atom_dot by assumption.
      ra. 
     ra. 
Qed.

Lemma teval_xitr n m (r: guard n m) q: teval (xitr r q) == (geval r * teval q)^+.
Proof.
  unfold xitr. 
  rewrite 2teval_dot, sup_app, 2sup_singleton, teval_one. 
  symmetry. rewrite itr_str_l. rewrite (geval_fst r) at 2. 
  rewrite <-(dotA (g_atom _ _)), str_dot. 
  apply dot_weq. 2: reflexivity. 
  rewrite cupC. unfold geval at 3. rewrite dotA. rewrite <-itr_str_l. 
  rewrite itr_aea by now rewrite idem_atom_dot. rewrite <-str_itr. apply str_weq1.
  induction q as [|e q IH]. ra. 
  simpl (sup _ _). 
  rewrite 2dotxpls, 2dotplsx. rewrite <-(cupI 1), 2cupA, 2comm4. apply cup_weq. 
  2: assumption. clear IH.
  rewrite <-dirac_refl. rewrite teval_inner_dot. 
  case eqb_spec; intro E. 
   setoid_rewrite dot1x. rewrite E. now rewrite <-dotA, <-geval_lst.
  rewrite (geval_lst e), <-2dotA, empty_atom_dot by congruence. ra. 
Qed.

Lemma teval_str n (x: guards n n): teval (g_str' x) == teval x ^*.
Proof.
  induction x as [|r q IH]; simpl g_str'. 
  rewrite teval_one. symmetry. apply str0.
  simpl (sup _ _). setoid_rewrite (cupC (geval r)). rewrite str_pls.
  rewrite sup_app, teval_dot, teval_xitr, IH. rewrite (str_itr (_*_)). ra. 
Qed.

(** ** summing up the constructions, by induction *)

Fixpoint hat n m (e: gregex n m): guards n m := 
  match e with
    | g_zer _ _ => []
    | g_prd n p => g_prd' n p
    | g_pls _ _ e f => hat e \cup hat f
    | g_dot _ _ _ e f => g_dot' (hat e) (hat f)
    | g_itr _ e => g_dot' (hat e) (g_str' (hat e))
    | g_var i => g_var' i
  end.

Theorem teval_hat n m (e: gregex n m): teval (hat e) == e.
Proof.
  induction e; simpl hat. 
   reflexivity.
   apply teval_prd. 
   apply teval_var. 
   setoid_rewrite sup_app. now apply cup_weq. 
   rewrite teval_dot. now apply dot_weq.
   rewrite teval_dot, teval_str, <-itr_str_l. now apply itr_weq. 
Qed.



(** * Relationship between generalised regular expressions and (plain) regular expressions *)

(** ** extended alphabet *)

(** a letter in the extended alphabet is either a Kleene variable, a
   positive predicate variable, or a negative one. We moreover need to
   record the type of the corresponding test in the two latter cases *)

Inductive letter :=
| l_pos (n: positive) (p: ord pred)
| l_neg (n: positive) (p: ord pred)
| l_var (i: Sigma).

(** the above type can be retracted into positives: this saves us from
   proving KA completeness on an arbitrary alphabet (this would
   require a lot of polymorphic definitions) *)

Definition lp (l: letter): positive :=
  match l with
    | l_pos n x => mk_sum (inl (mk_sum (inl (mk_pair (n, mk_ord x)))))
    | l_neg n x => mk_sum (inl (mk_sum (inr (mk_pair (n, mk_ord x)))))
    | l_var i   => mk_sum (inr i)
  end.
Definition pl (p: positive): letter :=
  match get_sum p with
    | inl p => match get_sum p with
                 | inl p => let '(n,p) := get_pair p in 
                   match get_ord _ p with None => l_var 1 | Some x => l_pos n x end
                 | inr p => let '(n,p) := get_pair p in 
                   match get_ord _ p with None => l_var 1 | Some x => l_neg n x end
               end
    | inr i => l_var i
  end.
Lemma plp l: pl (lp l) = l. 
Proof. destruct l; unfold pl, lp; now rewrite !get_mk_sum, ?get_mk_pair, ?get_mk_ord. Qed.

(** the retraction into positives also equips [letter] with a
   [cmpType] structure *)
Definition compare_letter (a b: letter) := cmp (lp a) (lp b).
Lemma compare_letter_spec a b: compare_spec (a=b) (compare_letter a b). 
Proof.
  unfold compare_letter. case cmp_spec; intro E; constructor. 
  now rewrite <-(plp a), <-(plp b), E. congruence. congruence. 
Qed.
Canonical Structure cmp_letter := mk_simple_cmp _ compare_letter_spec.

(** typing extended letters: 
   - predicate letters come with their type
   - Kleene letters use the typing environment *)
Definition src' l := 
  match l with
    | l_pos n _ | l_neg n _ => n
    | l_var i => src i 
  end.

Definition tgt' l := 
  match l with
    | l_pos n _ | l_neg n _ => n
    | l_var i => tgt i 
  end.

(** ** regular expressions on the extended alphabet *)
 
(** [expr3] is intuitively the set of typed regular expressions on [letter],
   while [uexpr3] is the set of untyped regular expressions on [letter] 

   we use [uexpr3] rather than [regex] to use the untyping theorem
   (which we proved on generic expressions rather than regular
   expressions). 

   we now define several maps between these representations:
   - [o : gregex n m -> expr3 n m] (injective)
   - [o': expr3 n m -> gregex]     (partial, since expr3 has to many operations)
   - [v : expr3 n m -> regex]      (type-erasing, partial for the same reasons)
   - [w : regex -> uexpr3]         (injective, even if we do not prove it)
   - [u : expr3 n m -> uexpr3]     (type-erasing, actually [untyping.erase])
   
   and we prove the following properties:
   - [o'o = id]                 (yielding injectivity of [o])
   - [wvo = uo]                 (allowing us to use the untyping theorem)

*)
Notation expr3 n m := (expr_ops src' tgt' BKA n m).
Notation uexpr3 := (expr_ops (fun _ => xH) (fun _ => xH) BKA xH xH). 


(** ** [o: gregex n m -> expr3 n m] *)

Section n.
Variable n: positive.
Import lsyntax.
(** we need to push negation to leaves in Boolean expressions *)
Fixpoint o_pred (x: test): expr3 n n :=
  match x with
    | e_bot => 0
    | e_top => 1
    | e_cup x y => o_pred x + o_pred y
    | e_cap x y => o_pred x * o_pred y
    | e_neg x => o_npred x
    | e_var a => syntax.e_var (l_pos n a)
  end
with o_npred (x: test): expr3 n n :=
  match x with
    | e_bot => 1
    | e_top => 0
    | e_cup x y => o_npred x * o_npred y
    | e_cap x y => o_npred x + o_npred y
    | e_neg x => o_pred x
    | e_var a => syntax.e_var (l_neg n a)
  end.
Import syntax.
Lemma o_pred_level x: e_level (o_pred x) << BKA
  with o_npred_level x: e_level (o_npred x) << BKA. 
Proof.
  destruct x; simpl o_pred; simpl e_level; rewrite ?merge_spec; intuition. 
  destruct x; simpl o_npred; simpl e_level; rewrite ?merge_spec; intuition. 
Qed.
End n.

Fixpoint o n m (e: gregex n m): expr3 n m:=
  match e with
    | g_zer _ _ => 0
    | g_prd n p => o_pred n p
    | g_pls _ _ e f => o e + o f
    | g_dot _ _ _ e f => o e * o f
    | g_itr _ e => o e ^+
    | g_var j => e_var (l_var j)
  end.

Lemma o_sup n m I J (f: I -> gregex n m): o (sup f J) = \sup_(i\in J) (o (f i)).
Proof. apply f_sup_eq; now f_equal. Qed.

Lemma o_level n m (e: gregex n m): e_level (o e) << BKA. 
Proof.
  pose proof o_pred_level. 
  induction e; simpl o; simpl e_level; rewrite ?merge_spec; intuition. 
Qed.

(** ** [o': expr3 n m -> gregex n m] *)

Definition o': forall n m, expr3 n m -> gregex n m :=
  @eval _ src' tgt' (gregex_monoid_ops pred src tgt) id 
  (fun l => match l return gregex (src' l) (tgt' l) with
              | l_pos n p => g_prd _ _ (lsyntax.e_var p)
              | l_neg n p => g_prd _ _ (! lsyntax.e_var p)
              | l_var i => g_var i
            end).

Lemma o'o_pred: forall n (a: test), o' (o_pred n a) == g_prd _ _ a
 with o'o_npred: forall n (a: test), o' (o_npred n a) == g_prd _ _ (!a).
Proof.
  destruct a.
   symmetry. apply inj_bot. 
   symmetry. apply inj_top.
   setoid_rewrite inj_cup. apply cup_weq; apply o'o_pred. 
   setoid_rewrite inj_cap. apply dot_weq; apply o'o_pred. 
   apply o'o_npred. 
   reflexivity. 
  destruct a.
   symmetry. etransitivity. apply inj_weq. apply negbot. apply inj_top. 
   symmetry. etransitivity. apply inj_weq. apply negtop. apply inj_bot. 
   etransitivity. 2: apply inj_weq; symmetry; apply negcup. rewrite inj_cap.
    apply dot_weq; apply o'o_npred. 
   etransitivity. 2: apply inj_weq; symmetry; apply negcap. rewrite inj_cup.
    apply cup_weq; apply o'o_npred. 
   etransitivity. 2: apply inj_weq; symmetry; apply negneg. apply o'o_pred. 
   reflexivity. 
Qed.

(** [o] admits [o'] as left-inverse *)
Lemma o'o: forall n m (e: gregex n m), o' (o e) == e.
Proof.
  induction e; simpl o; simpl o'. 
   reflexivity. 
   apply o'o_pred.
   reflexivity. 
   now apply cup_weq. 
   now apply dot_weq. 
   now apply itr_weq.
Qed.

Lemma o'_weq n m: Proper (weq ==> weq) (@o' n m). 
Proof. intros ? ? H. apply (H (gregex_monoid_ops _ _ _) _ id). Qed.

(** so that [o] is injective *)
Corollary o_inj n m (e f: gregex n m): o e == o f -> e == f.
Proof. intro H. apply o'_weq in H. revert H. now rewrite 2o'o. Qed.


(** ** [expr3 -v-> regex -w-> uexpr3] *)

Definition v: forall n m, expr3 n m -> regex :=
  eval (f':=fun _ => regex_tt) (fun l => r_var (lp l)).

Definition w (e: regex): uexpr3 :=
  eval (X:=expr_ops _ _ BKA) (f':=fun _ => xH) (fun p => e_var (pl p)) (to_expr e).

Lemma wv_u n m (e: expr3 n m): e_level e << BKA -> w (v e) == erase BKA e.
Proof.
  unfold w.
  induction e; simpl e_level; intro Hl; try discriminate_levels;
    try (first [reflexivity|apply dot_weq|apply cup_weq|apply str_weq]);
      try (first [apply IHe1|apply IHe2|apply IHe]; solve_lower').
  symmetry. simpl (erase _ _). rewrite itr_str_l, <-IHe. reflexivity. solve_lower'.
  simpl. now rewrite plp.
Qed.

(** key lemma to be able to use the untyping theorem *)
Lemma wvo_uo n m (e: gregex n m): w (v (o e)) == erase BKA (o e).
Proof. apply wv_u, o_level. Qed. (* note: on doit pouvoir prouver une égalité forte *)

Lemma w_weq: Proper (weq ==> weq) w. 
Proof. intros ? ? H. apply (H (expr_ops _ _ _) _ (fun _ => xH)). Qed.

Lemma v_sup n m I J (f: I -> expr3 n m): v (sup f J) = \sup_(i\in J) (v (f i)).
Proof. apply f_sup_eq; now f_equal. Qed.



(** * From guarded string languages to languages on the extended alphabet *)
(** i.e., we define a coercion from [glang] [lang] *)

Notation word := (list positive).
Notation lang := (lang_ops positive lang_tt lang_tt).

(** converting an atom into a word of the extended alphabet. 
   this word has length [pred]: each predicate variable appears
   exactly once, with its assigned truth value *)
Definition atom_to_word n (a: Atom) := 
  map (fun i => if set.mem a i then lp (l_pos n i) else lp (l_neg n i)) (seq pred).

(** converting an guarded string into a word of the extended alphabet
   the resulting word has length [pred+(1+pred)*n], where [n] is the
   length of the guarded string *)
Fixpoint gword_to_word n (w: gword) :=
  match w with
    | tnil a => atom_to_word n a
    | tcons a i w => atom_to_word n a ++ lp (l_var i) :: gword_to_word (tgt i) w
  end.

(** we convert a guarded string language by converting its words *)
Definition gl n m (G: glang n m): lang :=
  fun w => exists g, w = gword_to_word n g /\ proj1_sig G g.


Instance gl_leq n m: Proper (leq ==> leq) (@gl n m).
Proof. intros G G' H w [t [? Hw]]. exists t. split. assumption. apply H, Hw. Qed.
Instance gl_weq n m: Proper (weq ==> weq) (@gl n m) := op_leq_weq_1.


(** auxiliary definition for the following auxiliary lemma:
   [gword_to_word' w] return the suffix of the word corresponding to
   [w], where the initial atom has been omitted *)
Definition gword_to_word' (w: gword) :=
  match w with
    | tnil a => []
    | tcons a i w => lp (l_var i) :: gword_to_word (tgt i) w
  end.

Lemma gword_to_word_cut n w: 
  gword_to_word n w = atom_to_word n (thead w) ++ gword_to_word' w.
Proof. destruct w. apply app_nil_end. reflexivity. Qed.

Lemma gword_tapp: forall x y z, tapp x y z -> 
  forall n, gword_to_word n z = gword_to_word n x ++ gword_to_word' y. 
Proof.
  induction 1; simpl; intros n. 
   apply app_nil_end.
   reflexivity. 
   now rewrite IHtapp, app_ass. 
Qed.




(** * 2. G (hat e) = R (hat e)

   (more formally, gl (G (hat e)) == R (v (o (hat e))))

  *)

Notation R := R.lang.
Notation G := G.lang.

Notation latom n a := (eq (atom_to_word n a): lang).


(** regular language corresponding to an atom *)

Lemma R_lang_atom n a: R (v (o (g_atom n a))) == latom n a.
Proof.
  simpl o. unfold atom, atom_to_word. 
  induction (seq pred). apply R.lang_1. simpl (sup _ _). 
  setoid_rewrite R.lang_dot. setoid_rewrite (eq_app_dot _ [_]). apply dot_weq. 
  case set.mem; apply R.lang_var. assumption. 
Qed.


(** ** properties of [gl]  *)

(** [gl] is a semilattice morphism (note that it does not preserve products/iterations) *)

Lemma gl_bot n m: @gl n m bot == bot.
Proof. split. intros [? [? []]]. intros []. Qed.

Lemma gl_cup n m (e f: glang n m): gl (e \cup f) == gl e \cup gl f.
Proof. 
  split. 
   intros [w [-> [H|H]]]; [left|right]; exists w; split; auto.
   intros [H|H]; destruct H as [w [-> H]]; exists w; split; trivial; (now left) || (now right).
Qed.

Lemma gl_sup n m I J (f: I -> glang n m): gl (sup f J) == \sup_(i\in J) gl (f i).
Proof. apply f_sup_weq. apply gl_bot. apply gl_cup. Qed.

(** [gl] maps atoms to atoms *)

Lemma gl_atom n a: gl (tatom n a) == latom n a.
Proof.
  intro w; split. 
  intros [g [-> <-]]. reflexivity. 
  intros <-. eexists. split. 2: reflexivity. reflexivity. 
Qed.

(** image of single letter traces under [gl] *)
Lemma gl_single' a i b:
  gl (tsingle' a i b) == 
  eq (atom_to_word (src i) a++[lp (l_var i)]++atom_to_word (tgt i) b).
Proof.
  intro w; split. 
  intros [g [-> <-]]. reflexivity. 
  intros <-. eexists. split. 2: reflexivity. reflexivity. 
Qed.

(** key auxiliary lemma for composition: we need to use an atom as a cutting point *)
Lemma gl_dot n m p (e: glang n m) a (f: glang m p) (e' f': lang): 
  gl (e * tatom m a) == e' * latom m a ->  
  gl (tatom m a * f) == latom m a * f' ->  
  gl (e * tatom m a * f) == e' * latom m a * f'.
Proof.
  setoid_rewrite weq_spec.
  intros He Hf. split; intro w.
  - apply proj1 in He. apply proj1 in Hf.
    intros [g [-> [xa [x Hx [? <- Hxa]] [y Hy Hg]]]].
    apply tapp_x_nil_eq in Hxa as [Ha ->].
    destruct (tapp_bounds Hg) as (H1&H2&H3). (* TOSIMPL *)
    destruct (He (gword_to_word n x)) as [x' Hx' [? <- Hxa']].
     repeat eexists; eauto. rewrite Ha. apply tapp_x_nil.
    destruct (Hf (gword_to_word m y)) as [? <- [y' Hy' Hay']].
     repeat eexists; eauto. rewrite Ha. rewrite H1. apply tapp_nil_x.
    repeat eexists; eauto.
    rewrite app_ass, <-Hay', (gword_to_word_cut m y), (gword_tapp Hg), <-app_ass.
    congruence.
  - apply proj2 in He. apply proj2 in Hf.
    intros [ea [x Hx [? <- ->]] [y Hy ->]].
    edestruct (He (x++atom_to_word m a)) as [xa [Hxa [x' Hx' [? <- Hxa']]]]. eexists; eauto.
    edestruct (Hf (atom_to_word m a++y)) as [ay [Hay [? <- [y' Hy' Hay']]]]. eexists; eauto.
    apply tapp_x_nil_eq in Hxa' as [-> ->].
    apply tapp_nil_x_eq in Hay' as [Ha ->].
    destruct (tapp_cat x' y' Ha) as [z Hz]. 
    repeat eexists; eauto. 2: apply tapp_x_nil.
    rewrite (gword_tapp Hz), <-Hxa, app_ass, Hay, gword_to_word_cut, ass_app.
    congruence.
Qed.

Lemma gl_nildot a n m (e: glang n m): exists e', gl (tatom n a * e) == latom n a * e'.
Proof.
  exists (fun w => exists g, proj1_sig e g /\ thead g = a /\ w = gword_to_word' g).
  rewrite weq_spec. split; intro w.
   intros [u [-> [? <- [v Hv H]]]]. apply tapp_nil_x_eq in H as [-> ->].
   repeat eexists; eauto. apply gword_to_word_cut.
   intros [? <- [u (x&He&<-&->) ->]].
   repeat eexists; eauto. apply eq_sym, gword_to_word_cut. apply tapp_nil_x.
Qed.

(** key auxiliary lemma for iteration: we need to use an atom as bounds *)
Lemma gl_itr n (e: glang n n) a (e': lang): 
  gl (tatom n a * e * tatom n a) == e' * latom n a ->  
  gl ((tatom n a * e)^+ * tatom n a) == e'^+ * latom n a.
Proof.
  rename n into m.
  intro H. rewrite <-itr_dot. apply antisym.
  - apply weq_spec in H as [H _]. intros w [g [-> [? <- [u [n Hn] Hg]]]].
    apply tapp_nil_x_eq in Hg as [Hu ->]. revert u Hu Hn. induction n; intros u Hu Hn.
    destruct Hn as [v Hv [? <- Hn]]. apply tapp_x_nil_eq in Hn as [Hn ->].
    destruct (H (gword_to_word m v)) as [u He [? <- H']].
     repeat eexists; eauto. rewrite Hu. apply tapp_nil_x. rewrite Hn. apply tapp_x_nil.
    exists u. now exists O. eauto.
    destruct Hn as [w [v Hv [? <- Hn]] [w' Hw' H']].
    apply tapp_x_nil_eq in Hn as [Hn ->].
    assert (H'' := tapp_bounds H'). (* TOSIMPL *)
    assert (Haw: a=thead w') by (rewrite Hn; intuition congruence).
    destruct (H (gword_to_word m v)) as [xe He [? <- Hxe]].
    repeat eexists; eauto.
     rewrite Hu, <-(tapp_head H'). apply tapp_nil_x.
     rewrite Hn; apply tapp_x_nil.
    assert (Hext: e' * (e'^+ * latom m a) <== e'^+ * latom m a).
     now rewrite dotA, itr_cons.
    apply Hext. clear Hext.
    eexists. eassumption. eexists. apply IHn. apply Haw. 
    assumption.
    rewrite (gword_tapp H'), Hxe, gword_to_word_cut, Haw, app_ass. congruence.
  - apply itr_ind_l.
    now rewrite <-H, <-itr_ext, dotA.
    rewrite <-itr_cons at 2.
    destruct (gl_nildot a ((e * tatom m a)^+)) as [f' Hf].
    rewrite 2dotA. rewrite gl_dot by eassumption.
    now rewrite Hf, dotA.
Qed.


(** ** clean terms: those on which [G] and [R] coincide *)

Definition clean1 n m (e: guard n m) := gl (G (geval e)) == R (v (o (geval e))).
Definition clean n m (e: guards n m) := forall g, In g e -> clean1 g.

Lemma G_clean n m (e: guards n m): clean e -> gl (G (teval e)) == R (v (o (teval e))).
Proof.
  intro He. rewrite o_sup, v_sup, lang_sup, R.lang_sup, gl_sup.
  apply sup_weq'. reflexivity. intros g Hg. apply He, Hg. 
Qed.

(** basic constructors for clean terms *)

Lemma clean_bot n m: @clean n m bot. 
Proof. intros _ []. Qed.

Lemma clean_cup n m (e f: guards n m): clean e -> clean f -> clean (e++f). 
Proof. unfold clean. setoid_rewrite in_app_iff. intuition. Qed.

Lemma clean_single n m (g: guard n m): clean1 g -> clean [g].
Proof. now intros ? ? [<-|[]]. Qed.

Lemma clean_sup n m I J (f: I -> guards n m): (forall i, In i J -> clean (f i)) -> clean (sup f J).
Proof. apply P_sup. apply clean_bot. apply clean_cup. Qed.

Lemma clean_map n m I J (f: I -> guard n m): (forall i, In i J -> clean1 (f i)) -> clean (map f J).
Proof. rewrite map_sup. intro. apply clean_sup. intros. apply clean_single. auto. Qed.


(** ** the basic ingredients of the [hat] function preserve cleaness  *)

Lemma clean_pred n a: clean1 (@g_pred n a). 
Proof. unfold clean1, geval. rewrite G.lang_atom, R_lang_atom. apply gl_atom. Qed.

Lemma clean_elem_var a i b: clean1 (g_elem a (g_var i) b).
Proof.
  unfold clean1, geval.
  rewrite 2G.lang_dot, 2G.lang_atom. 
  setoid_rewrite atom_single_atom. rewrite gl_single'. rewrite 2eq_app_dot. 
  do 2 setoid_rewrite R.lang_dot. rewrite R.lang_var.
  setoid_rewrite R_lang_atom. apply dotA.
Qed.

Lemma clean_dot' n m p (e: guards n m) (f: guards m p): clean e -> clean f -> clean (g_dot' e f). 
Proof.
  intros He Hf. apply clean_sup. intros x Hx. apply clean_sup. intros y Hy. 
  apply He in Hx. apply Hf in Hy. clear e f He Hf. 
  destruct x as [a|a e b]; destruct y as [c|c f d]; unfold g_dot1; 
    (case eqb_spec; [intros <-|intro E]); try apply clean_bot; apply clean_single; trivial.
  revert Hx Hy. unfold clean1, geval. rewrite 8G.lang_dot, 3G.lang_atom.
  simpl o; simpl v. fold_regex. rewrite 8R.lang_dot. setoid_rewrite R_lang_atom. 
  intros Hx Hy. rewrite 4dotA, <-dotA, <-(dotA _ _ (latom _ _)). 
  apply gl_dot. assumption. rewrite 2dotA. assumption. 
Qed.

Lemma clean_one' n: clean (g_one' n).
Proof. apply clean_map. intros. apply clean_pred. Qed.

Lemma clean_inner_dot n m (e: guard n m) (He: clean1 e):
  forall p (f: guard m p), clean1 f -> 
   gl (tatom n (fst e) * G (g_inner_dot e f) * tatom p (fst e)) ==
   latom n (fst e) * R (v (o (g_inner_dot e f))) * latom p (fst e).
Proof.
  assert (Z: forall n m p q (e: glang n m) (f: glang p q) e' f', gl (e*G 0*f) == e'*R 0*f').
   intros. rewrite G.lang_0, dotx0, dot0x, gl_bot. setoid_rewrite R.lang_0. ra. 
  destruct e as [n a|n m a e b]; destruct f as [p c|p q c f d]; intros Hf;
    simpl fst; simpl lst; simpl g_inner_dot.
  - apply Z. 
  - case eqb_spec. intros <-. 2: intros; apply Z. 
    case eqb_spec. intros <-. 2: intros; apply Z. 
    unfold andb. unfold clean1, geval in Hf. 
    rewrite 2G.lang_dot, 2G.lang_atom in Hf. rewrite Hf. 
    rewrite <-2R_lang_atom, <-2R.lang_dot. reflexivity. 
  - case eqb_spec. intros <-. 2: intros; apply Z. 
    case eqb_spec. intros <-. 2: intros; apply Z. 
    unfold andb. unfold clean1, geval in He. 
    rewrite 2G.lang_dot, 2G.lang_atom in He. rewrite He. 
    rewrite <-2R_lang_atom, <-2R.lang_dot. reflexivity. 
  - case eqb_spec. intros <-. 2: intros; apply Z. 
    case eqb_spec. intros <-. 2: intros; apply Z. 
    unfold andb. 
    unfold clean1, geval in He. rewrite 2G.lang_dot, 2G.lang_atom in He. 
    unfold clean1, geval in Hf. rewrite 2G.lang_dot, 2G.lang_atom in Hf. 
    simpl o in *; simpl v in *. 
    rewrite 2R.lang_dot in He. setoid_rewrite R_lang_atom in He. 
    rewrite 2R.lang_dot in Hf. setoid_rewrite R_lang_atom in Hf. 
    rewrite 2R.lang_dot. setoid_rewrite R_lang_atom. 
    setoid_rewrite G.lang_dot. rewrite dotA. setoid_rewrite G.lang_dot. 
    rewrite G.lang_atom. 
    rewrite dotA. rewrite <-(dotA _ (G f)). 
    rewrite <-2dotA in Hf. 
    rewrite gl_dot by eassumption. ra. 
Qed.  

Lemma clean_str' n (e: guards n n): clean e -> clean (g_str' e). 
Proof.
  induction e; intro Hae; simpl g_str'. apply clean_one'.
  assert (He: clean e) by (intros ? ?; apply Hae; now right). specialize (IHe He). 
  assert (Ha: clean1 a) by (apply Hae; now left). clear Hae. 
  apply clean_cup. assumption.
  apply clean_dot'. assumption. 
  apply clean_dot'. apply clean_cup. 2: apply clean_one'. 
  2: apply clean_dot'; [now apply clean_single | assumption]. 
  revert IHe. generalize (g_str' e). clear e He. intros e He. 
  apply clean_single. unfold clean1. unfold geval. simpl o; simpl v; fold_regex. 
  rewrite 2dotA, <-str_itr, <-2itr_str_l. 
  rewrite G.lang_dot, G.lang_itr, G.lang_dot, G.lang_sup, G.lang_atom.
  rewrite R.lang_dot, R.lang_itr, R.lang_dot, o_sup, v_sup, R.lang_sup.
  setoid_rewrite R_lang_atom. 
  apply gl_itr. rewrite 2dotxsum, 2dotsumx, gl_sup. 
  apply sup_weq'. reflexivity. intros f Hf. 
  apply clean_inner_dot. apply Ha. apply He, Hf. 
Qed.

(** ** the [hat] function produces clean terms *)

Theorem clean_hat n m (e: gregex n m): clean (hat e).
Proof.
  induction e; simpl hat. 
   apply clean_bot. 
   apply clean_map. intros ? _. apply clean_pred. 
   apply clean_sup. intros ? _. apply clean_sup. intros ? _. apply clean_single, clean_elem_var.
   now apply clean_cup. 
   now apply clean_dot'. 
   apply clean_dot'. assumption. apply clean_str'. assumption. 
Qed.

(** whence the desired property, as a corollary *)

Corollary G_hat n m (e: gregex n m): gl (G e) == R (v (o (teval (hat e)))).
Proof. rewrite <-(teval_hat e) at 1. apply G_clean, clean_hat. Qed.

(** * KAT completeness *)

(** we assemble all the pieces as explained at the beginning of this file *)
Theorem kat_complete_weq n m: forall e f: gregex n m, G e == G f -> e == f.
Proof.
  intros e f H.
  apply gl_weq in H. 
  rewrite 2G_hat in H. 
  apply ka_complete_weq in H.
  apply w_weq in H. 
  rewrite 2wvo_uo in H. 
  apply erase_faithful_weq in H. 
   2: now rewrite 2o_level. 
   2: reflexivity. 
  apply o_inj in H. 
  rewrite 2teval_hat in H. 
  assumption.
Qed.

(** we deduce a similar result for language inclusions *)
Corollary kat_complete_leq n m: forall e f: gregex n m, G e <== G f -> e <== f.
Proof. intros e f. rewrite 2leq_iff_cup, <-G.lang_pls. apply kat_complete_weq. Qed.

(** and the above implications actually are equivalences *)
Corollary kat_correct_complete_weq n m: forall e f: gregex n m, G e == G f <-> e == f.
Proof. split. apply kat_complete_weq. apply G.lang_weq. Qed.

Corollary kat_correct_complete_leq n m: forall e f: gregex n m, G e <== G f <-> e <== f.
Proof. split. apply kat_complete_leq. apply G.lang_leq. Qed.

(** * KAT decidability  *)

(** additional corollaries (not used): 
   - KAT proofs reduce to KA proofs 
   - KAT equality is decidable *)

Corollary kat_reduces_to_ka n m: forall e f: gregex n m, 
  e==f <-> v (o (teval (hat e))) == v (o (teval (hat f))).
Proof.
   intros. split; intro H. 
    apply ka_complete_weq. now rewrite <-2G_hat, H.
    apply w_weq in H. 
    rewrite 2wvo_uo in H. 
    apply erase_faithful_weq in H. 
     2: now rewrite 2o_level. 
     2: reflexivity. 
    apply o_inj in H. 
    now rewrite 2teval_hat in H. 
Qed.

Corollary kat_dec n m: forall e f: gregex n m, {e==f} + {~(e==f)}.
Proof. intros. eapply sumbool_iff. symmetry. apply kat_reduces_to_ka. apply ka_weq_dec. Qed.

End s.
