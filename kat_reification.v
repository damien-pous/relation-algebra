(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * kat_reification: various definitions to ease the KAT reification process *)

(** We reify KAT terms as [syntax.expr] trees over an alphabet
   including [lsyntax.expr] for Boolean tests. This allows us to reuse
   the tools developped for ra_{normalise,reflexivity}, and this gives
   us more flexibility

   Here define the conversion function from this syntax to [gregex],
   as well as dependently typed positive maps to ease the definition
   of the environment for predicate variables *)

Require Import lsyntax ordinal lset.
Require Export positives kat gregex syntax.

Section s.
Notation Idx := positive.       (* type indices *)
Notation Sigma := positive.     (* Kleene variable indices *)
Notation Pred := positive.      (* predicate variables indices *)

Context {X: kat.ops}.

(** * Dependently types positive maps *)

(** we use dependently typed binary trees:
   [v f'] is used to repredent dependent functions of 
   type [forall n, Pred -> tst (f' n)] *)
Inductive v: (Idx -> ob X) -> Type :=
| v_L: forall f', v f'
| v_N: forall f', 
  v (fun n => f' (xO n)) -> 
  (Pred -> tst (f' xH)) -> 
  v (fun n => f' (xI n)) -> v f'.

(** [v_get] transforms such a tree into the corresponding function, 
   using [lattice.top] to fill the gaps *)
Fixpoint v_get f' (t: v f') n p: tst (f' n) :=
  match t with
    | v_L _ => lattice.top
    | v_N _ l m r => 
      match n with
        | xO n => v_get _ l n p
        | xI n => v_get _ r n p
        | xH => m p
      end
  end.

(** [v_add f' t n x] adds the binding [(n,x)] to [t] *)
Fixpoint v_add f' (t: v f') n: (Pred -> tst (f' n)) -> v f' :=
  match t with
    | v_L f' => 
        match n with
        | xH => fun x => v_N _ (v_L _) x (v_L _)
        | xO n => fun x => v_N _ 
          (v_add (fun n => f' (xO n)) (v_L _) n x) (fun _ => lattice.top) (v_L _)
        | xI n => fun x => v_N _ 
          (v_L _) (fun _ => lattice.top) (v_add (fun n => f' (xI n)) (v_L _) n x)
        end
    | v_N f' l y r => 
        match n with
        | xH => fun x => v_N _ l x r
        | xO n => fun x => v_N _ (v_add (fun n => f' (xO n)) l n x) y r
        | xI n => fun x => v_N _ l y (v_add (fun n => f' (xI n)) r n x)
        end
    end.


(** * Syntax of KAT reification *)

(** we use packages for Kleene variables, as for [ra_refication]  *)
Context {f': Idx -> ob X} {fs: Sigma -> Pack X f'}.

(** reified KAT expressions are just generic expressions
   ([syntax.expr]) over the following alphabet, which includes
   [lsyntax.expr] for Boolean expressions. The index type of the
   Boolean expressions is declared only once, at the [e_var] nodes
   switching from [syntax.expr] to [lsyntax.expr] *)
Definition var := (Sigma + Idx * lsyntax.expr Pred)%type.

(** typing functions for this alphabet: use the packages for Kleene
   variables, and the declared type for Boolean expressions *)
Definition s' (a: var) := match a with inl a => src_ fs a | inr (n,_) => n end.
Definition t' (a: var) := match a with inl a => tgt_ fs a | inr (n,_) => n end.

(** final type of reified KAT expressions *)
Definition kat_expr := expr s' t'.

(** additional constructors:
   - [e_inj n p] injects a Boolean expression [p], at type [n]
   - [e_var i] produces a Kleene variable
   - [p_var a] produces a predicat variable
   *)
Definition e_inj n p: kat_expr n n := e_var (inr (n,p)).
Definition e_var i: kat_expr (src_ fs i) (tgt_ fs i) := e_var (inl i).
Definition p_var := @lsyntax.e_var Pred.

Section e.

(** * Interpretation of KAT reified expressions *)

(** we use the interpretations functions [syntax.expr] and
   [lsyntax.expr], with the appropriate substitutions *)

Variable fp: forall n, Pred -> tst (f' n).

Definition eval: forall n m, kat_expr n m -> X (f' n) (f' m) :=
  syntax.eval (fun a => 
    match a return X (f' (s' a)) (f' (t' a)) with 
      | inl a => val (fs a)
      | inr (n,p) => inj (lsyntax.eval (fp n) p)
    end).

End e.

(** * Predicate variables of a KAT expression *)
Fixpoint vars {n m} (e: kat_expr n m): list Pred :=
  match e with
    | e_zer _ _ 
    | e_top _ _ 
    | e_one _ => []
    | e_pls x y 
    | e_cap x y 
    | e_ldv x y 
    | e_rdv x y 
    | e_dot x y => union (vars x) (vars y)
    | e_neg x 
    | e_itr x 
    | e_str x 
    | e_cnv x => vars x
    | syntax.e_var (inr (_,x)) => lsyntax.vars x
    | syntax.e_var _ => []
  end.

(** index of an element in a list, as an ordinal.
   Together with the list of all predicate variables indices appearing in a
   reified term, this function will allow us to convert positive
   indices to ordinal ones, as required byb [gregex]. *)
Fixpoint idx (x: Pred) (l: list Pred): option (ord (length l)) :=
  match l with 
    | [] => None
    | y::q => 
      if eqb_pos x y then Some ord0 else 
      match idx x q with Some i => Some (ordS i) | None => None end
  end.

(** * From reified KAT expressions to [gregex] *)

(** we interpret the expression in the [gregex] model, 
   mapping all Boolean expressions with positives variables 
   to their counterpart with ordinal variables *)
Definition to_gregex (l: list positive):
  forall n m, kat_expr n m -> gregex (length l) (src_ fs) (tgt_ fs) n m :=
    syntax.eval (fun a => 
      match a return gregex _ (src_ fs) (tgt_ fs) (s' a) (t' a) with 
        | inl a => g_var a
        | inr (n,p) => g_prd _ _ 
          (* here we just map all predicate variable indices 
             into their ordinal counterpart *)
          (lsyntax.eval (fun x => 
            match idx x l with
              | Some i => lsyntax.e_var i
              | None => lsyntax.e_top: lsyntax.expr_ BL
            end) p)
      end).

(** correctness of the [idx] function *)
Lemma in_idx x l: In x l -> exists j, idx x l = Some j /\ nth j l xH = x.
Proof.
  induction l. intros []. intro Hl. simpl idx. case eqb_spec.
  intros <-. exists ord0. now split. 
  destruct Hl as [<-|Hl]. congruence. 
  intros _. apply IHl in Hl as [j [-> Hj]]. exists (ordS j). split. reflexivity. 
  destruct j. assumption. 
Qed.

(** factorisation of the interpretation function, through [gregex]

   since the type of expressions is slightly to big (it contains
   residuals and converse, for instance), we have to check that the
   expression does not use such constructions, whence the first
   hypothesis. *)
Lemma to_gregex_eval {L: laws X} v n m e fp: e_level e << BKA -> vars e <== v -> 
  eval fp n m e ==
  gregex.eval f' (fun n i => fp n (nth i v xH)) (fun i => val (fs i)) (to_gregex v n m e).
Proof.
  induction e; simpl e_level; simpl (vars _); intros Hl Hv;
    try discriminate_levels; simpl; rewrite ?union_app in Hv. 
   reflexivity.
   symmetry. apply kat.inj_top.
   apply cup_weq. 
    apply IHe1. solve_lower'. rewrite <- Hv. lattice.
    apply IHe2. solve_lower'. rewrite <- Hv. lattice.
   apply dot_weq. 
    apply IHe1. solve_lower'. rewrite <- Hv. lattice.
    apply IHe2. solve_lower'. rewrite <- Hv. lattice.
   apply itr_weq, IHe. solve_lower'. assumption. 
   rewrite kat.inj_top, <-str_itr. apply str_weq, IHe. solve_lower'. assumption. 
   destruct a as [a|[n p]]. reflexivity. 
   simpl. apply kat.inj_weq. clear Hl. 
   induction p; simpl; simpl (lsyntax.vars _) in Hv; rewrite ?union_app in Hv. 
    reflexivity. 
    reflexivity. 
    apply cup_weq.
     apply IHp1. rewrite <-Hv. lattice.
     apply IHp2. rewrite <-Hv. lattice.
    apply cap_weq.
     apply IHp1. rewrite <-Hv. lattice.
     apply IHp2. rewrite <-Hv. lattice.
    apply neg_weq, IHp. assumption. 
    simpl. destruct (in_idx a v) as [j [-> Hj]]. apply Hv; now left. 
    simpl. now rewrite Hj. 
Qed.

(** as a corollary, we get the reification lemma 
   (The hypothesis that expressions do not use forbidden symbols will be easily
   checked by reflection, dynamically.) *)

Corollary to_gregex_weq {L: laws X} n m e f fp: 
  e_level e + e_level f << BKA ->
  (let v := vars (e_pls e f) in to_gregex v n m e == to_gregex v n m f) -> 
  eval fp n m e == eval fp n m f.
Proof.
  intros Hl H. rewrite 2(to_gregex_eval (vars (e_pls e f))) 
    by (solve_lower' || simpl (vars _); rewrite union_app; lattice). 
   apply H, L. 
Qed.

End s.

Arguments e_inj _ _ _ _%positive _%last.
Arguments e_var _ _ _ _%positive.
Arguments p_var _%positive.

(** Load ML reification modules *)

Declare ML Module "ra_common". 
Declare ML Module "kat_reification". 
