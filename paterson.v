(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2013: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)


(** * paterson: Equivalence of two flowchart schemes, due to Paterson
   cf. "Mathematical theory of computation", Manna, 1974 
   cf. "Kleene algebra with tests and program schematology", A. Angus and D. Kozen, 2001
*)

Require Import kat normalisation rewriting move kat_tac comparisons rel.
Set Implicit Arguments.

Unset Injection On Proofs.

(** * Memory model  *)

(** we need only five memory locations: the [y_i] are temporary
   variables and [io] is used for input and output *)
Inductive loc := y1 | y2 | y3 | y4 | io.
Record state := { v1: nat; v2: nat; v3: nat; v4: nat; vio: nat }.

(** getting the content of a memory cell *)
Definition get x := match x with y1 => v1 | y2 => v2 | y3 => v3 | y4 => v4 | io => vio end.

(** setting the content of a memory cell *)
Definition set x n m := 
  match x with
    | y1 => {| v1:=n; v2:=v2 m; v3:=v3 m; v4:=v4 m; vio:=vio m |}
    | y2 => {| v1:=v1 m; v2:=n; v3:=v3 m; v4:=v4 m; vio:=vio m |}
    | y3 => {| v1:=v1 m; v2:=v2 m; v3:=n; v4:=v4 m; vio:=vio m |}
    | y4 => {| v1:=v1 m; v2:=v2 m; v3:=v3 m; v4:=n; vio:=vio m |}
    | io => {| v1:=v1 m; v2:=v2 m; v3:=v3 m; v4:=v4 m; vio:=n |}
  end.

(** basic properties of [get] and [set] *)
Lemma get_set x v m: get x (set x v m) = v. 
Proof. now destruct x. Qed.

Lemma get_set' x y v m: x<>y -> get x (set y v m) = get x m. 
Proof. destruct y; destruct x; simpl; trivial; congruence. Qed.

Lemma set_set x v v' m: set x v (set x v' m) = set x v m.
Proof. now destruct x. Qed.

Lemma set_set' x y v v' m: x<>y -> set x v (set y v' m) = set y v' (set x v m).
Proof. destruct y; destruct x; simpl; trivial; congruence. Qed.

(** comparing locations *)
Definition eqb x y :=
  match x,y with
    | y1,y1 | y2,y2 | y3,y3 | y4,y4 | io,io => true
    | _,_ => false
  end.
Lemma eqb_spec: forall x y, reflect (x=y) (eqb x y).
Proof. destruct x; destruct y; simpl; try constructor; congruence. Qed.
Lemma eqb_false x y: x<>y -> eqb x y = false.
Proof. case eqb_spec; congruence. Qed.
Lemma neqb_spec x y: negb (eqb x y) <-> x<>y.
Proof. case eqb_spec; intuition; congruence. Qed.


(** * Arithmetic and Boolean expressions *)

Section s.

(** we assume arbitrary functions to interpret symbols [f], [g], and [p]  *)
Variable ff: nat -> nat.
Variable gg: nat -> nat -> nat. 
Variable pp: nat -> bool. 

(** we use a single inductive to represent Arithmetic and Boolean
   expressions: this allows us to share code about evaluation, free
   variables and so on, through polymorphism *)
Inductive expr: Set -> Set :=
  | e_var: loc -> expr nat
  | O: expr nat
  | f': expr nat -> expr nat
  | g': expr nat -> expr nat -> expr nat
  | p': expr nat -> expr bool
  | e_cap: expr bool -> expr bool -> expr bool
  | e_cup: expr bool -> expr bool -> expr bool
  | e_neg: expr bool -> expr bool
  | e_bot: expr bool
  | e_top: expr bool.

Coercion e_var: loc >-> expr.

(** ** evaluation of expressions  *)
Fixpoint eval A (e: expr A) (m: state): A :=
  match e with
    | e_var x => get x m
    | O => 0%nat
    | f' e => ff (eval e m)
    | g' e f => gg (eval e m) (eval f m)
    | p' e => pp (eval e m)
    | e_cap e f => eval e m &&& eval f m
    | e_cup e f => eval e m ||| eval f m
    | e_neg e => negb (eval e m)
    | e_bot => false
    | e_top => true
  end.


(** ** Free variables *)

Fixpoint free y A (e: expr A): bool :=
  match e with
    | e_var x => negb (eqb x y)
    | f' e | p' e | e_neg e => free y e
    | g' e f | e_cap e f | e_cup e f => free y e &&& free y f
    | _ => true
  end.

(** ** Substitution *)

Fixpoint subst x v A (f: expr A): expr A :=  
  match f with
    | e_var y => if eqb x y then v else e_var y
    | O => O
    | f' e => f' (subst x v e)
    | p' e => p' (subst x v e)
    | g' e f => g' (subst x v e) (subst x v f)
    | e_cup e f => e_cup (subst x v e) (subst x v f)
    | e_cap e f => e_cap (subst x v e) (subst x v f)
    | e_neg e => e_neg (subst x v e)
    | e_bot => e_bot
    | e_top => e_top
  end.

Lemma subst_free x v A (e: expr A): free x e -> subst x v e = e.
Proof.
  induction e; simpl; trivial. 
   rewrite neqb_spec. case eqb_spec; congruence.
   intro. now rewrite IHe. 
   rewrite landb_spec. intros [? ?]. now rewrite IHe1, IHe2. 
   intro. now rewrite IHe. 
   rewrite landb_spec. intros [? ?]. now rewrite IHe1, IHe2. 
   rewrite landb_spec. intros [? ?]. now rewrite IHe1, IHe2. 
   intro. now rewrite IHe. 
Qed.

Lemma free_subst x e A (f: expr A): free x e -> free x (subst x e f).
Proof.
  intro. induction f; simpl; rewrite ?IHf1; auto. 
  case eqb_spec; trivial. simpl. rewrite neqb_spec. congruence.
Qed.


(** * Programs *)
(** We just use KAT expressions, since any gflowchat scheme can be encoded as such an expression *)
Inductive prog :=
| p_tst(t: expr bool)
| p_aff(x: loc)(e: expr nat)
| p_str(p: prog)
| p_dot(p q: prog)
| p_pls(p q: prog).


(** * Bigstep semantics *)

(** updating the memory, according to the assignment [x<-e] *)
Definition update x e m := set x (eval e m) m.
(** relational counterpart of this function *)
Notation upd x e := (frel (update x e)).

(** Bigstep semantics, as a fixpoint *)
Fixpoint bstep (p: prog): rel state state :=
  match p with
    | p_tst p => [eval p: dset state]
    | p_aff x e => upd x e
    | p_str p => bstep p ^*
    | p_dot p q => bstep p * bstep q
    | p_pls p q => bstep p + bstep q
  end.

(** auxiliary lemma relating the evaluation of expressions, the
   assignments to the memory, and subsitution of expressions *)
Lemma eval_update x v A (e: expr A) m: eval e (update x v m) = eval (subst x v e) m.
Proof.
  induction e; simpl; try congruence. 
   unfold update. case eqb_spec. intros <-. apply get_set. 
   intro. apply get_set'. congruence.
  now rewrite IHe1, IHe2. 
  now rewrite IHe1, IHe2. 
Qed.


(** Now we make the set of programs a Kleene algebra with tests: we
   declare canonical structures for Boolean expressions (tests),
   programs (Kleene elements), and the natural injection of the former
   into the latter *)

Canonical Structure expr_lattice_ops: lattice.ops := {|
  car := expr bool;
  leq := fun x y => eval x <== eval y;
  weq := fun x y => eval x == eval y;
  cup := e_cup;
  cap := e_cap;
  bot := e_bot;
  top := e_top;
  neg := e_neg
|}.

Canonical Structure prog_lattice_ops: lattice.ops := {|
  car := prog;
  leq := fun x y => bstep x <== bstep y;
  weq := fun x y => bstep x == bstep y;
  cup := p_pls;
  cap := assert_false p_pls;
  bot := p_tst e_bot;
  top := assert_false (p_tst e_bot);
  neg := assert_false id
|}.

Canonical Structure prog_monoid_ops: monoid.ops := {|
  ob  := unit;
  mor n m := prog_lattice_ops;
  dot n m p := p_dot;
  one n := p_tst e_top;
  itr n := (fun x => p_dot x (p_str x));
  str n := p_str;
  cnv n m := assert_false id;
  ldv n m p := assert_false (fun _ => id);
  rdv n m p := assert_false (fun _ => id)
|}.

Canonical Structure prog_kat_ops: kat.ops := {|
  kar := prog_monoid_ops;
  tst n := expr_lattice_ops;
  inj n := p_tst
|}.

Notation prog' := (prog_kat_ops tt tt).
Notation test := (@tst prog_kat_ops tt).

(** proving that the laws of KAT are satisfied is almost trivial,
   since the model faithfully embeds in the relational model *)

Instance expr_lattice_laws: lattice.laws BL expr_lattice_ops. 
Proof.
  apply laws_of_injective_morphism with (@eval bool: expr bool -> dset state); trivial. 
  split; simpl; tauto.
Qed.

Instance prog_monoid_laws: monoid.laws BKA prog_monoid_ops. 
Proof. 
  apply laws_of_faithful_functor with (fun _ => state) (fun _ _: unit => bstep); trivial.
  split; simpl; try discriminate; try tauto. 2: firstorder. 
  split; simpl; try discriminate; try tauto. firstorder. 
Qed.
Instance prog_lattice_laws: lattice.laws BKA prog_lattice_ops := lattice_laws tt tt. 

Instance prog_kat_laws: kat.laws prog_kat_ops. 
Proof.
  constructor; simpl; eauto with typeclass_instances. 2: tauto. 
  split; try discriminate; try (simpl; tauto).
  intros x y H. apply inj_leq. intro m. apply H.
  intros x y H. apply inj_weq. intro m. apply H.
  intros _ x y. apply (inj_cup (X:=rel_kat_ops)).
  intros _ x y. apply (inj_cap (X:=rel_kat_ops)).
Qed.

(** ** variables read by a program *)

(** [dont_read y p] holds if [p] never reads [y] *)
Fixpoint dont_read y (p: prog'): bool :=
  match p with
    | p_str p => dont_read y p
    | p_dot p q | p_pls p q => dont_read y p &&& dont_read y q
    | p_aff x e => free y e
    | p_tst t => free y t
  end.



(** ** Additional notation  *)

Infix " ;" := (dot _ _ _) (left associativity, at level 40): ra_terms. 
Definition aff x e: prog' := p_aff x e.
Notation "x <- e" := (aff x e) (at level 30).
Notation del y := (y<-O).


(** * Laws of schematic KAT *)

Arguments rel_monoid_ops : simpl never.
Arguments rel_lattice_ops : simpl never. 

(** (the numbering corresponds to Angus and Kozen's paper)  *)
Lemma eq_6 (x y: loc) (s t: expr nat): 
  negb (eqb x y) &&& free y s -> x<-s;y<-t == y<-subst x s t; x<-s. 
Proof.
  rewrite landb_spec, neqb_spec. intros [D H]. cbn. 
  rewrite 2frel_comp. apply frel_weq. intro m. 
  unfold update at 1 2 3. rewrite set_set' by congruence. f_equal.  
  now rewrite eval_update, subst_free.
  unfold update. now rewrite <-eval_update.
Qed.

Lemma eq_7 (x y: loc) (s t: expr nat): 
  negb (eqb x y) &&& free x s -> x<-s;y<-t == x<-s;y<-subst x s t. 
Proof.
  rewrite landb_spec, neqb_spec. intros [D H]. cbn. 
  rewrite 2frel_comp. apply frel_weq. intro m. 
  unfold update at 1 3. f_equal.  
  rewrite 2eval_update. symmetry. rewrite subst_free. reflexivity. 
  now apply free_subst.
Qed.

Lemma eq_8 (x: loc) (s t: expr nat): x<-s;x<-t == x<-subst x s t. 
Proof.
  cbn. rewrite frel_comp. apply frel_weq. intro m. 
  unfold update. rewrite set_set. f_equal. apply eval_update. 
Qed.

Lemma eq_9 (x: loc) (t: expr nat) (phi: test): [subst x t phi: test];x<-t == x<-t;[phi].
Proof.
  Transparent rel_lattice_ops. intros m m'. split. Opaque rel_lattice_ops. 
   intros [m0 [<- H] ->]. eexists. reflexivity. split; trivial. now rewrite eval_update.
   intros [m0 -> [<- H]]. eexists. 2: reflexivity. split; trivial. now rewrite <-eval_update.
Qed.


Lemma eq_6' (x y: loc) (s t: expr nat): free x t &&& negb (eqb x y) &&& free y s -> 
  x<-s;y<-t == y<-t; x<-s. 
Proof. rewrite landb_spec. intros [? ?]. now rewrite eq_6, subst_free. Qed.

Lemma eq_9' (x: loc) (t: expr nat) (phi: test): free x phi -> [phi];x<-t == x<-t;[phi].
Proof. intro. now rewrite <-eq_9, subst_free. Qed.

Transparent rel_lattice_ops.
Arguments rel_lattice_ops : simpl never.

Lemma same_value (f: state -> state) (p: prog') (a b: test):
  bstep p == frel f -> (forall m, eval a (f m) = eval b (f m)) -> 
  p;[a\cap !b \cup !a\cap b] <== 0.
Proof.
  intros Hp H. cbn. rewrite Hp. 
   intros m m' [? -> [<- E]]. 
  exfalso. rewrite lorb_spec, 2landb_spec, 2negb_spec, H in E. intuition congruence.
Qed.


(** * Garbage-collecting assignments to unread variables *)

(** (i.e., Lemma 4.5 in Angus and Kozen's paper)  *)
Fixpoint gc y (p: prog'): prog' :=
  match p with
    | p_str p => gc y p^*
    | p_tst _ => p
    | p_aff x e => if eqb x y then 1 else x<-e
    | p_dot p q => gc y p ; gc y q
    | p_pls p q => gc y p + gc y q
  end.

Arguments prog_monoid_ops : simpl never.
Arguments prog_lattice_ops : simpl never.
Arguments prog_kat_ops : simpl never.

Lemma gc_correct y p: dont_read y p -> gc y p; del y == p; del y.
Proof.
  intro H. transitivity (del y; gc y p).
  induction p; cbn. 
   now apply eq_9'.
   case eqb_spec. ra. intro. apply eq_6'. now rewrite eqb_false. 
   symmetry. apply str_move. symmetry. now auto. 
   apply landb_spec in H as [? ?]. mrewrite IHp2. 2: assumption. now mrewrite IHp1.  
   apply landb_spec in H as [? ?]. ra_normalise. now apply cup_weq; auto. 
  symmetry. induction p; cbn. 
   now apply eq_9'.
   case eqb_spec. intros <-. rewrite eq_8. ra. intro D. apply eq_6'. now rewrite eqb_false. 
   symmetry. apply str_move. symmetry. now auto. 
   apply landb_spec in H as [? ?]. mrewrite IHp2. 2: assumption. now mrewrite IHp1.  
   apply landb_spec in H as [? ?]. ra_normalise. now apply cup_weq; auto. 
Qed.   


Ltac solve_rmov ::=
  first 
    [ eassumption 
    | symmetry; eassumption
    | eapply rmov_x_dot
    | apply rmov_x_pls
    | apply rmov_x_str
    | apply rmov_x_itr
    | apply rmov_x_cap
    | apply rmov_x_cup
    | apply rmov_x_neg
    | apply rmov_inj
    | apply rmov_x_1
    | apply rmov_x_0 ]; 
    match goal with |- ?x == ?y => solve_rmov end.
  
(** * Paterson's equivalence *)
Theorem Paterson: 
  let a1 := p' y1: test in
  let a2 := p' y2: test in
  let a3 := p' y3: test in
  let a4 := p' y4: test in
  let clr := del y1; del y2; del y3; del y4 in
  let x1 := y1<-io in
  let s1 := y1<-f' io in
  let s2 := y2<-f' io in
  let z1 := io<-y1; clr in
  let z2 := io<-y2; clr in
  let p11 := y1<-f' y1 in
  let p13 := y1<-f' y3 in
  let p22 := y2<-f' y2 in
  let p41 := y4<-f' y1 in
  let q222 := y2<-g' y2 y2 in
  let q214 := y2<-g' y1 y4 in
  let q211 := y2<-g' y1 y1 in
  let q311 := y3<-g' y1 y1 in
  let r11 := y1<-f' (f' y1) in
  let r12 := y1<-f' (f' y2) in
  let r13 := y1<-f' (f' y3) in
  let r22 := y2<-f' (f' y2) in
  let rhs := s2;[a2];q222;([!a2];r22;[a2];q222)^*;[a2];z2 in
  x1;p41;p11;q214;q311;([!a1];p11;q214;q311)^*;[a1];p13;
  (([!a4]+[a4];([!a2];p22)^*;[a2\cap !a3];p41;p11);q214;q311;([!a1];p11;q214;q311)^*;[a1];p13)^*;
  [a4];([!a2];p22)^*;[a2\cap a3];z2  ==  rhs.
Proof.
  intros.
  (** simple commutation hypotheses, to be exploited by [hkat] *)
  assert (a1p22:  [a1];p22  == p22;[a1])  by now apply eq_9'. 
  assert (a1q214: [a1];q214 == q214;[a1]) by now apply eq_9'. 
  assert (a1q211: [a1];q211 == q211;[a1]) by now apply eq_9'. 
  assert (a1q311: [a1];q311 == q311;[a1]) by now apply eq_9'. 
  assert (a2p13:  [a2];p13  == p13;[a2])  by now apply eq_9'. 
  assert (a2r12:  [a2];r12  == r12;[a2])  by now apply eq_9'. 
  assert (a2r13:  [a2];r13  == r13;[a2])  by now apply eq_9'. 
  assert (a3p13:  [a3];p13  == p13;[a3])  by now apply eq_9'. 
  assert (a3p22:  [a3];p22  == p22;[a3])  by now apply eq_9'. 
  assert (a3r12:  [a3];r12  == r12;[a3])  by now apply eq_9'. 
  assert (a3r13:  [a3];r13  == r13;[a3])  by now apply eq_9'. 
  assert (a4p13:  [a4];p13  == p13;[a4])  by now apply eq_9'. 
  assert (a4p11:  [a4];p11  == p11;[a4])  by now apply eq_9'. 
  assert (a4p22:  [a4];p22  == p22;[a4])  by now apply eq_9'. 
  assert (a4q214: [a4];q214 == q214;[a4]) by now apply eq_9'. 
  assert (a4q211: [a4];q211 == q211;[a4]) by now apply eq_9'. 
  assert (a4q311: [a4];q311 == q311;[a4]) by now apply eq_9'. 
  assert (p41p11: p41;p11;[a1\cap !a4 \cup !a1\cap a4] <== 0).
   eapply same_value. apply frel_comp. reflexivity. 
  assert (q211q311: q211;q311;[a2\cap !a3 \cup !a2\cap a3] <== 0).
   eapply same_value. apply frel_comp. reflexivity.
  assert (r12p22: r12;p22;p22;[a1\cap !a2 \cup !a1\cap a2] <== 0).
   eapply same_value. simpl bstep. rewrite 2frel_comp. reflexivity. reflexivity.
  (** this one cannot be used by [hkat], it's used by [rmov1]  *)
  assert (p13p22: p13;p22 == p22;p13) by now apply eq_6'.

  (** here starts the proof; the numbers in the comments refer to the
     equation numbers in Angus and Kozen's paper proof *)

  (** (19) *)
  transitivity (
    x1;p41;p11;q214;q311;
    ([!a1\cap !a4];p11;q214;q311 +
     [!a1\cap  a4];p11;q214;q311 +
     [ a1\cap !a4];p13;[!a4];q214;q311 +
     [a1\cap a4];p13;([!a2];p22)^*;[a2 \cap !a3];p41;p11;q214;q311)^*;
    [a1];p13;([!a2];p22)^*;[a2 \cap a3 \cap a4];z2). 
  clear -a4p13 a4p22. hkat. 
  do 2 rmov1 p13. 
  (** (23+) *)
  transitivity (
    x1;p41;p11;q214;q311;
    ([!a1\cap !a4];p11;q214;q311 +
     [!a1\cap  a4];p11;q214;q311 +
     [ a1\cap !a4];p13;[!a4];q214;q311 +
     [a1\cap a4];p13;([!a2];p22)^*;[a2 \cap !a3];p41;p11;q214;q311)^*;
    ([!a2];p22)^*;[a1 \cap a2 \cap a3 \cap a4];(p13;z2)). 
  clear -a1p22; hkat. 
  setoid_replace (p13;z2) with z2
     by (unfold z2, clr; mrewrite <-(gc_correct y1); [ simpl gc; kat | reflexivity ]).
  (** (24) *)
  transitivity (x1;p41;p11;q214;q311;
    ([a1 \cap a4];p13;([!a2];p22)^*;[a2 \cap !a3];p41;p11;q214;q311)^*;
    ([!a2];p22)^*;[a1 \cap a2 \cap a3 \cap a4];z2).
  clear -p41p11 a1p22 a1q214 a1q311 a4p11 a4p13 a4p22 a4q214 a4q311; hkat.
  (** big simplification w.r.t the paper proof here... *)

  (** (27) *)
  assert (p41p11q214: p41;p11;q214 == p41;p11;q211).
  change (upd y4 (f' y1) ; upd y1 (f' y1) ; upd y2 (g' y1 y4) == upd y4 (f' y1) ; upd y1 (f' y1) ; upd y2 (g' y1 y1)).
  now rewrite 3frel_comp.
  do 2 mrewrite p41p11q214. clear p41p11q214.
  (** (29) *)
  transitivity (x1;(p41;(p11;q211;q311;[a1];p13;([!a2];p22)^*;[a2\cap!a3]))^*;
                p41;p11;q211;q311;([!a2];p22)^*;[a1\cap a2\cap a3];z2).
  clear -p41p11 a1p22 a1q211 a1q311 a4p22 a4q211 a4q311; hkat.
  (** (31) *)
  transitivity (x1;(p11;q211;q311;[a1];p13;([!a2];p22)^*;[a2\cap!a3])^*;
                p11;q211;q311;([!a2];p22)^*;[a1\cap a2\cap a3];z2).
  unfold z2, clr. mrewrite <-(gc_correct y4). 2: reflexivity. simpl gc. kat. 
  (** (32) *)
  rmov1 p13.
  transitivity ((x1;p11);(q211;q311;([!a2];p22)^*;[a1\cap a2\cap!a3];(p13;p11))^*;
                q211;q311;([!a2];p22)^*;[a1\cap a2\cap a3];z2).
  clear -a1p22 a2p13 a3p13; hkat. 
  (** big simplification w.r.t the paper proof here... *)

  (** (33) *)
  setoid_replace (x1;p11) with s1 by apply eq_8. 
  setoid_replace (p13;p11) with r13 by apply eq_8. 
  (** (34) *)
  transitivity (s1;(q211;q311;(([!a2];p22)^*;([a1];r13));[a2\cap!a3])^*;
                q211;q311;([!a2];p22)^*;[a1\cap a2\cap a3];z2).
  clear -a2r13 a3r13; hkat. 
  setoid_replace (([!a2];p22)^*;([a1];r13)) with ([a1];r13;([!a2];p22)^*)
   by (assert (r13;p22 == p22;r13) by (now apply eq_6'); rmov1 r13; clear -a1p22; hkat). 
  transitivity (s1;([a1];(q211;q311;r13);([!a2];p22)^*;[a2\cap!a3])^*;
                q211;q311;([!a2];p22)^*;[a1\cap a2\cap a3];z2).
  clear -a1q311 a1q211; hkat. 
  (** (35) *)
  setoid_replace (q211;q311;r13) with (q211;q311;r12).
  2: change (upd y2 (g' y1 y1) ; upd y3 (g' y1 y1) ; upd y1 (f' (f' y3)) == upd y2 (g' y1 y1) ; upd y3 (g' y1 y1) ; upd y1 (f' (f' y2))); now rewrite 3frel_comp.
  (** (36) *)
  transitivity (s1;([a1];(q211;q311);[!a2];r12;([!a2];p22)^*;[a2])^*;
                (q211;q311);[a2];([!a2];p22)^*;[a1\cap a2];z2).
  clear -a3p22 a3r12 q211q311. hkat. 
  (** (37) *)
  transitivity (s1;([a1];q211;[!a2];r12;([!a2];p22)^*;[a2])^*;
                q211;[a2];([!a2];p22)^*;[a1\cap a2];z2).
  unfold z2, clr. mrewrite <-(gc_correct y3). 2: reflexivity. simpl gc. kat. 
  (** (38) *)
  transitivity (s1;[a1];q211;([!a2];r12;[a1];p22;[a2];q211 + 
                              [!a2];r12;[a1];p22;[!a2];(p22;q211))^*;[a2];z2).
  clear -a1p22 a1q211 a2r12 r12p22 a1p22. hkat. 
  (** big simplification w.r.t the paper proof here... *)

  (** (43) *)
  assert (p22q211: p22;q211 == q211) by apply eq_8. rewrite p22q211.
  transitivity (s1;[a1];q211;([!a2];r12;[a1];(p22;q211))^*;[a2];z2). kat.
  rewrite p22q211. clear p22q211.
  (** (44) *)
  unfold s1, a1, q211, r12, a2. rewrite <-eq_9. mrewrite eq_7. 2: reflexivity.
  mrewrite <-eq_9. mrewrite (eq_7 y1 y2 (f' (f' y2))). 2: reflexivity.
  unfold z2, clr. mrewrite <-(gc_correct y1). 2: reflexivity.
  unfold rhs, z2, clr, s2, a2. rewrite <-eq_9.
  unfold q222. mrewrite eq_7. 2: reflexivity.
  unfold r22. mrewrite <-eq_9. do 2 mrewrite eq_8.
  simpl gc. kat. 
  (** (47) *)
Qed.

End s.
