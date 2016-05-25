(*******************************************************************)
(*  This is part of RelationAlgebra, it is distributed under the   *)
(*    terms of the GNU Lesser General Public License version 3     *)
(*              (see file LICENSE for more details)                *)
(*                                                                 *)
(*  Copyright 2012: Damien Pous. (CNRS, LIP - ENS Lyon, UMR 5668)  *)
(*******************************************************************)

(** * lattice: from preorders to Boolean lattices *)

(** We define here all structures ranging from preorders to Boolean
   lattice (e.g., sup-semilattices, inf-semilattices with bottom
   element, bounded lattices, etc...).  *)

Require Export common level.

Delimit Scope ra_terms with ra.
Open Scope ra_scope.
Open Scope ra_terms.

(** * Lattice operations *)

(** The following class packages all operations that can possibly
   come with a preorder: a supremum, a bottom element, a negation,
   etc... We use dummy values when working in structures lacking some
   operations. 

   We use a "Class" rather than a "Structure" just to make the first
   argument of all the corresponding projections implicit. Instances
   of this class will be declared as Canonical structures rather than
   typeclasses instances, so that this first argument will actually be
   inferred by unification. (except in the abstract and unconstrained
   case, where typeclass resolution will be called since unification
   will keep the hole unconstrained) *)

Class ops := mk_ops {
  car: Type;                    (** carrier *)
  leq: relation car;            (** preorder *)
  weq: relation car;            (** underlying equality *)
  cup: car -> car -> car;       (** supremum *)
  cap: car -> car -> car;       (** infimum *)
  neg: car -> car;              (** Boolean negation *)
  bot: car;                     (** bottom element *)
  top: car                      (** top element *)
}.
Implicit Arguments car [].
Coercion car: ops >-> Sortclass.
Bind Scope ra_terms with car.

(** Hints for simpl *)
Arguments weq {ops} (x y)%ra / : simpl nomatch.
Arguments leq {ops} (x y)%ra / : simpl nomatch.
Arguments cup {ops} (x y)%ra / : simpl nomatch.
Arguments cap {ops} (x y)%ra / : simpl nomatch.
Arguments neg {ops} (x)%ra / : simpl nomatch.
Arguments bot {ops} / : simpl nomatch.
Arguments top {ops} / : simpl nomatch.

(** Notations *)
Infix "<=="  := leq (at level 79): ra_scope.
Infix "=="   := weq (at level 79): ra_scope.
Infix "\cup" := cup (left associativity, at level 50): ra_terms.
Infix "\cap" := cap (left associativity, at level 40): ra_terms.
Notation "! x" := (neg x) (right associativity, at level 20): ra_terms.

(** * Lattice laws (axioms) *)

(** [laws l X] provides the laws corresponding to the various
   operations of [X], provided these operations belong to the level
   [l]. For instance, the specification of the supremum ([cup]) is
   available only if the level contains [CUP].

   Note that [leq] is always require to be a preorder, and [weq] is
   always required to be the kernel of that preorder.
   
   Also note that some axioms ([leq_bx_], [leq_x_t_]) are present
   unless some operations are present in [l]. They end with an
   underscore, they are actually derivable from the other axioms when
   the additional operations belong to [l]. They are reformulated
   without the escaping disjunction below, under the same name but
   without the ending underscore (see [leq_bx], [leq_x_t] below).

   The field name [cupcap_] also ends with an underscore, this is
   because it's statement is an inequality, for which the converse
   inequality is derivable. It is thus later reformulated as an
   equality (see lemma [cupcap] below).

   Unlike for operations ([ops]), laws are actually inferred by
   typeclass resolution. *)

Class laws (l: level) (X: ops) := {
  leq_PreOrder:> PreOrder leq;
  weq_spec            : forall x y , x==y <-> x<==y /\ y<==x;
  cup_spec {Hl:CUP<<l}: forall x y z, x \cup y <== z <-> x <== z /\ y <== z;
  cap_spec {Hl:CAP<<l}: forall x y z, z <== x \cap y <-> z <== x /\ z <== y;
  leq_bx_  {Hl:BOT<<l}: NEG+CAP<<l \/ forall x, bot <== x;
  leq_xt_  {Hl:TOP<<l}: NEG+CUP<<l \/ forall x, x <== top;
  cupcap_  {Hl:DL <<l}: forall x y z, (x\cup y) \cap (x\cup z) <== x \cup (y \cap z);
  capneg   {Hl:NEG+CAP+BOT<<l}: forall x, x \cap !x == bot;
  cupneg   {Hl:NEG+CUP+TOP<<l}: forall x, x \cup !x == top
}.



(** * Properties of the preorder ([<==]) and it kernel ([==]) *)

Lemma antisym `{laws}: forall x y, x<==y -> y<==x -> x==y.
Proof. intros. apply weq_spec; split; assumption. Qed.

Lemma from_below `{laws}: forall x y, (forall z, z<==x <-> z<==y) -> x==y.
Proof. intros x y E. apply antisym; apply E; reflexivity. Qed.

Lemma from_above `{laws}: forall x y, (forall z, x<==z <-> y<==z) -> x==y.
Proof. intros x y E. apply antisym; apply E; reflexivity. Qed.


(** Trivial hints *)
Hint Extern 0 (_ <== _) => reflexivity. 
Hint Extern 0 (_ == _) => reflexivity. 

(** Instances to be used by the setoid_rewrite machinery *)
Instance weq_Equivalence `{laws}: Equivalence weq.
Proof.
  constructor. 
   intro. now rewrite weq_spec. 
   intros ? ?. rewrite 2weq_spec. tauto.
   intros x y z. rewrite 3weq_spec. intuition; etransitivity; eassumption.
Qed.

Instance weq_leq `{laws}: subrelation weq leq.
Proof. intros x y E. apply weq_spec in E as [? ?]. assumption. Qed.

Instance weq_geq `{laws}: subrelation weq (flip leq).
Proof. intros x y E. apply weq_spec in E as [? ?]. assumption. Qed.

Instance leq_weq_iff `{laws}: Proper (weq ==> weq ==> iff) leq.
Proof.
  intros x y E x' y' E'. split; intro L. 
  now rewrite <-E, <-E'.
  now rewrite E, E'.
Qed.

(** Utility lemmas, to deduce that a function preserves [weq] once we
   proved that it preserves [leq], these are extremely useful in
   practice *)

Lemma op_leq_weq_1 {h k X Y} {HX: laws h X} {HY: laws k Y} {f: X -> Y} 
  {Hf: Proper (leq ==> leq) f}: Proper (weq ==> weq) f.
Proof. intros x y. rewrite 2weq_spec. intro E; split; apply Hf; apply E. Qed.

Lemma op_leq_weq_2 {h k l X Y Z} {HX: laws h X} {HY: laws k Y} {HZ: laws l Z} {f: X -> Y -> Z}
  {Hf: Proper (leq ==> leq ==> leq) f}: Proper (weq ==> weq ==> weq) f.
Proof. 
  intros x y E x' y' E'. rewrite weq_spec in E. rewrite weq_spec in E'.
  apply antisym; apply Hf; (apply E || apply E').
Qed.

(** Additional hints, to speedup typeclass resolution  *)

Instance leq_Reflexive `{laws}: Reflexive leq |1.
Proof. eauto with typeclass_instances. Qed.
Instance leq_Transitive `{laws}: Transitive leq |1.
Proof. eauto with typeclass_instances. Qed.

Instance weq_Reflexive `{laws}: Reflexive weq |1.
Proof. eauto with typeclass_instances. Qed.
Instance weq_Transitive `{laws}: Transitive weq |1.
Proof. eauto with typeclass_instances. Qed.
Instance weq_Symmetric `{laws}: Symmetric weq |1.
Proof. eauto with typeclass_instances. Qed.

(** We declare most projections as Opaque for typeclass resolution:
   this saves a lot of compilation time *)
(* NOTE: declaring [weq] as opaque for typeclasses also saves some time,
   but this is problematic with the [Prop] instances, for which we often
   need [weq=iff] to be used by typeclass resolution *)
Typeclasses Opaque (* weq *) leq cup cap neg bot top.


(** * Basic properties of [\cup], [\cap], [bot], and [top] *)

Lemma leq_cupx `{laws} `{CUP<<l}: forall x y z, x<==z -> y<==z -> x \cup y <== z.
Proof. intros. apply cup_spec. split; assumption. Qed.

Lemma leq_xcup `{laws} `{CUP<<l}: forall x y z, z<==x \/ z<==y -> z <== x \cup y.
Proof. 
  intros x y z. assert (C:= cup_spec x y (x\cup y)). 
  intros [E|E]; rewrite E; apply C; reflexivity.
Qed.

Lemma leq_xcap `{laws} `{CAP<<l}: forall x y z, z<==x -> z<==y -> z <== x \cap y.
Proof. intros. apply cap_spec. split; assumption. Qed.

Lemma leq_capx `{laws} `{CAP<<l}: forall x y z, x<==z \/ y<==z -> x \cap y <== z.
Proof. 
  intros x y z. assert (C:= cap_spec x y (x\cap y)). 
  intros [E|E]; rewrite <- E; apply C; reflexivity.
Qed.

Lemma leq_bx `{L: laws} {Hl:BOT<<l}: forall x, bot <== x.
Proof.
  destruct leq_bx_ as [Hl'|H]. 2: apply H. 
  intro x. rewrite <-(capneg x). apply leq_capx. left. reflexivity. 
Qed.

Lemma leq_xb_iff `{L: laws} {Hl:BOT<<l}: forall x, x <== bot <-> x == bot.
Proof.
  split; intro. apply antisym. assumption. apply leq_bx. 
  now apply weq_leq.
Qed.

Lemma leq_xt `{L: laws} {Hl:TOP<<l}: forall x, x <== top.
Proof.
  destruct leq_xt_ as [Hl'|H]. 2: apply H. 
  intro x. rewrite <-(cupneg x). apply leq_xcup. left. reflexivity. 
Qed.

Lemma leq_tx_iff `{L: laws} {Hl:TOP<<l}: forall x, top <== x <-> x == top.
Proof.
  split; intro. apply antisym. apply leq_xt. assumption. 
  now apply weq_leq.
Qed.


(** * Subtyping / weakening *)

(** laws that hold at any level [h] hold for all level [k << h]  *)
Lemma lower_lattice_laws {h k} {X} {H: laws h X} {le: k<<h}: laws k X.
Proof. 
  constructor; try solve [ apply H | intro; apply H; eauto using lower_trans ]. 
   intro. right. eapply @leq_bx. apply H. eauto using lower_trans. 
   intro. right. eapply @leq_xt. apply H. eauto using lower_trans. 
Qed.


(** * Solving (in)equations in non distributive lattices *)

(** simple tactic to solve lattice (in)equations, 
   using a basic focused proof search algorithm *)
Ltac lattice := 
  let rec async := (* idtac "async"; *) solve 
    [ apply leq_cupx; async
    | apply leq_xcap; async
    | apply leq_bx
    | apply leq_xt
    | sync_l false || sync_r false ]
  with sync_l b := (* idtac "sync_l"; *) solve 
    [ reflexivity 
    | assumption
    | apply leq_capx; ((left; sync_l true) || (right; sync_l true))
    | match b with true => async end ]
  with sync_r b := (* idtac "sync_r"; *) solve 
    [ reflexivity
    | assumption 
    | apply leq_xcup; ((left; sync_r true) || (right; sync_r true))
    | match b with true => async end ]
  in
  (try apply antisym); async || fail "not a lattice theorem".

(** extension of the above tactic so that it also tries to exploit
    hypotheses in a more agressive way *)
Ltac hlattice :=
  repeat 
    match goal with 
      | H: _ == _ |- _ => apply weq_spec in H as [? ?]
      | H: _ \cup _ <== _ |- _ => apply cup_spec in H as [? ?]
      | H: _ <== _ \cap _ |- _ => apply cap_spec in H as [? ?]
    end; lattice.


(** * Reasoning by duality *)

(** dual lattice operations: we reverse the preorder, and swap cup
   with cap, and resp bot with top) *)
Definition dual (X: ops) := {|
  leq := flip leq;
  weq := weq;
  cup := cap;
  cap := cup;
  neg := neg;
  bot := top;
  top := bot |}.

Lemma capcup_ `{laws} `{DL<<l}: forall x y z, x \cap (y \cup z) <== (x\cap y) \cup (x\cap z).
Proof.
  intros. rewrite <- cupcap_. apply leq_xcap. lattice.
  transitivity (z\cup x\cap y). 2: lattice. 
  rewrite <- cupcap_. lattice.
Qed.

Ltac inverse_lower l Hl := 
  revert Hl; clear; destruct l; unfold lower, merge; simpl; rewrite ?landb_spec; tauto.

(** laws on a given set of operations can be transferred to the dual set of operations *)
Lemma dual_laws l (X: ops): laws (level.dual l) X -> laws l (dual X).
Proof.
  intro H. constructor; try (destruct l; apply H).
  constructor. apply H. intros x y z H1 H2. revert H2 H1. simpl. apply H.
  intros x y. simpl. rewrite weq_spec. tauto.
  intro. simpl. eapply @capcup_. apply H. inverse_lower l Hl. 
  intro. simpl. eapply @cupneg. apply H. inverse_lower l Hl. 
  intro. simpl. eapply @capneg. apply H. inverse_lower l Hl. 
Qed.

(** this gives us a tactic to prove properties by lattice duality *)
Lemma dualize {h} {P: ops -> Prop} (L: forall l X, laws l X -> h<<l -> P X) 
  {l X} {H: laws l X} {Hl:level.dual h<<l}: P (dual X).
Proof. 
  apply L with (level.dual l). apply dual_laws. 
  destruct l; apply H. 
  revert Hl. rewrite 2lower_spec. destruct l; destruct h; simpl. tauto. 
Qed.

Ltac dual x := apply (dualize x).



(** * [(\cup,bot)] forms a commutative, idempotent monoid *)

Lemma cupA `{laws} `{CUP<<l}: forall x y z, x \cup (y \cup z) == (x \cup y) \cup z.
Proof. intros. lattice. Qed.
Lemma cupC `{laws} `{CUP<<l}: forall x y, x \cup y == y \cup x.
Proof. intros. lattice. Qed.
Lemma cupI `{laws} `{CUP<<l}: forall x, x \cup x == x.
Proof. intros. lattice. Qed.
Lemma cupbx `{laws} `{CUP+BOT<<l}: forall x, bot \cup x == x.
Proof. intros. lattice. Qed.
Lemma cupxb `{laws} `{CUP+BOT<<l}: forall x, x \cup bot == x.
Proof. intros. lattice. Qed.

Lemma cuptx `{laws} `{CUP+TOP<<l}: forall x, top \cup x == top.
Proof. intros. lattice. Qed.
Lemma cupxt `{laws} `{CUP+TOP<<l}: forall x, x \cup top == top.
Proof. intros. lattice. Qed.

Lemma leq_cup_l `{laws} `{CUP<<l} x y: x <== x \cup y.
Proof. lattice. Qed.
Lemma leq_cup_r `{laws} `{CUP<<l} x y: y <== x \cup y.
Proof. lattice. Qed.

Instance cup_leq `{laws} `{CUP<<l}: Proper (leq ==> leq ==> leq) cup.
Proof. intros x x' Hx y y' Hy. lattice. Qed.

Instance cup_weq `{laws} `{CUP<<l}: Proper (weq ==> weq ==> weq) cup.
Proof. apply op_leq_weq_2. Qed.

(** distribution of [\cup] over [\cap] *)
Lemma cupcap `{laws} `{DL<<l}: forall x y z, x \cup (y \cap z) == (x\cup y) \cap (x\cup z).
Proof. intros. apply antisym. lattice. apply cupcap_. Qed.

(** characterisation of the preorder by the semilattice operations *)
Lemma leq_iff_cup `{laws} `{CUP<<l} (x y: X): x<==y <-> x\cup y==y. 
Proof. split. intro. hlattice. intro E. rewrite <- E. lattice. Qed.

(* this lemma is used twice... *)
Lemma comm4 `{laws} `{CUP<<l} (a b c d: X): a\cup b\cup c\cup d == (a\cup c)\cup(b\cup d).
Proof. lattice. Qed.


(** * [(\cap,top)] forms a commutative, idempotent monoid (by duality) *)

Lemma capA `{laws} `{CAP<<l}: forall x y z, x \cap (y \cap z) == (x \cap y) \cap z.
Proof. dual @cupA. Qed.
Lemma capC `{laws} `{CAP<<l}: forall x y, x \cap y == y \cap x.
Proof. dual @cupC. Qed.
Lemma capI `{laws} `{CAP<<l}: forall x, x \cap x == x.
Proof. dual @cupI. Qed.
Lemma captx `{laws} `{CAP+TOP<<l}: forall x, top \cap x == x.
Proof. dual @cupbx. Qed.
Lemma capxt `{laws} `{CAP+TOP<<l}: forall x, x \cap top == x.
Proof. dual @cupxb. Qed.

Lemma capbx `{laws} `{CAP+BOT<<l}: forall x, bot \cap x == bot.
Proof. dual @cuptx. Qed.
Lemma capxb `{laws} `{CAP+BOT<<l}: forall x, x \cap bot == bot.
Proof. dual @cupxt. Qed.

Lemma leq_cap_l `{laws} `{CAP<<l} x y: x \cap y <== x.
Proof. lattice. Qed.
Lemma leq_cap_r `{laws} `{CAP<<l} x y: x \cap y <== y.
Proof. lattice. Qed.

Instance cap_leq `{laws} `{CAP<<l}: Proper (leq ==> leq ==> leq) cap.
Proof. intros x x' Hx y y' Hy. lattice. Qed.

Instance cap_weq `{laws} `{CAP<<l}: Proper (weq ==> weq ==> weq) cap.
Proof. apply op_leq_weq_2. Qed.

Lemma leq_iff_cap `{laws} `{CAP<<l} (x y: X): x<==y <-> x\cap y==x. 
Proof. split. intro. hlattice. intro E. rewrite <- E. lattice. Qed.

Lemma capcup `{laws} `{DL<<l}: forall x y z, x \cap (y \cup z) == (x\cap y) \cup (x\cap z).
Proof. dual @cupcap. Qed.

Lemma cupcap' `{laws} `{DL<<l}: forall x y z, (y \cap z) \cup x == (y\cup x) \cap (z\cup x).
Proof. intros. now rewrite cupC, cupcap, 2(cupC x). Qed.

Lemma capcup' `{laws} `{DL<<l}: forall x y z, (y \cup z) \cap x == (y\cap x) \cup (z\cap x).
Proof. dual @cupcap'. Qed.


(** * Properties of negation *)

Lemma neg_unique' `{laws} `{BL<<l} (x y: X): y \cap x <== bot -> y <== !x.
Proof.
  intros E. rewrite <-(capxt y). rewrite <-(cupneg x). 
  rewrite capcup. rewrite E. lattice. 
Qed.

Lemma neg_unique `{laws} `{BL<<l} (x y: X):
  top <== y \cup x -> y \cap x <== bot -> y == !x.
Proof. 
  intros Ht Hb. apply antisym. 
  now apply neg_unique'. 
  revert Ht. dual @neg_unique'. 
Qed.

Instance neg_leq `{laws} `{BL<<l}: Proper (leq --> leq) neg.
Proof.
  intros x y E. apply neg_unique'. 
  rewrite <-E, capC. now rewrite capneg.
Qed.

Instance neg_weq `{laws} `{BL<<l}: Proper (weq ==> weq) neg.
Proof. intros x y. rewrite 2weq_spec. intro E; split; apply neg_leq, E. Qed.

Lemma negneg `{laws} `{BL<<l} (x: X): !!x == x.
Proof. symmetry. apply neg_unique. now rewrite cupneg. now rewrite capneg. Qed.

Lemma negbot `{laws} `{BL<<l}: !bot == top.
Proof. symmetry. apply neg_unique; lattice. Qed.
  
Lemma negtop `{laws} `{BL<<l}: !top == bot.
Proof. dual @negbot. Qed.

Lemma negcap' `{laws} `{BL<<l} (x y: X): !x \cup !y <== !(x\cap y).
Proof. apply leq_cupx; apply neg_leq; lattice. Qed.

Lemma negcup `{laws} `{BL<<l} (x y: X): !(x\cup y) == !x \cap !y.
Proof. 
  apply antisym. dual @negcap'.
  rewrite <- (negneg x) at 2. 
  rewrite <- (negneg y) at 2. 
  now rewrite negcap', negneg. 
Qed.

Lemma negcap `{laws} `{BL<<l} (x y: X): !(x\cap y) == !x \cup !y.
Proof. dual @negcup. Qed.

(** switching negations *)
Lemma neg_leq_iff `{laws} `{BL<<l} (x y: X): !x <== !y <-> y <== x. 
Proof. split. intro E. apply neg_leq in E. now rewrite 2negneg in E. apply neg_leq. Qed.
Lemma neg_leq_iff' `{laws} `{BL<<l} (x y: X): x <== !y <-> y <== !x. 
Proof. now rewrite <- neg_leq_iff, negneg. Qed.
Lemma neg_leq_iff'' `{laws} `{BL<<l} (x y: X): !x <== y <-> !y <== x. 
Proof. now rewrite <- neg_leq_iff, negneg. Qed.

Lemma neg_weq_iff `{laws} `{BL<<l} (x y: X): !x == !y <-> y == x. 
Proof. now rewrite 2weq_spec, 2neg_leq_iff. Qed.
Lemma neg_weq_iff' `{laws} `{BL<<l} (x y: X): x == !y <-> !x == y. 
Proof. now rewrite <-neg_weq_iff, negneg. Qed.
Lemma neg_weq_iff'' `{laws} `{BL<<l} (x y: X): !x == y <-> x == !y. 
Proof. now rewrite <-neg_weq_iff, negneg. Qed.

Ltac neg_switch := first [
  rewrite neg_leq_iff |
  rewrite neg_leq_iff' |
  rewrite neg_leq_iff'' |
  rewrite <-neg_leq_iff |
  rewrite neg_weq_iff |
  rewrite neg_weq_iff' |
  rewrite neg_weq_iff'' |
  rewrite <-neg_weq_iff ].

Lemma leq_cap_neg `{laws} `{BL<<l} (x y: X): y <== x <-> y \cap !x <== bot.
Proof.
  split. intro E. now rewrite E, capneg.
  intro E. now rewrite (neg_unique' _ _ E), negneg.
Qed.

Lemma leq_cap_neg' `{laws} `{BL<<l} (x y: X): y \cap x <== bot <-> y <== !x.
Proof. rewrite <-(negneg x) at 1. symmetry. apply leq_cap_neg. Qed.

Lemma leq_cup_neg `{laws} `{BL<<l} (x y: X): x <== y <-> top <== y \cup !x.
Proof. dual @leq_cap_neg. Qed.

Lemma leq_cup_neg' `{laws} `{BL<<l} (x y: X): top <== y \cup x -> !x <== y.
Proof. dual @leq_cap_neg'. Qed.


(** * Morphisms *)

(** an [l]-morphism betwen to sets of operations are defined as
   expected: the function is requried to preserve only the operations
   listed in [l] *)

Class morphism l {X Y: ops} (f: X -> Y) := {
  fn_leq: Proper (leq ==> leq) f;
  fn_weq: Proper (weq ==> weq) f;
  fn_cup {Hl:CUP<<l}: forall x y, f (x \cup y) == f x \cup f y;
  fn_cap {Hl:CAP<<l}: forall x y, f (x \cap y) == f x \cap f y;
  fn_bot {Hl:BOT<<l}: f bot == bot;
  fn_top {Hl:TOP<<l}: f top == top;
  fn_neg {Hl:NEG<<l}: forall x, f (!x) == ! f x
}.

(** generating a structure by injective embedding *)

Lemma laws_of_injective_morphism {h l X Y} {L: laws h Y} {Hl: l<<h} f:
  @morphism l X Y f -> 
  (forall x y, f x <== f y -> x <== y) ->
  (forall x y, f x == f y -> x == y) ->
  laws l X.
Proof.
  intros Hf Hleq Hweq. apply (@lower_lattice_laws _ _ _ L) in Hl. clear L.
  assert (Hleq_iff: forall x y, f x <== f y <-> x <== y).
   split. apply Hleq. apply fn_leq.
  assert (Hweq_iff: forall x y, f x == f y <-> x == y).
   split. apply Hweq. apply fn_weq.
  constructor. constructor. 
   intro. apply Hleq. reflexivity. 
   intros x y z. rewrite <-3Hleq_iff. apply Hl.
   intros. now rewrite <-Hweq_iff, weq_spec, 2Hleq_iff. 
   intros. rewrite <-3Hleq_iff, fn_cup. apply cup_spec.
   intros. rewrite <-3Hleq_iff, fn_cap. apply cap_spec.
   right. intros. apply Hleq. rewrite fn_bot. apply leq_bx.
   right. intros. apply Hleq. rewrite fn_top. apply leq_xt.
   intros. apply Hleq. rewrite fn_cup, fn_cap, 2fn_cup, fn_cap. apply cupcap_.
   intros. rewrite <-Hweq_iff. rewrite fn_cap, fn_neg, fn_bot. apply capneg.
   intros. rewrite <-Hweq_iff. rewrite fn_cup, fn_neg, fn_top. apply cupneg.
Qed.



(** * Pointwise extension of a structure *)

Definition pw0 {Y X} (f: X) (y: Y) := f. 
Definition pw1 {Y X} (f: X -> X) (u: Y -> X) (y: Y) := f (u y). 
Definition pw2 {Y X} (f: X -> X -> X) (u v: Y -> X) (y: Y) := f (u y) (v y). 

Arguments pw0 {Y X} _ _ /.
Arguments pw1 {Y X} _ _ _ /.
Arguments pw2 {Y X} _ _ _ _ /.

(** As explained above, we use canonical structures for operations inference *)
Canonical Structure pw_ops (X: ops) Y: ops := {|
  car := Y -> X;
  leq := pwr leq;
  weq := pwr weq;
  cup := pw2 cup;
  cap := pw2 cap;
  neg := pw1 neg;
  bot := pw0 bot;
  top := pw0 top
|}.

(** In contrast, we use typeclass resolution for laws inference.
 Note the level polymorphism in the instance below: laws of level [l]
 on [X] yield laws of the same level [l] on [Y -> X]. *)
Instance pw_laws `{laws} Y: laws l (pw_ops X Y).
Proof.
  constructor; simpl; intros. constructor.
   intros f x. reflexivity.
   intros f g h ? ? x. now transitivity (g x).
   setoid_rewrite weq_spec. firstorder.
   setoid_rewrite cup_spec. firstorder.
   setoid_rewrite cap_spec. firstorder.
   right; intros; apply leq_bx. 
   right; intros; apply leq_xt.
   apply cupcap_.
   apply capneg.
   apply cupneg.
Qed.


(** trick to factorise code in various tactics: make the choice
   between [leq] or [weq] first-class *)

Definition leq_or_weq (b: bool) := if b then @leq else @weq.
Arguments leq_or_weq _ {_} (_ _)%ra.
Notation "x <=[ b ]= y"  := (leq_or_weq b x y) (at level 79): ra_scope.

Lemma leq_or_weq_weq `{laws} b: Proper (weq ==> weq ==> iff) (leq_or_weq b).
Proof. unfold leq_or_weq; case b; eauto with typeclass_instances. Qed.
