
# Relation Algebra for Coq

Webpage of the project: http://perso.ens-lyon.fr/damien.pous/ra


## DESCRIPTION

This Coq development is a modular library about relation algebra:
those algebras admitting heterogeneous binary relations as a model,
ranging from partially ordered monoid to residuated Kleene allegories
and Kleene algebra with tests (KAT).

This library presents this large family of algebraic theories in a
modular way; it includes several high-level reflexive tactics:
 - [kat], which decides the (in)equational theory of KAT;
 - [hkat], which decides the Hoare (in)equational theory of KAT 
     (i.e., KAT with Hoare hypotheses);
 - [ka], which decides the (in)equational theory of KA;
 - [ra], a normalisation based partial decision procedure for Relation 
     algebra;
 - [ra_normalise], the underlying normalisation tactic.

The tactic for Kleene algebra with tests is obtained by reflection,
using a simple bisimulation-based algorithm working on the appropriate
automaton of partial derivatives, for the generalised regular
expressions corresponding to KAT.

Combined with a formalisation of KA completeness, and then of KAT
completeness on top of it, this provides entirely axiom-free decision
procedures for all model of these theories (including relations,
languages, traces, min-max and max-plus algebras, etc...).

Algebraic structures are generalised in a categorical way: composition
is typed like in categories, allowing us to reach "heterogeneous"
models like rectangular matrices or heterogeneous binary relations,
where most operations are partial. We exploit untyping theorems to
avoid polluting decision algorithms with these additional typing
constraints.


## APPLICATIONS

We give a few examples of applications of this library to program
verification:
- a formalisation of a paper by Dexter Kozen and Maria-Cristina Patron. 
  showing how to certify compiler optimisations using KAT.
- a formalisation of the IMP programming language, followed by: 1/ some
  simple program equivalences that become straightforward to prove
  using our tactics; 2/ a formalisation of Hoare logic rules for partial
  correctness in the above language: all rules except the assignation one 
  are proved by a single call to the hkat tactic.
- a proof of the equivalence of two flowchart schemes, due to
  Paterson. The informal paper proof takes one page; Allegra Angus and
  Dexter Kozen gave a six pages long proof using KAT; our Coq proof is
  about 100 lines.


## INSTALLATION

Run 'make' to compile the library, and 'make install' to install
it. Coq v8.5.0 is required; more recent versions might work.


## DOCUMENTATION

Each module is documented, see index.html or 
     http://perso.ens-lyon.fr/damien.pous/ra
for:
- a description of each module's role and dependencies
- a list of the available user-end tactics
- the coqdoc generated documentation.


## LICENSE

This library is distributed under the terms of the GNU Lesser General
Public License version 3. See files LICENSE and COPYING.


## AUTHORS

* Main author
  - Damien Pous (2012-), CNRS - LIP, ENS Lyon (UMR 5668), France
 
* Additional authors
  - Insa Stucke (2015-), Dpt of CS, University of Kiel, Germany
  - Coq development team (2013-)
