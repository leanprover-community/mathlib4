/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Generators
import Mathlib.RingTheory.FinitePresentation

/-!

# Presentations of algebras

## Main definition

- `Algebra.Presentation`: A presentation of a `R`-algebra `S` is a family of
  generators with
  1. `relations`: The type of relations.
  2. `relation : relations → MvPolynomial vars R`: The assignment of
     each relation to a polynomial in the generators.

## TODO

- define `Hom`s of presentations

-/

universe t w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/--
A presentation of a `R`-algebra `S` is a family of
generators with
1. `relations`: The type of relations.
2. `relation : relations → MvPolynomial vars R`: The assignment of
each relation to a polynomial in the generators.
-/
structure Algebra.Presentation extends Algebra.Generators.{w} R S where
  /-- The type of relations.  -/
  relations : Type t
  /-- The assignment of each relation to a polynomial in the generators. -/
  relation : relations → MvPolynomial vars R
  /-- The relations span the kernel of the canonical map. -/
  ker_algebraMap_eq_span_range_relation :
    RingHom.ker (algebraMap (MvPolynomial vars R) S) = Ideal.span (Set.range <| relation)

namespace Algebra.Presentation

variable {R S}
variable (P : Presentation.{t, w} R S)

protected abbrev Ideal : Ideal P.Ring := RingHom.ker <| algebraMap P.Ring S

lemma ideal_eq_span_range_relation : P.Ideal = Ideal.span (Set.range <| P.relation) :=
  P.ker_algebraMap_eq_span_range_relation

/-- The polynomial algebra wrt a family of generators module a family of relations. -/
protected abbrev Quotient : Type (max w u) := P.Ring ⧸ P.Ideal

/-- `P.Quotient` is `P.Ring`-isomorphic to `S` and in particular `R`-isomorphic to `S`. -/
@[simps!]
def quotientEquiv : P.Quotient ≃ₐ[P.Ring] S :=
  Ideal.quotientKerAlgEquivOfRightInverse (f := Algebra.ofId P.Ring S) P.aeval_val_σ

/-- A presentation is called finite if there are only finitely-many
relations and finitely-many relations. -/
class IsFinite (P : Presentation.{t, w} R S) : Prop where
  finite_vars : Finite P.vars
  finite_relations : Finite P.relations

attribute [instance] IsFinite.finite_vars IsFinite.finite_relations

lemma ideal_fg_of_isFinite [P.IsFinite] : P.Ideal.FG := by
  use (Set.finite_range P.relation).toFinset
  simp [ideal_eq_span_range_relation]

/-- If a presentation is finite, the corresponding quotient is
of finite presentation. -/
instance [P.IsFinite] : FinitePresentation R P.Quotient :=
  FinitePresentation.quotient P.ideal_fg_of_isFinite

lemma finitePresentation_of_presentation_of_isFinite [P.IsFinite] :
    FinitePresentation R S :=
  FinitePresentation.equiv (P.quotientEquiv.restrictScalars R)

section Construction

/-
TODO: add constructor for `Presentation` with `Presentation.IsFinite` for
a finitely-presented algebra.
-/

end Construction

/--
Dimension of a presentation defined as the cardinality of the generators
minus the cardinality of the relations.

Note: this definition is completely non-sensical for non-finite presentations and
even then for this to make sense, you should assume that the presentation
is standard smooth.
-/
noncomputable def dimension : ℕ :=
  Nat.card P.vars - Nat.card P.relations

end Algebra.Presentation
