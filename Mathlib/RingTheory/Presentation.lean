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
  /-- The relations are mapped to zero under the canonical map. -/
  relation_zero (r : relations) : MvPolynomial.aeval val (relation r) = 0
  σ'_aeval_val_sub_mem_span_range_relation (p : MvPolynomial vars R) :
    σ' ((aeval val) p) - p ∈ Ideal.span (Set.range <| relation)

namespace Algebra.Presentation

variable {R S}
variable (P : Presentation.{t, w} R S)

protected abbrev Ideal : Ideal P.Ring := Ideal.span <| Set.range <| P.relation

/-- The polynomial algebra wrt a family of generators module a family of relations. -/
protected abbrev Quotient : Type (max w u) := P.Ring ⧸ P.Ideal

/-- The canonical map from the quotient obtained from a presentation to `S`. -/
def fromQuotient : P.Quotient →ₐ[P.Ring] S :=
  Ideal.Quotient.liftₐ P.Ideal (Algebra.ofId P.Ring S) <| fun a ha ↦ by
    refine Submodule.span_induction ha ?_ ?_ (fun x y hx hy ↦ ?_) (fun a x hx ↦ ?_)
    · rintro x ⟨r, rfl⟩
      exact P.relation_zero r
    · simp
    · simp [hx, hy]
    · simp [hx]

@[simp]
lemma fromQuotient_mk (x : P.Ring) :
    P.fromQuotient x = aeval P.val x :=
  rfl

/-- `P.Quotient` is `P.Ring`-isomorphic to `S` and in particular `R`-isomorphic to `S`. -/
@[simps]
def quotientEquiv : P.Quotient ≃ₐ[R] S where
  toFun := P.fromQuotient
  invFun s := P.σ s
  left_inv x := Quotient.inductionOn x <| fun x ↦
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    (P.σ'_aeval_val_sub_mem_span_range_relation x)
  right_inv x := by simp
  map_mul' := by simp
  map_add' := by simp
  commutes' := by simp

/-- A presentation is called finite if there are only finitely-many
relations and finitely-many relations. -/
class IsFinite (P : Presentation.{t, w} R S) : Prop where
  finite_vars : Finite P.vars
  finite_relations : Finite P.relations

attribute [instance] IsFinite.finite_vars IsFinite.finite_relations

lemma ideal_fg_of_isFinite [P.IsFinite] : P.Ideal.FG := by
  use (Set.finite_range P.relation).toFinset
  simp

/-- If a presentation is finite, the corresponding quotient is
of finite presentation. -/
instance [P.IsFinite] : FinitePresentation R P.Quotient :=
  FinitePresentation.quotient P.ideal_fg_of_isFinite

lemma finitePresentation_of_presentation_of_isFinite [P.IsFinite] : 
    FinitePresentation R S :=
  FinitePresentation.equiv P.quotientEquiv

section Construction

/-
TODO: add constructor for `Presentation` with `Presentation.IsFinite` for
a finitely-presented algebra.
-/

end Construction

end Algebra.Presentation
