/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Points of `Over` sites

Given a point `Φ` of a site `(C, J)`, an object `X : C`, and `x : Φ.fiber.obj X`,
we define a point `Φ.over x` of the site `(Over X, J.over X)`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [LocallySmall.{w} C] (Φ : Point.{w} J) {X : C} (x : Φ.fiber.obj X)

set_option backward.isDefEq.respectTransparency false in
open InitiallySmall in
/-- Given a point `Φ` of a site `(C, J)`, an object `X : C`, and `x : Φ.fiber.obj X`,
this is the point of the site `(Over X, J.over X)` such that the fiber of
an object of `Over X` corresponding to a morphism `f : Y ⟶ X` identifies
to subtype of `Φ.fiber.obj Y` consisting of elemnts `y` such
that `Φ.fiber.map f y = x`. -/
def over : Point.{w} (J.over X) where
  fiber := FunctorToTypes.fromOverFunctor Φ.fiber x
  initiallySmall :=
    initiallySmall_of_initial_of_initiallySmall
      (FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber x).inverse
  jointly_surjective := by
    rintro U R hR ⟨u, hu⟩
    obtain ⟨R, rfl⟩ := (Sieve.overEquiv _).symm.surjective R
    simp only [mem_over_iff, Equiv.apply_symm_apply] at hR
    obtain ⟨Y, f, hf, v, rfl⟩ := Φ.jointly_surjective R hR u
    refine ⟨Over.mk (f ≫ U.hom), Over.homMk f, hf, ⟨v, ?_⟩, rfl⟩
    rw [FunctorToTypes.mem_fromOverSubfunctor_iff] at hu ⊢
    simpa

end CategoryTheory.GrothendieckTopology.Point
