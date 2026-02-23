/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Comma.LocallySmall
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Point.Conservative

/-!
# Points of `Over` sites

Given a point `Φ` of a site `(C, J)`, an object `X : C`, and `x : Φ.fiber.obj X`,
we define a point `Φ.over x` of the site `(Over X, J.over X)`.

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace GrothendieckTopology.Point

variable (Φ : Point.{w} J) {X : C} (x : Φ.fiber.obj X)

set_option backward.isDefEq.respectTransparency false in
open InitiallySmall in
/-- Given a point `Φ` of a site `(C, J)`, an object `X : C`, and `x : Φ.fiber.obj X`,
this is the point of the site `(Over X, J.over X)` such that the fiber of
an object of `Over X` corresponding to a morphism `f : Y ⟶ X` identifies
to subtype of `Φ.fiber.obj Y` consisting of elemnts `y` such
that `Φ.fiber.map f y = x`. -/
@[simps -isSimp]
def over [InitiallySmallCofiltered.{w}
    (FunctorToTypes.fromOverFunctor Φ.fiber x).Elements] : Point.{w} (J.over X) where
  fiber := FunctorToTypes.fromOverFunctor Φ.fiber x
  jointly_surjective := by
    rintro U R hR ⟨u, hu⟩
    obtain ⟨R, rfl⟩ := (Sieve.overEquiv _).symm.surjective R
    simp only [mem_over_iff, Equiv.apply_symm_apply] at hR
    obtain ⟨Y, f, hf, v, rfl⟩ := Φ.jointly_surjective R hR u
    refine ⟨Over.mk (f ≫ U.hom), Over.homMk f, hf, ⟨v, ?_⟩, rfl⟩
    rw [FunctorToTypes.mem_fromOverSubfunctor_iff] at hu ⊢
    simpa

section

variable [LocallySmall.{w} C] [IsCofiltered Φ.fiber.Elements]

instance :
    InitiallySmall.{w} (FunctorToTypes.fromOverFunctor Φ.fiber x).Elements :=
  initiallySmall_of_initial_of_initiallySmall
    (FunctorToTypes.fromOverFunctorElementsEquivalence Φ.fiber x).inverse

instance : IsCofiltered (Φ.over x).fiber.Elements := by
  dsimp [over_fiber]
  infer_instance

end

end GrothendieckTopology.Point

namespace ObjectProperty

open GrothendieckTopology

lemma IsConservativeFamilyOfPoints.over
    {P : ObjectProperty (Point.{w} J)} [ObjectProperty.Small.{w} P]
    [LocallySmall.{w} C] [J.WEqualsLocallyBijective (Type w)] [HasSheafify J (Type w)]
    (hP : P.IsConservativeFamilyOfPoints) (X : C) [HasSheafify (J.over X) (Type w)]
    [∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X),
      InitiallySmallCofiltered.{w}
        (FunctorToTypes.fromOverFunctor Φ.obj.fiber x).Elements] :
    IsConservativeFamilyOfPoints
      (ObjectProperty.ofObj (fun (ψ : Σ (Φ : P.FullSubcategory),
        Φ.obj.fiber.obj X) ↦ ψ.1.obj.over ψ.2)) :=
  mk' (fun Y S hS ↦ by
    obtain ⟨Y, f, rfl⟩ := Over.mk_surjective Y
    obtain ⟨S, rfl⟩ := (Sieve.overEquiv _).symm.surjective S
    rw [mem_over_iff, Equiv.apply_symm_apply]
    obtain ⟨ι, Z, g, rfl⟩ := S.exists_eq_ofArrows
    rw [hP.jointly_reflect_ofArrows_mem_of_small]
    intro Φ y
    obtain ⟨T, a, ⟨_, b, _, ⟨i⟩, hb⟩, ⟨z, hz₁⟩, hz₂⟩ := hS (⟨_, ⟨⟨Φ, Φ.obj.fiber.map f y⟩⟩⟩)
      (⟨by exact y, by rw [FunctorToTypes.mem_fromOverSubfunctor_iff]; rfl⟩)
    rw [Subtype.ext_iff] at hz₂
    dsimp at hz₂
    exact ⟨i, Φ.obj.fiber.map b z,
      (congr_fun (Φ.obj.fiber.map_comp b (g i)) _).symm.trans (by rwa [hb])⟩)

end ObjectProperty

end CategoryTheory
