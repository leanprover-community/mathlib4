/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Local

/-!
# Orthogonal of triangulated subcategories

Let `P` be a triangulated subcategory of a pretriangulated category `C`. We show
that `P.rightOrthogonal` (which consists of objects `Y` with no nonzero
map `X ⟶ Y` with `X` satisfying `P`) is a triangulated subcategory. The dual result
for `P.leftOrthogonal` is also obtained.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Limits Pretriangulated

namespace ObjectProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (P : ObjectProperty C)

section

variable {M : Type*} [AddGroup M] [HasShift C M] [HasZeroMorphisms C]

instance [P.IsStableUnderShift M] : P.rightOrthogonal.IsStableUnderShift M where
  isStableUnderShiftBy n := ⟨fun Y hY X f hX ↦ by
    obtain ⟨g, rfl⟩ := ((shiftEquiv C n).symm.toAdjunction.homEquiv _ _).surjective f
    simp [hY g (P.le_shift (-n) _ hX), Adjunction.homEquiv_unit]⟩

instance [P.IsStableUnderShift M] : P.leftOrthogonal.IsStableUnderShift M where
  isStableUnderShiftBy n := ⟨fun X hX Y f hY ↦ by
    obtain ⟨g, rfl⟩ := ((shiftEquiv C n).toAdjunction.homEquiv _ _).symm.surjective f
    simp [hX g (P.le_shift (-n) _ hY), Adjunction.homEquiv_counit]⟩

end

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

instance : P.rightOrthogonal.IsTriangulatedClosed₂ :=
  .mk' (fun T hT h₁ h₃ X f hX ↦ by
    obtain ⟨g, rfl⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hT f (h₃ _ hX)
    simp [h₁ g hX])

instance : P.leftOrthogonal.IsTriangulatedClosed₂ :=
  .mk' (fun T hT h₁ h₃ Y f hY ↦ by
    obtain ⟨g, rfl⟩ := Pretriangulated.Triangle.yoneda_exact₂ T hT f (h₁ _ hY)
    simp [h₃ g hY])

instance [P.IsStableUnderShift ℤ] : P.rightOrthogonal.IsTriangulated where

instance [P.IsStableUnderShift ℤ] : P.leftOrthogonal.IsTriangulated where

example [P.IsTriangulated] : P.rightOrthogonal.IsTriangulated := inferInstance

example [P.IsTriangulated] : P.leftOrthogonal.IsTriangulated := inferInstance

lemma isLocal_trW [P.IsTriangulated] :
    P.trW.isLocal = P.rightOrthogonal := by
  ext Y
  refine ⟨fun hY X f hX ↦ ?_, fun hY X₁ X₂ f ⟨X₃, g, h, hT, hX₃⟩ ↦ ⟨?_, fun α ↦ ?_⟩⟩
  · exact (hY _ (trW.mk P (contractible_distinguished₁ X) hX)).injective (by simp)
  · suffices ∀ (α : X₂ ⟶ Y), f ≫ α = 0 → α = 0 from fun α₁ α₂ hα ↦ by
      simpa [sub_eq_zero] using this (α₁ - α₂) (by simpa [sub_eq_zero] using hα)
    intro α hα
    obtain ⟨β, rfl⟩ := Triangle.yoneda_exact₂ _ hT α hα
    simp [hY β hX₃]
  · obtain ⟨β, rfl⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT)
      α (hY _ (P.le_shift _ _ hX₃))
    exact ⟨β, rfl⟩

lemma isColocal_trW [P.IsTriangulated] :
    P.trW.isColocal = P.leftOrthogonal := by
  ext X
  refine ⟨fun hX Y f hY ↦ ?_, fun hX Y₂ Y₃ h hh ↦ ?_⟩
  · exact (hX _ (trW.mk P (contractible_distinguished₂ Y) (P.le_shift _ _ hY))).injective (by simp)
  · rw [trW_iff'] at hh
    obtain ⟨Y₁, f, g, hT, hY₁⟩ := hh
    refine ⟨?_, fun α ↦ ?_⟩
    · suffices ∀ (α : X ⟶ Y₂), α ≫ h = 0 → α = 0 from fun α₁ α₂ hα ↦ by
        simpa [sub_eq_zero] using this (α₁ - α₂) (by simpa [sub_eq_zero])
      intro α hα
      obtain ⟨β, rfl⟩ := Triangle.coyoneda_exact₂ _ hT α hα
      simp [hX β hY₁]
    · obtain ⟨β, rfl⟩ := Triangle.coyoneda_exact₂ _ (rot_of_distTriang _ hT)
        α (hX _ (P.le_shift _ _ hY₁))
      exact ⟨β, rfl⟩

variable {P} in
lemma rightOrthogonal.map_bijective_of_isTriangulated
    [P.IsTriangulated] [IsTriangulated C] {Y : C} (hY : P.rightOrthogonal Y)
    (L : C ⥤ D) [L.IsLocalization P.trW] (X : C) :
    Function.Bijective (L.map : (X ⟶ Y) → _) := by
  rw [← isLocal_trW] at hY
  refine ⟨fun f₁ f₂ hf ↦ ?_, fun g ↦ ?_⟩
  · rw [MorphismProperty.map_eq_iff_precomp L P.trW] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    exact (hY _ hs).1 eq
  · obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L P.trW g
    have := Localization.inverts L P.trW φ.s φ.hs
    obtain ⟨α, hα⟩ := (hY _ φ.hs).2 φ.f
    refine ⟨α, ?_⟩
    rw [hφ, ← cancel_epi (L.map φ.s), MorphismProperty.RightFraction.map_s_comp_map,
      ← hα, Functor.map_comp]

variable {P} in
lemma leftOrthogonal.map_bijective_of_isTriangulated
    [P.IsTriangulated] [IsTriangulated C] {X : C} (hX : P.leftOrthogonal X)
    (L : C ⥤ D) [L.IsLocalization P.trW] (Y : C) :
    Function.Bijective (L.map : (X ⟶ Y) → _) := by
  rw [← isColocal_trW] at hX
  refine ⟨fun f₁ f₂ hf ↦ ?_, fun g ↦ ?_⟩
  · rw [MorphismProperty.map_eq_iff_postcomp L P.trW] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    exact (hX _ hs).1 eq
  · obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction L P.trW g
    have := Localization.inverts L P.trW φ.s φ.hs
    obtain ⟨α, hα⟩ := (hX _ φ.hs).2 φ.f
    refine ⟨α, ?_⟩
    rw [hφ, ← cancel_mono (L.map φ.s), MorphismProperty.LeftFraction.map_comp_map_s,
      ← hα, Functor.map_comp]

end ObjectProperty

end CategoryTheory
