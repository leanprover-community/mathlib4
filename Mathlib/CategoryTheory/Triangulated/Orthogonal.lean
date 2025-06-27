/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Right orthogonal to a triangulated subcategory

-/

namespace CategoryTheory

open Limits Pretriangulated Preadditive Triangulated ZeroObject

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace ObjectProperty

variable (S : ObjectProperty C)

def rightOrthogonal : ObjectProperty C :=
  fun Y ↦ ∀ ⦃X : C⦄ (f : X ⟶ Y), S X → f = 0

instance : S.rightOrthogonal.IsClosedUnderIsomorphisms where
  of_iso e h X f hX := by
    rw [← cancel_mono e.inv, zero_comp]
    exact h _ hX

instance [S.IsTriangulated] : S.rightOrthogonal.IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, fun _ _ _ ↦ Subsingleton.elim _ _⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ X f₂ hX ↦ by
    obtain ⟨f₁, rfl⟩ := T.coyoneda_exact₂ hT f₂ (h₃ _ hX)
    rw [h₁ f₁ hX, zero_comp])
  isStableUnderShiftBy n :=
    { le_shift Y hY X f hX := by
        have : f⟦-n⟧' ≫ (shiftEquiv C n).unitIso.inv.app Y = 0 := hY _ (S.le_shift _ _ hX)
        simp only [Preadditive.IsIso.comp_right_eq_zero] at this
        apply (shiftFunctor C (-n)).map_injective
        rw [this, Functor.map_zero] }

lemma rightOrthogonal_precomp_W_bijective [S.IsTriangulated] (Z : C) (hZ : S.rightOrthogonal Z)
    {X Y : C} (w : X ⟶ Y) (hw : S.trW w) :
    Function.Bijective (fun (f : Y ⟶ Z) => w ≫ f) := by
  constructor
  · intros y₁ y₂ hy
    let y := y₁ - y₂
    suffices y = 0 by
      rw [← sub_eq_zero]
      exact this
    dsimp at hy
    obtain ⟨U, f, g, H, mem⟩ := hw
    obtain ⟨u, hu⟩ := Triangle.yoneda_exact₂ _ H y (by dsimp; rw [comp_sub, hy, sub_self])
    rw [hu, hZ u mem, comp_zero]
  · intro z
    rw [trW_iff'] at hw
    obtain ⟨U, f, g, H, mem⟩ := hw
    obtain ⟨u, hu⟩ := Triangle.yoneda_exact₂ _ H z (hZ _ mem)
    exact ⟨u, hu.symm⟩

variable [IsTriangulated C] {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization S.trW]

lemma map_bijective_of_rightOrthogonal [S.IsTriangulated] (X Y : C) (hY : S.rightOrthogonal Y) :
    Function.Bijective (L.map : (X ⟶ Y) → _) := by
  constructor
  · intros f₁ f₂ hf
    rw [MorphismProperty.map_eq_iff_precomp L S.trW] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    exact (S.rightOrthogonal_precomp_W_bijective _ hY s hs).1 eq
  · intro g
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L S.trW g
    obtain ⟨h, H⟩ := (S.rightOrthogonal_precomp_W_bijective _ hY φ.s φ.hs).2 φ.f
    dsimp at H
    refine ⟨h, ?_⟩
    have := Localization.inverts L S.trW φ.s φ.hs
    rw [hφ, ← cancel_epi (L.map φ.s), MorphismProperty.RightFraction.map_s_comp_map, ← H,
      Functor.map_comp]

end ObjectProperty

end CategoryTheory
