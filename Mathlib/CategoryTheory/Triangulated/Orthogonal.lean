import Mathlib.CategoryTheory.Triangulated.Subcategory

namespace CategoryTheory

open Limits Pretriangulated Preadditive

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

variable (S : Subcategory C)

namespace Subcategory

def rightOrthogonal : Subcategory C := Subcategory.mk'
  (fun Y => ∀ ⦃X : C⦄ (f : X ⟶ Y), S.P X → f = 0)
  (by aesop_cat)
  (fun Y n hY X f hX => by
    have : f⟦-n⟧' ≫ (shiftEquiv C n).unitIso.inv.app Y = 0 := hY _ (S.shift _ _ hX)
    simp only [Preadditive.IsIso.comp_right_eq_zero] at this
    apply (shiftFunctor C (-n)).map_injective
    rw [this, Functor.map_zero])
  (fun T hT h₁ h₃ X f₂ hX => by
    obtain ⟨f₁, rfl⟩ := T.coyoneda_exact₂ hT f₂ (h₃ _ hX)
    rw [h₁ f₁ hX, zero_comp])

instance : ClosedUnderIsomorphisms S.rightOrthogonal.P := by
  dsimp only [rightOrthogonal]
  infer_instance

section

lemma rightOrthogonal_precomp_W_bijective (Z : C) (hZ : S.rightOrthogonal.P Z)
    {X Y : C} (w : X ⟶ Y) (hw : S.W w) :
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
    rw [W_iff'] at hw
    obtain ⟨U, f, g, H, mem⟩ := hw
    obtain ⟨u, hu⟩ := Triangle.yoneda_exact₂ _ H z (hZ _ mem)
    exact ⟨u, hu.symm⟩

variable [IsTriangulated C] {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization S.W]

lemma map_bijective_of_rightOrthogonal (X Y : C) (hY : S.rightOrthogonal.P Y) :
    Function.Bijective (L.map : (X ⟶ Y) → _) := by
  constructor
  · intros f₁ f₂ hf
    rw [MorphismProperty.map_eq_iff_precomp L S.W] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    exact (S.rightOrthogonal_precomp_W_bijective _ hY s hs).1 eq
  · intro g
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L S.W g
    obtain ⟨h, H⟩ := (S.rightOrthogonal_precomp_W_bijective _ hY φ.s φ.hs).2 φ.f
    dsimp at H
    refine' ⟨h, _⟩
    have := Localization.inverts L S.W φ.s φ.hs
    rw [hφ, ← cancel_epi (L.map φ.s), MorphismProperty.RightFraction.map_s_comp_map, ← H,
      Functor.map_comp]

end

end Subcategory

end Triangulated

end CategoryTheory
