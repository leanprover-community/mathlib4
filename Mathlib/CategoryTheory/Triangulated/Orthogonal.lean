import Mathlib.CategoryTheory.Triangulated.Subcategory

namespace CategoryTheory

open Limits Pretriangulated Preadditive

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

variable (S : Subcategory C)

namespace Subcategory

def rightOrthogonal : Subcategory C := Subcategory.mk'
  (fun Y => ∀ ⦃X : C⦄ (f : X ⟶ Y), X ∈ S.set → f = 0)
  (by aesop_cat)
  (fun Y n hY X f hX => by
    have : f⟦-n⟧' ≫ (shiftEquiv C n).unitIso.inv.app Y = 0 := hY _ (S.shift _ _ hX)
    simp only [Preadditive.IsIso.comp_right_eq_zero] at this
    apply (shiftFunctor C (-n)).map_injective
    simpa only [Functor.map_zero] using this)
  (fun T hT h₁ h₃ X f₂ hX => by
    obtain ⟨f₁, rfl⟩ := T.coyoneda_exact₂ hT f₂ (h₃ _ hX)
    rw [h₁ f₁ hX, zero_comp])

instance : S.rightOrthogonal.set.RespectsIso := by
  dsimp only [rightOrthogonal]
  infer_instance

section

lemma rightOrthogonal_precomp_W_bijective (Z : C) (hZ : Z ∈ S.rightOrthogonal.set)
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
    rw [W_eq_W'] at hw
    obtain ⟨U, f, g, H, mem⟩ := hw
    obtain ⟨u, hu⟩ := Triangle.yoneda_exact₂ _ H z (hZ _ mem)
    exact ⟨u, hu.symm⟩

variable [IsTriangulated C] {D : Type*} [Category D] (L : C ⥤ D) [L.IsLocalization S.W]

lemma map_bijective_of_rightOrthogonal (X Y : C) (hY : Y ∈ S.rightOrthogonal.set) :
    Function.Bijective (L.map : (X ⟶ Y) → _) := by
  constructor
  · intros f₁ f₂ hf
    rw [MorphismProperty.HasRightCalculusOfFractions.map_eq_iff L S.W] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    exact (S.rightOrthogonal_precomp_W_bijective _ hY s hs).1 eq
  · intro g
    obtain ⟨Z, f, s, hs, eq⟩ := MorphismProperty.HasRightCalculusOfFractions.fac L S.W g
    obtain ⟨h, H⟩ := (S.rightOrthogonal_precomp_W_bijective _ hY s hs).2 f
    dsimp at H
    refine' ⟨h, _⟩
    simp only [eq, ← H, Functor.map_comp, Localization.isoOfHom_inv_hom_id_assoc]

end

end Subcategory

end Triangulated

end CategoryTheory
