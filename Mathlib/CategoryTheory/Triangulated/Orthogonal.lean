import Mathlib.CategoryTheory.Triangulated.Subcategory

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

variable (S : Subcategory C)

namespace Subcategory

def rightOrthogonal : Subcategory C where
  set Y := ∀ ⦃X : C⦄ (f : X ⟶ Y), X ∈ S.set → f = 0
  zero := by aesop_cat
  shift Y n hY X f hX := by
    have : f⟦-n⟧' ≫ (shiftEquiv C n).unitIso.inv.app Y = 0 := hY _ (S.shift _ _ hX)
    simp only [Preadditive.IsIso.comp_right_eq_zero] at this
    apply (shiftFunctor C (-n)).map_injective
    simpa only [Functor.map_zero] using this
  ext₂ T hT h₁ h₃ X f₂ hX := by
    obtain ⟨f₁, rfl⟩ := T.coyoneda_exact₂ hT f₂ (h₃ _ hX)
    rw [h₁ f₁ hX, zero_comp]

end Subcategory

end Triangulated

end CategoryTheory
