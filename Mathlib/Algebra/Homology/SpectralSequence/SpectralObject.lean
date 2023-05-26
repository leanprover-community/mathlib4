import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.ArrowThree

open CategoryTheory Category Limits

variable (C ι : Type _) [Category C] [Abelian C] [Category ι]

namespace CategoryTheory

namespace Abelian

structure SpectralObject where
  H (n : ℤ) : Arrow ι ⥤ C
  δ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) : Arrow₂.δ₀ ⋙ H n₀ ⟶ Arrow₂.δ₂ ⋙ H n₁
  zero₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : Arrow₂ ι) :
    (δ n₀ n₁ h).app D ≫ (H n₁).map (Arrow₂.δ₂Toδ₁.app D) = 0
  zero₂ (n : ℤ) (D : Arrow₂ ι) :
    (H n).map (Arrow₂.δ₂Toδ₁.app D) ≫ (H n).map (Arrow₂.δ₁Toδ₀.app D) = 0
  zero₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : Arrow₂ ι) :
    (H n₀).map (Arrow₂.δ₁Toδ₀.app D) ≫ (δ n₀ n₁ h).app D = 0
  exact₁ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : Arrow₂ ι) :
    (ShortComplex.mk _ _ (zero₁ n₀ n₁ h D)).Exact
  exact₂ (n : ℤ) (D : Arrow₂ ι) :
    (ShortComplex.mk _ _ (zero₂ n D)).Exact
  exact₃ (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : Arrow₂ ι) :
    (ShortComplex.mk _ _ (zero₃ n₀ n₁ h D)).Exact

namespace SpectralObject

variable {C ι}
variable (X : SpectralObject C ι) (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)

/-def E : Arrow₃ ι ⥤ ShortComplex C where
  obj D := ShortComplex.mk ((X.δ n₀ n₁ hn₁).app (Arrow₃.δ₀.obj D))
    ((X.δ n₁ n₂ hn₂).app (Arrow₃.δ₃.obj D)) sorry
  map {D₁ D₂} φ :=
    { τ₁ := (X.H n₀).map (Arrow₃.hMor.map φ)
      τ₂ := (X.H n₁).map (Arrow₃.gMor.map φ)
      τ₃ := (X.H n₂).map (Arrow₃.fMor.map φ)
      comm₁₂ := (X.δ n₀ n₁ hn₁).naturality (Arrow₃.δ₀.map φ)
      comm₂₃ := (X.δ n₁ n₂ hn₂).naturality (Arrow₃.δ₃.map φ) }
  map_id := sorry
  map_comp := sorry-/

end SpectralObject

end Abelian

end CategoryTheory
