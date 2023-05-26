import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.ArrowThree
import Mathlib.Tactic.Linarith

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

-- the homology of these short complexes gives the terms in all the pages of the spectral sequence
@[simps]
def shortComplexE' : Arrow₃ ι ⥤ ShortComplex C where
  obj D := ShortComplex.mk ((X.δ n₀ n₁ hn₁).app (Arrow₃.δ₀.obj D))
    ((X.δ n₁ n₂ hn₂).app (Arrow₃.δ₃.obj D)) (by
      have eq := (X.δ n₁ n₂ hn₂).naturality (Arrow₃.δ₃Toδ₂.app D)
      dsimp at eq
      simp only [Arrow₃.δ₂_map_δ₃Toδ₂_app, Arrow₂.δ₂_obj, Arrow₃.δ₃_obj_f,
        Functor.map_id, comp_id] at eq
      rw [← eq, Arrow₃.δ₀_map_δ₃Toδ₂_app_eq_δ₂Toδ₁_app_δ₀_obj,
        reassoc_of% (X.zero₁ n₀ n₁ hn₁ (Arrow₃.δ₀.obj D)), zero_comp])
  map φ :=
    { τ₁ := (X.H n₀).map (Arrow₃.hMor.map φ)
      τ₂ := (X.H n₁).map (Arrow₃.gMor.map φ)
      τ₃ := (X.H n₂).map (Arrow₃.fMor.map φ)
      comm₁₂ := (X.δ n₀ n₁ hn₁).naturality (Arrow₃.δ₀.map φ)
      comm₂₃ := (X.δ n₁ n₂ hn₂).naturality (Arrow₃.δ₃.map φ) }
  map_id _ := by ext <;> dsimp <;> simp
  map_comp _ _ := by ext <;> dsimp <;> simp

noncomputable def E := X.shortComplexE' n₀ n₁ n₂ hn₁ hn₂ ⋙ ShortComplex.homologyFunctor C

end SpectralObject

end Abelian

end CategoryTheory
