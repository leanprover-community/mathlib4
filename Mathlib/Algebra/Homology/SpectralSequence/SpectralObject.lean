import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
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

-- the homology of this short complex gives the terms in all the pages of the spectral sequence
def shortComplexE' : ShortComplex (Arrow₃ ι ⥤ C) where
  X₁ := Arrow₃.hMor ⋙ X.H n₀
  X₂ := Arrow₃.gMor ⋙ X.H n₁
  X₃ := Arrow₃.fMor ⋙ X.H n₂
  f := whiskerLeft (Arrow₃.δ₀) (X.δ n₀ n₁ hn₁)
  g := whiskerLeft (Arrow₃.δ₃) (X.δ n₁ n₂ hn₂)
  zero := by
    ext D
    have eq := (X.δ n₁ n₂ hn₂).naturality (Arrow₃.δ₃Toδ₂.app D)
    dsimp at eq ⊢
    simp only [Arrow₃.δ₂_map_δ₃Toδ₂_app, Arrow₂.δ₂_obj, Arrow₃.δ₃_obj_f,
      Functor.map_id, comp_id] at eq
    rw [← eq, Arrow₃.δ₀_map_δ₃Toδ₂_app_eq_δ₂Toδ₁_app_δ₀_obj,
      reassoc_of% (X.zero₁ n₀ n₁ hn₁ (Arrow₃.δ₀.obj D)), zero_comp]

section

variable (n₀ n₁ n₂ : ℤ) (h : n₀ + 1 = n₁) (h' : n₁ + 1 = n₂) (D : Arrow₂ ι)

noncomputable def cycles : Arrow₂ ι ⥤ C := kernel (X.δ n₀ n₁ h)
noncomputable def cyclesCo : Arrow₂ ι ⥤ C := cokernel (X.δ n₀ n₁ h)

noncomputable def iCycles : X.cycles n₀ n₁ h ⟶ Arrow₂.δ₀ ⋙ X.H n₀ := kernel.ι _
noncomputable def pCyclesCo : Arrow₂.δ₂ ⋙ X.H n₁ ⟶ X.cyclesCo n₀ n₁ h := cokernel.π _

lemma iCycles_δ_app : (X.iCycles n₀ n₁ h).app D ≫ (X.δ n₀ n₁ h).app D = 0 := by
  simp only [← NatTrans.comp_app, iCycles, kernel.condition, zero_app]

lemma δ_pCyclesCo_app : (X.δ n₀ n₁ h).app D ≫ (X.pCyclesCo n₀ n₁ h).app D  = 0 := by
  simp only [← NatTrans.comp_app, pCyclesCo, cokernel.condition, zero_app]

noncomputable def isLimitCycles (D : Arrow₂ ι) :
    IsLimit (KernelFork.ofι _ (X.iCycles_δ_app n₀ n₁ h D)) :=
  KernelFork.mapIsLimit _ (kernelIsKernel (X.δ n₀ n₁ h)) ((evaluation _ _).obj D)

noncomputable def isColimitCyclesCo (D : Arrow₂ ι) :
    IsColimit (CokernelCofork.ofπ _ (X.δ_pCyclesCo_app n₀ n₁ h D)) :=
  CokernelCofork.mapIsColimit _ (cokernelIsCokernel (X.δ n₀ n₁ h)) ((evaluation _ _).obj D)

end

end SpectralObject

end Abelian

end CategoryTheory
