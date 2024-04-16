import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.QuasiIso

open CategoryTheory Category Limits

variable {C J ι : Type*} [Category C] [Category J]
   {c : ComplexShape ι} [IsCofiltered J]

namespace HomologicalComplex

lemma isIso_π_f_of_isLimit_of_isEventuallyConstantTo
    [HasZeroMorphisms C] (F : J ⥤ HomologicalComplex C c)
    [∀ (j : ι), HasLimit (F ⋙ eval C c j)]
    {κ : Cone F} (hκ : IsLimit κ)
    (q : ι) (j : J) (hq : (F ⋙ eval C c q).IsEventuallyConstantTo j) :
    IsIso ((κ.π.app j).f q) :=
  hq.isIso_π_ofIsLimit (isLimitOfPreserves (eval C c q) hκ)

lemma isIso_limit_π_of_isEventuallyConstantTo
    [HasZeroMorphisms C] (F : J ⥤ HomologicalComplex C c)
    [∀ (j : ι), HasLimit (F ⋙ eval C c j)]
    (q : ι) (j : J) (hq : (F ⋙ eval C c q).IsEventuallyConstantTo j) :
    IsIso ((limit.π F j).f q) :=
  isIso_π_f_of_isLimit_of_isEventuallyConstantTo F (limit.isLimit _) q j hq

lemma quasiIsoAt_π_of_isLimit_of_isEventuallyConstantTo
    [HasZeroMorphisms C] [CategoryWithHomology C]
    (F : J ⥤ HomologicalComplex C c)
    [∀ (j : ι), HasLimit (F ⋙ eval C c j)]
    {κ : Cone F} (hκ : IsLimit κ) (q₀ q₁ q₂ : ι) (h₀ : c.prev q₁ = q₀) (h₂ : c.next q₁ = q₂) (j : J)
    (hq₀ : (F ⋙ eval C c q₀).IsEventuallyConstantTo j)
    (hq₁ : (F ⋙ eval C c q₁).IsEventuallyConstantTo j)
    (hq₂ : (F ⋙ eval C c q₂).IsEventuallyConstantTo j) :
    QuasiIsoAt (κ.π.app j) q₁ := by
  rw [quasiIsoAt_iff' _ q₀ q₁ q₂ h₀ h₂]
  have : IsIso ((shortComplexFunctor' C c q₀ q₁ q₂).map (κ.π.app j)).τ₁ :=
    isIso_π_f_of_isLimit_of_isEventuallyConstantTo F hκ _ _ hq₀
  have : IsIso ((shortComplexFunctor' C c q₀ q₁ q₂).map (κ.π.app j)).τ₂ :=
    isIso_π_f_of_isLimit_of_isEventuallyConstantTo F hκ _ _ hq₁
  have : IsIso ((shortComplexFunctor' C c q₀ q₁ q₂).map (κ.π.app j)).τ₃ :=
    isIso_π_f_of_isLimit_of_isEventuallyConstantTo F hκ _ _ hq₂
  apply ShortComplex.quasiIso_of_epi_of_isIso_of_mono

lemma quasiIsoAt_limit_π_of_isEventuallyConstantTo
    [HasZeroMorphisms C] [CategoryWithHomology C]
    (F : J ⥤ HomologicalComplex C c)
    [∀ (j : ι), HasLimit (F ⋙ eval C c j)]
    (q₀ q₁ q₂ : ι) (h₀ : c.prev q₁ = q₀) (h₂ : c.next q₁ = q₂) (j : J)
    (hq₀ : (F ⋙ eval C c q₀).IsEventuallyConstantTo j)
    (hq₁ : (F ⋙ eval C c q₁).IsEventuallyConstantTo j)
    (hq₂ : (F ⋙ eval C c q₂).IsEventuallyConstantTo j) :
    QuasiIsoAt (limit.π F j) q₁ :=
  quasiIsoAt_π_of_isLimit_of_isEventuallyConstantTo F (limit.isLimit _)
    q₀ q₁ q₂ h₀ h₂ j hq₀ hq₁ hq₂

end HomologicalComplex
