/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Limits of eventually constant systems

-/

@[expose] public section

open CategoryTheory Category Limits

variable {C J ι : Type*} [Category C] [Category J]
   {c : ComplexShape ι} [IsCofiltered J]

namespace HomologicalComplex

variable [HasZeroMorphisms C] (F : J ⥤ HomologicalComplex C c)
  [∀ (j : ι), HasLimit (F ⋙ eval C c j)]

lemma isIso_π_f_of_isLimit_of_isEventuallyConstantTo
    {cF : Cone F} (hcF : IsLimit cF)
    (q : ι) (j : J) (hq : (F ⋙ eval C c q).IsEventuallyConstantTo j) :
    IsIso ((cF.π.app j).f q) :=
  hq.isIso_π_of_isLimit (isLimitOfPreserves (eval C c q) hcF)

lemma isIso_limit_π_of_isEventuallyConstantTo
    (q : ι) (j : J) (hq : (F ⋙ eval C c q).IsEventuallyConstantTo j) :
    IsIso ((limit.π F j).f q) :=
  isIso_π_f_of_isLimit_of_isEventuallyConstantTo F (limit.isLimit _) q j hq

variable [CategoryWithHomology C]

lemma quasiIsoAt_π_of_isLimit_of_isEventuallyConstantTo
    {cF : Cone F} (hcF : IsLimit cF) (q₀ q₁ q₂ : ι)
    (h₀ : c.prev q₁ = q₀) (h₂ : c.next q₁ = q₂) (j : J)
    (hq₀ : (F ⋙ eval C c q₀).IsEventuallyConstantTo j)
    (hq₁ : (F ⋙ eval C c q₁).IsEventuallyConstantTo j)
    (hq₂ : (F ⋙ eval C c q₂).IsEventuallyConstantTo j) :
    QuasiIsoAt (cF.π.app j) q₁ := by
  rw [quasiIsoAt_iff' _ q₀ q₁ q₂ h₀ h₂]
  let φ := (shortComplexFunctor' C c q₀ q₁ q₂).map (cF.π.app j)
  have : IsIso φ.τ₁ := isIso_π_f_of_isLimit_of_isEventuallyConstantTo F hcF _ _ hq₀
  have : IsIso φ.τ₂ := isIso_π_f_of_isLimit_of_isEventuallyConstantTo F hcF _ _ hq₁
  have : IsIso φ.τ₃ := isIso_π_f_of_isLimit_of_isEventuallyConstantTo F hcF _ _ hq₂
  apply ShortComplex.quasiIso_of_epi_of_isIso_of_mono

lemma quasiIsoAt_limit_π_of_isEventuallyConstantTo
    (q₀ q₁ q₂ : ι) (h₀ : c.prev q₁ = q₀) (h₂ : c.next q₁ = q₂) (j : J)
    (hq₀ : (F ⋙ eval C c q₀).IsEventuallyConstantTo j)
    (hq₁ : (F ⋙ eval C c q₁).IsEventuallyConstantTo j)
    (hq₂ : (F ⋙ eval C c q₂).IsEventuallyConstantTo j) :
    QuasiIsoAt (limit.π F j) q₁ :=
  quasiIsoAt_π_of_isLimit_of_isEventuallyConstantTo F (limit.isLimit _)
    q₀ q₁ q₂ h₀ h₂ j hq₀ hq₁ hq₂

end HomologicalComplex
