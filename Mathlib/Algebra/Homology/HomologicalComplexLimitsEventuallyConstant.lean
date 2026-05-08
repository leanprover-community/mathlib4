/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Limits of degreewise eventually constant systems

Let `F : J ⥤ HomologicalComplex C c` be a functor from a cofiltered category
such that for any degree `q`, the functor `F ⋙ eval C c q : J ⥤ C` is
eventually constant. Let `cF` be a limit cone for `F`. For a given degree `q`,
we show that for suitable `j : J`, the map `(cF.π.app j).f q` is an
isomorphism, and that `cf.π.app j` is a quasi-isomorphism in degree `q`.

-/

public section

open CategoryTheory Category Limits

variable {C J ι : Type*} [Category C] [Category J]
   {c : ComplexShape ι} [IsCofiltered J]

namespace HomologicalComplex

variable [HasZeroMorphisms C] (F : J ⥤ HomologicalComplex C c)
  [∀ (j : ι), HasLimit (F ⋙ eval C c j)]
  {cF : Cone F} (hcF : IsLimit cF)

include hcF

lemma isIso_π_f_of_isLimit_of_isEventuallyConstantTo
    (q : ι) (j : J) (hq : (F ⋙ eval C c q).IsEventuallyConstantTo j) :
    IsIso ((cF.π.app j).f q) :=
  hq.isIso_π_of_isLimit (isLimitOfPreserves (eval C c q) hcF)

lemma quasiIsoAt_π_of_isLimit_of_isEventuallyConstantTo
    [CategoryWithHomology C] (q₀ q₁ q₂ : ι)
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

end HomologicalComplex
