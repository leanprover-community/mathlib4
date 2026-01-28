/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.EpiMono

/-!
# The homology of the differentials of a spectral object

Let `X` be a spectral object indexed by a category `ι` in an abelian
category `C`. Assume we have seven composable arrows
`f₁`, `f₂`, `f₃`, `f₄`, `f₅`, `f₆`, `f₇` in `ι`. In this file,
we compute the homology of the differentials, i.e. the homology of the short complex
`E^{n - 1}(f₅, f₆, f₇) ⟶ E^n(f₃, f₄, f₅) ⟶ E^{n + 1}(f₁, f₂, f₃)`.
The main definition for this is `dHomologyData` which is an homology data
for this short complex where:
* the cycles are `E^n(f₂ ≫ f₃, f₄, f₅)`;
* the opcycles are `E^n(f₃, f₄, f₅ ≫ f₆)`;
* the homology is `E^n(f₂ ≫ f₃, f₄, f₅ ≫ f₆)`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ComposableArrows Preadditive

namespace Abelian

variable {C ι : Type*} [Category C] [Abelian C] [Category ι]

namespace SpectralObject

variable (X : SpectralObject C ι)

section

variable (n₀ n₁ n₂ n₃ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃)
  {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)

/-- The (exact) sequence expressing `E^n(f₁, f₂, f₃ ≫ f₄)` as the cokernel
of the differential `E^{n-1}(f₃, f₄, f₅) ⟶ E^n(f₁, f₂, f₃)` -/
@[simps!]
noncomputable def dCokernelSequence : ShortComplex C :=
  ShortComplex.mk _ _ (X.d_EMap_fourδ₄Toδ₃ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ f₃₄ h₃₄)

instance : Epi (X.dCokernelSequence n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ f₃₄ h₃₄).g := by
  dsimp
  infer_instance

lemma dCokernelSequence_exact :
    (X.dCokernelSequence n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ f₃₄ h₃₄).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂ ⊢
  have hx₂' := hx₂ =≫ X.ιE _ _ _ _ _ _ _ _
  simp only [assoc, zero_comp] at hx₂'
  rw [X.EMap_ιE n₁ n₂ n₃ hn₂ hn₃ f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄)
    (threeδ₃Toδ₂ f₂ f₃ f₄ f₃₄ h₃₄) (by cat_disch)] at hx₂'
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    ((X.sequenceΨ_exact n₁ n₂ hn₂ f₂ f₃ f₄ _ rfl
      f₃₄ h₃₄).exact 1).exact_up_to_refinements (x₂ ≫ X.ιE _ _ _ _ _ _ _ _) (by
        dsimp [sequenceΨ, Precomp.map]
        rw [assoc, hx₂'])
  dsimp [sequenceΨ, Precomp.map] at x₁ hx₁
  refine ⟨A₁, π₁, inferInstance, x₁ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₃ f₄ f₅, ?_⟩
  rw [← cancel_mono (X.ιE _ _ _ _ _ _ _ _), assoc, assoc, assoc, hx₁, πE_d_ιE]

/-- The (exact) sequence expressing `E^n(f₂ ≫ f₃, f₄, f₅)` as the kernel
of the differential `E^n(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)` -/
@[simps!]
noncomputable def dKernelSequence : ShortComplex C :=
  ShortComplex.mk _ _ (X.EMap_fourδ₁Toδ₀_d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃)

instance : Mono (X.dKernelSequence n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃).f := by
  dsimp
  infer_instance

lemma dKernelSequence_exact :
    (X.dKernelSequence n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at x₂ hx₂ ⊢
  obtain ⟨A₁, π₁, _, y₂, hy₂⟩ :=
    surjective_up_to_refinements_of_epi (X.πE n₀ n₁ n₂ hn₁ hn₂ f₃ f₄ f₅) x₂
  have hy₂' := hy₂ =≫ (X.d n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₁ f₂ f₃ f₄ f₅ ≫ X.ιE _ _ _ _ _ _ _ _)
  simp only [assoc, reassoc_of% hx₂, zero_comp, comp_zero, πE_d_ιE] at hy₂'
  obtain ⟨A₂, π₂, _, y₁, hy₁⟩ :=
    ((X.sequenceΨ_exact n₁ n₂ hn₂ f₂ f₃ f₄
      f₂₃ h₂₃ _ rfl).exact 0).exact_up_to_refinements y₂ hy₂'.symm
  dsimp [sequenceΨ] at y₁ hy₁
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, y₁ ≫ X.πE n₀ n₁ n₂ hn₁ hn₂ f₂₃ f₄ f₅, ?_⟩
  rw [assoc, assoc, hy₂, reassoc_of% hy₁,
    X.πE_EMap n₀ n₁ n₂ hn₁ hn₂ f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃)
    (threeδ₁Toδ₀ f₂ f₃ f₄ f₂₃ h₂₃) (by ext <;> simp; rfl)]

end

variable (n₀ n₁ n₂ n₃ n₄ : ℤ)
  (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) (hn₄ : n₃ + 1 = n₄)
  {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₆ : i₅ ⟶ i₆) (f₇ : i₆ ⟶ i₇)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₅₆ : i₄ ⟶ i₆) (h₅₆ : f₅ ≫ f₆ = f₅₆)

/-- The short complex `E^{n₁}(f₅, f₆, f₇) ⟶ E^{n₀}(f₃, f₄, f₅) ⟶ E^{n₂}(f₁, f₂, f₃)`
given by the differentials of a spectral object. -/
@[simps!]
noncomputable def dShortComplex : ShortComplex C :=
  ShortComplex.mk _ _ (X.d_d n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄ f₁ f₂ f₃ f₄ f₅ f₆ f₇)

@[reassoc]
lemma EMap_fourδ₁Toδ₀_EMap_fourδ₄Toδ₃ :
    X.EMap n₁ n₂ n₃ hn₂ hn₃ f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) ≫
      X.EMap n₁ n₂ n₃ hn₂ hn₃ f₃ f₄ f₅ f₃ f₄ f₅₆ (fourδ₄Toδ₃ f₃ f₄ f₅ f₆ f₅₆ h₅₆) =
    X.EMap n₁ n₂ n₃ hn₂ hn₃ f₂₃ f₄ f₅ f₂₃ f₄ f₅₆ (fourδ₄Toδ₃ f₂₃ f₄ f₅ f₆ f₅₆ h₅₆) ≫
      X.EMap n₁ n₂ n₃ hn₂ hn₃ f₂₃ f₄ f₅₆ f₃ f₄ f₅₆ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅₆ f₂₃ h₂₃) := by
  simp only [← EMap_comp]
  congr 1
  ext <;> simp

/-- The homology data of the short complex
`E^{n-1}(f₅, f₆, f₇) ⟶ E^{n}(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)` for which
* the cycles are `E^n(f₂ ≫ f₃, f₄, f₅)`;
* the opcycles are `E^n(f₃, f₄, f₅ ≫ f₆)`;
* the homology is `E^n(f₂ ≫ f₃, f₄, f₅ ≫ f₆)`. -/
@[simps!]
noncomputable def dHomologyData :
    (X.dShortComplex n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄ f₁ f₂ f₃ f₄ f₅ f₆ f₇).HomologyData :=
  ShortComplex.HomologyData.ofEpiMonoFactorisation
    (X.dShortComplex n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄ f₁ f₂ f₃ f₄ f₅ f₆ f₇)
    (X.dKernelSequence_exact n₁ n₂ n₃ n₄ hn₂ hn₃ hn₄ f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃).fIsKernel
    (X.dCokernelSequence_exact n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ f₃ f₄ f₅ f₆ f₇ f₅₆ h₅₆).gIsCokernel
    (X.EMap_fourδ₁Toδ₀_EMap_fourδ₄Toδ₃ n₁ n₂ n₃ hn₂ hn₃ f₂ f₃ f₄ f₅ f₆ f₂₃ h₂₃ f₅₆ h₅₆)

/-- The homology of the short complex
`E^{n₁}(f₅, f₆, f₇) ⟶ E^{n₀}(f₃, f₄, f₅) ⟶ E^{n₂}(f₁, f₂, f₃)` identifies to
`E^n(f₂ ≫ f₃, f₄, f₅ ≫ f₆)`. -/
noncomputable def dHomologyIso :
    (X.dShortComplex n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄ f₁ f₂ f₃ f₄ f₅ f₆ f₇).homology ≅
      X.E n₁ n₂ n₃ hn₂ hn₃ f₂₃ f₄ f₅₆ :=
  (X.dHomologyData n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄
    f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₂₃ h₂₃ f₅₆ h₅₆).left.homologyIso

end SpectralObject

end Abelian

end CategoryTheory
