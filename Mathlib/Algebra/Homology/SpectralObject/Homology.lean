/-
Copyright (c) 2026 Joël Riou. All rights reserved.
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

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (n₀ n₁ n₂ n₃ : ℤ)

/-- The (exact) sequence expressing `E^n(f₁, f₂, f₃ ≫ f₄)` as the cokernel
of the differential `E^{n-1}(f₃, f₄, f₅) ⟶ E^n(f₁, f₂, f₃)` -/
@[simps!]
noncomputable def dCokernelSequence
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.d_map_fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₅ f₃₄ h₃₄ n₀ n₁ n₂ n₃)

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) :
    Epi (X.dCokernelSequence f₁ f₂ f₃ f₄ f₅ f₃₄ h₃₄ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃).g :=
  inferInstanceAs (Epi (X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) ..))

set_option backward.isDefEq.respectTransparency false in
lemma dCokernelSequence_exact
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    (X.dCokernelSequence f₁ f₂ f₃ f₄ f₅ f₃₄ h₃₄ n₀ n₁ n₂ n₃).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at hx₂ ⊢
  have hx₂' := hx₂ =≫ X.ιE ..
  simp only [assoc, zero_comp] at hx₂'
  rw [X.map_ιE f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄)
    (threeδ₃Toδ₂ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃] at hx₂'
  obtain ⟨A₁, π₁, _, x₁, hx₁⟩ :=
    ((X.sequenceΨ_exact f₂ f₃ f₄ _ rfl f₃₄ h₃₄ n₁ n₂).exact 1).exact_up_to_refinements
      (x₂ ≫ X.ιE ..) (by dsimp [sequenceΨ, Precomp.map]; rw [assoc, hx₂'])
  dsimp [sequenceΨ, Precomp.map] at hx₁
  refine ⟨A₁, π₁, inferInstance, x₁ ≫ X.πE f₃ f₄ f₅ n₀ n₁ n₂, ?_⟩
  rw [← cancel_mono (X.ιE ..), assoc, assoc, assoc, hx₁, πE_d_ιE ..]

/-- The (exact) sequence expressing `E^n(f₂ ≫ f₃, f₄, f₅)` as the kernel
of the differential `E^n(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)` -/
@[simps!]
noncomputable def dKernelSequence
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.map_fourδ₁Toδ₀_d f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃)

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) :
    Mono (X.dKernelSequence f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃).f :=
  inferInstanceAs (Mono (X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) ..))

set_option backward.isDefEq.respectTransparency false in
lemma dKernelSequence_exact
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    (X.dKernelSequence f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp at hx₂ ⊢
  obtain ⟨A₁, π₁, _, y₂, hy₂⟩ :=
    surjective_up_to_refinements_of_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂) x₂
  have hy₂' := hy₂ =≫ X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ ≫ X.ιE ..
  simp only [assoc, reassoc_of% hx₂, zero_comp, comp_zero, πE_d_ιE] at hy₂'
  obtain ⟨A₂, π₂, _, y₁, hy₁⟩ :=
    ((X.sequenceΨ_exact f₂ f₃ f₄ f₂₃ h₂₃ _ rfl n₁ n₂).exact 0).exact_up_to_refinements y₂ hy₂'.symm
  dsimp [sequenceΨ] at y₁ hy₁
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, y₁ ≫ X.πE f₂₃ f₄ f₅ n₀ n₁ n₂, ?_⟩
  simp [hy₂, reassoc_of% hy₁, X.πE_map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃)
    (threeδ₁Toδ₀ f₂ f₃ f₄ f₂₃ h₂₃) n₀ n₁ n₂]

end

variable {i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅) (f₆ : i₅ ⟶ i₆) (f₇ : i₆ ⟶ i₇)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₅₆ : i₄ ⟶ i₆) (h₅₆ : f₅ ≫ f₆ = f₅₆)
  (n₀ n₁ n₂ n₃ n₄ : ℤ)

/-- The short complex `E^{n₁}(f₅, f₆, f₇) ⟶ E^{n₀}(f₃, f₄, f₅) ⟶ E^{n₂}(f₁, f₂, f₃)`
given by the differentials of a spectral object. -/
@[simps!]
noncomputable def dShortComplex
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) (hn₄ : n₃ + 1 = n₄ := by lia) :
    ShortComplex C :=
  ShortComplex.mk _ _ (X.d_d f₁ f₂ f₃ f₄ f₅ f₆ f₇ n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma map_fourδ₁Toδ₀_EMap_fourδ₄Toδ₃
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₁ n₂ n₃ hn₂ hn₃ ≫
      X.map f₃ f₄ f₅ f₃ f₄ f₅₆ (fourδ₄Toδ₃ f₃ f₄ f₅ f₆ f₅₆ h₅₆) n₁ n₂ n₃ hn₂ hn₃ =
    X.map f₂₃ f₄ f₅ f₂₃ f₄ f₅₆ (fourδ₄Toδ₃ f₂₃ f₄ f₅ f₆ f₅₆ h₅₆) n₁ n₂ n₃ hn₂ hn₃ ≫
      X.map f₂₃ f₄ f₅₆ f₃ f₄ f₅₆ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅₆ f₂₃ h₂₃) n₁ n₂ n₃ hn₂ hn₃ := by
  simp only [← map_comp]
  cat_disch

set_option backward.isDefEq.respectTransparency false in
/-- The homology data of the short complex
`E^{n-1}(f₅, f₆, f₇) ⟶ E^{n}(f₃, f₄, f₅) ⟶ E^{n+1}(f₁, f₂, f₃)` for which
* the cycles are `E^n(f₂ ≫ f₃, f₄, f₅)`;
* the opcycles are `E^n(f₃, f₄, f₅ ≫ f₆)`;
* the homology is `E^n(f₂ ≫ f₃, f₄, f₅ ≫ f₆)`. -/
@[simps!]
noncomputable def dHomologyData
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) (hn₄ : n₃ + 1 = n₄ := by lia) :
    (X.dShortComplex f₁ f₂ f₃ f₄ f₅ f₆ f₇ n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄ ).HomologyData :=
  ShortComplex.HomologyData.ofEpiMonoFactorisation
    (X.dShortComplex f₁ f₂ f₃ f₄ f₅ f₆ f₇ n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄)
    (X.dKernelSequence_exact f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ n₁ n₂ n₃ n₄ hn₂ hn₃ hn₄).fIsKernel
    (X.dCokernelSequence_exact f₃ f₄ f₅ f₆ f₇ f₅₆ h₅₆ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃).gIsCokernel
    (X.map_fourδ₁Toδ₀_EMap_fourδ₄Toδ₃ f₂ f₃ f₄ f₅ f₆ f₂₃ h₂₃ f₅₆ h₅₆ n₁ n₂ n₃ hn₂ hn₃)

/-- The homology of the short complex
`E^{n₁}(f₅, f₆, f₇) ⟶ E^{n₀}(f₃, f₄, f₅) ⟶ E^{n₂}(f₁, f₂, f₃)` identifies to
`E^n(f₂ ≫ f₃, f₄, f₅ ≫ f₆)`. -/
noncomputable def dHomologyIso
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) (hn₄ : n₃ + 1 = n₄ := by lia) :
    (X.dShortComplex f₁ f₂ f₃ f₄ f₅ f₆ f₇ n₀ n₁ n₂ n₃ n₄ hn₁ hn₂ hn₃ hn₄).homology ≅
      X.E f₂₃ f₄ f₅₆ n₁ n₂ n₃ hn₂ hn₃ :=
  (X.dHomologyData f₁ f₂ f₃ f₄ f₅ f₆ f₇ f₂₃ h₂₃ f₅₆ h₅₆ ..).left.homologyIso

end SpectralObject

end Abelian

end CategoryTheory
