/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-! # The Laplacian on Schwartz functions and tempered distributions -/

@[expose] public noncomputable section

variable {𝕜 E F : Type*}
  [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] --[NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] --[NormedSpace 𝕜 F]

namespace SchwartzMap

open Laplacian LineDeriv

variable (𝕜 E F) in
def laplacianCLM [NormedSpace 𝕜 F] : 𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  ∑ i, lineDerivOpCLM 𝕜 𝓢(E, F) (stdOrthonormalBasis ℝ E i) ∘L
    lineDerivOpCLM 𝕜 𝓢(E, F) (stdOrthonormalBasis ℝ E i)

theorem laplacianCLM_apply_eq_sum [NormedSpace 𝕜 F] (f : 𝓢(E, F)) : laplacianCLM 𝕜 E F f =
    ∑ i, ∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E i} f) := by
  simp [laplacianCLM]

instance instLaplacian : Laplacian 𝓢(E, F) 𝓢(E, F) where
  laplacian := laplacianCLM ℝ E F

private
theorem laplacianCLM_apply' (f : 𝓢(E, F)) : laplacianCLM ℝ E F f = Δ f := rfl

theorem laplacian_eq_sum (f : 𝓢(E, F)) :
    Δ f = ∑ i, ∂_{stdOrthonormalBasis ℝ E i} (∂_{stdOrthonormalBasis ℝ E i} f) := by
  simp [← laplacianCLM_apply', laplacianCLM]

@[simp]
theorem laplacianCLM_apply [NormedSpace 𝕜 F] (f : 𝓢(E, F)) : laplacianCLM 𝕜 E F f = Δ f := by
  rw [laplacian_eq_sum, laplacianCLM_apply_eq_sum]

open Classical in
@[simp]
theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → 𝓢(E, F)) (x : E) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  apply Finset.induction_on (motive := fun s ↦ (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x)
  · simp only [Finset.sum_empty, zero_apply]
  · intro i s his h
    simp only [his, not_false_eq_true, Finset.sum_insert, add_apply, h]

theorem laplacian_coe (f : 𝓢(E, F)) : Δ f = Δ (f : E → F) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, laplacian_eq_sum]
  ext x
  rw [sum_apply]
  congr 1
  ext i
  rw [← iteratedLineDerivOp_eq_iteratedFDeriv]
  rfl

end SchwartzMap
