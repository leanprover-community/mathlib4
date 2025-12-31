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
  · simp
  · intro i s his h
    simp [his, h]

theorem coe_laplacian (f : 𝓢(E, F)) : ((Δ f : 𝓢(E, F)) : E → F) = Δ (f : E → F) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, laplacian_eq_sum]
  ext x
  rw [sum_apply]
  congr 1
  ext i
  rw [iteratedFDeriv_two_apply]
  rw [lineDerivOp_apply_eq_fderiv]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  congr
  ext v

  --rw [Finset.sum_apply]
  sorry

variable (f : Finset.range 4 → 𝓢(E, F))

theorem sum_apply (x : E) : (∑ i, f i) x = ∑ i, f i x := by rfl

end SchwartzMap
