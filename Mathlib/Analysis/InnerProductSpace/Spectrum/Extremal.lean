/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Extremal eigenvectors in finite dimension

A unit eigenvector attains the largest absolute eigenvalue of a symmetric linear map.
-/

@[expose] public section

noncomputable section

namespace LinearMap.SymmetricSpectrum

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [Nontrivial H]

theorem exists_max_abs_eigenvalue_index (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) :
    ∃ i : Fin (Module.finrank ℂ H),
      ∀ j : Fin (Module.finrank ℂ H),
        |hK.eigenvalues rfl j| ≤ |hK.eigenvalues rfl i| := by
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℂ H))).Nonempty := by
    exact ⟨⟨0, Module.finrank_pos⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_max_image
      (Finset.univ : Finset (Fin (Module.finrank ℂ H)))
      (fun j => |hK.eigenvalues rfl j|) hne
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

/-- An index maximizing the absolute value of the spectral-theorem eigenvalues. -/
def maxAbsEigenvalueIndex (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) :
    Fin (Module.finrank ℂ H) :=
  (exists_max_abs_eigenvalue_index K hK).choose

/-- An eigenvalue with maximal absolute value. -/
def maxAbsEigenvalue (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) : ℝ :=
  hK.eigenvalues rfl (maxAbsEigenvalueIndex K hK)

/-- The absolute value of a maximal eigenvalue. -/
def maxEigenvalueNorm (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) : ℝ :=
  |maxAbsEigenvalue K hK|

/-- A unit eigenvector for a maximal eigenvalue. -/
def maxEigenvalueVector (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) : H :=
  hK.eigenvectorBasis rfl (maxAbsEigenvalueIndex K hK)

theorem abs_eigenvalue_le_maxEigenvalueNorm
    (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric)
    (j : Fin (Module.finrank ℂ H)) :
    |hK.eigenvalues rfl j| ≤ maxEigenvalueNorm K hK := by
  exact (exists_max_abs_eigenvalue_index K hK).choose_spec j

theorem maxEigenvalueNorm_nonneg (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) :
    0 ≤ maxEigenvalueNorm K hK :=
  abs_nonneg _

theorem norm_maxEigenvalueVector (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) :
    ‖maxEigenvalueVector K hK‖ = 1 := by
  exact (hK.eigenvectorBasis rfl).orthonormal.norm_eq_one (maxAbsEigenvalueIndex K hK)

theorem apply_maxEigenvalueVector (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) :
    K (maxEigenvalueVector K hK) =
      (maxAbsEigenvalue K hK : ℂ) • maxEigenvalueVector K hK := by
  exact hK.apply_eigenvectorBasis rfl (maxAbsEigenvalueIndex K hK)

theorem norm_apply_le_maxEigenvalueNorm_mul
    (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) (v : H) :
    ‖K v‖ ≤ maxEigenvalueNorm K hK * ‖v‖ := by
  let hn : Module.finrank ℂ H = Module.finrank ℂ H := rfl
  have hKv_sq :
      ‖K v‖ ^ 2 =
        ∑ i : Fin (Module.finrank ℂ H),
          ‖(hK.eigenvalues hn i : ℂ) *
            ((hK.eigenvectorBasis hn).repr v i)‖ ^ 2 := by
    calc
      ‖K v‖ ^ 2 = ‖(hK.eigenvectorBasis hn).repr (K v)‖ ^ 2 := by
        rw [(hK.eigenvectorBasis hn).repr.norm_map]
      _ = ∑ i : Fin (Module.finrank ℂ H),
          ‖(hK.eigenvectorBasis hn).repr (K v) i‖ ^ 2 :=
        EuclideanSpace.norm_sq_eq _
      _ = ∑ i : Fin (Module.finrank ℂ H),
          ‖(hK.eigenvalues hn i : ℂ) *
            ((hK.eigenvectorBasis hn).repr v i)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
          (hK.eigenvectorBasis_apply_self_apply hn v i)
  have hsum_le :
      (∑ i : Fin (Module.finrank ℂ H),
          ‖(hK.eigenvalues hn i : ℂ) *
            ((hK.eigenvectorBasis hn).repr v i)‖ ^ 2) ≤
        ∑ i : Fin (Module.finrank ℂ H),
          maxEigenvalueNorm K hK ^ 2 *
            ‖(hK.eigenvectorBasis hn).repr v i‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    have hi := abs_eigenvalue_le_maxEigenvalueNorm K hK i
    have hi' :
        |hK.eigenvalues hn i| ≤ maxEigenvalueNorm K hK := by
      simpa only using hi
    have hi_nonneg : 0 ≤ |hK.eigenvalues hn i| := abs_nonneg _
    have hR_nonneg := maxEigenvalueNorm_nonneg K hK
    have hi_sq :
        |hK.eigenvalues hn i| ^ 2 ≤ maxEigenvalueNorm K hK ^ 2 := by
      nlinarith [hi']
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow] using
      mul_le_mul_of_nonneg_right hi_sq
        (sq_nonneg ‖(hK.eigenvectorBasis hn).repr v i‖)
  have hv_sq :
      (∑ i : Fin (Module.finrank ℂ H),
          maxEigenvalueNorm K hK ^ 2 *
            ‖(hK.eigenvectorBasis hn).repr v i‖ ^ 2) =
        maxEigenvalueNorm K hK ^ 2 * ‖v‖ ^ 2 := by
    rw [← Finset.mul_sum, ← EuclideanSpace.norm_sq_eq]
    rw [(hK.eigenvectorBasis hn).repr.norm_map]
  have hsq :
      ‖K v‖ ^ 2 ≤ (maxEigenvalueNorm K hK * ‖v‖) ^ 2 := by
    rw [hKv_sq, mul_pow]
    exact hsum_le.trans_eq hv_sq
  have hleft : 0 ≤ ‖K v‖ := norm_nonneg _
  have hright : 0 ≤ maxEigenvalueNorm K hK * ‖v‖ :=
    mul_nonneg (maxEigenvalueNorm_nonneg K hK) (norm_nonneg _)
  nlinarith

theorem norm_inner_apply_le_maxEigenvalueNorm
    (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric)
    (v : H) (hv : ‖v‖ = 1) :
    ‖@inner ℂ H _ v (K v)‖ ≤ maxEigenvalueNorm K hK := by
  calc
    ‖@inner ℂ H _ v (K v)‖ ≤ ‖v‖ * ‖K v‖ :=
      norm_inner_le_norm v (K v)
    _ ≤ ‖v‖ * (maxEigenvalueNorm K hK * ‖v‖) :=
      mul_le_mul_of_nonneg_left
        (norm_apply_le_maxEigenvalueNorm_mul K hK v) (norm_nonneg _)
    _ = maxEigenvalueNorm K hK := by rw [hv]; ring

theorem norm_inner_maxEigenvalueVector
    (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) :
    ‖@inner ℂ H _ (maxEigenvalueVector K hK) (K (maxEigenvalueVector K hK))‖ =
      maxEigenvalueNorm K hK := by
  rw [apply_maxEigenvalueVector K hK, inner_smul_right]
  rw [inner_self_eq_norm_sq_to_K, norm_maxEigenvalueVector K hK]
  simp [maxEigenvalueNorm, maxAbsEigenvalue]

theorem maxEigenvalueNorm_pos
    (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) (hK0 : K ≠ 0) :
    0 < maxEigenvalueNorm K hK := by
  have hR0 : maxEigenvalueNorm K hK ≠ 0 := by
    intro hR
    apply hK0
    ext v
    have hv := norm_apply_le_maxEigenvalueNorm_mul K hK v
    rw [hR, zero_mul] at hv
    exact norm_eq_zero.mp (le_antisymm hv (norm_nonneg _))
  exact lt_of_le_of_ne (maxEigenvalueNorm_nonneg K hK) (Ne.symm hR0)

/-- The extremal absolute eigenvalue agrees with the canonical operator norm. -/
theorem norm_toContinuousLinearMap (K : H →ₗ[ℂ] H) (hK : K.IsSymmetric) :
    ‖K.toContinuousLinearMap‖ = maxEigenvalueNorm K hK := by
  apply le_antisymm
  · exact K.toContinuousLinearMap.opNorm_le_bound (maxEigenvalueNorm_nonneg K hK)
      (norm_apply_le_maxEigenvalueNorm_mul K hK)
  · have h := K.toContinuousLinearMap.le_opNorm (maxEigenvalueVector K hK)
    change ‖K (maxEigenvalueVector K hK)‖ ≤ _ at h
    rw [apply_maxEigenvalueVector, norm_smul, norm_maxEigenvalueVector, mul_one] at h
    simpa [maxEigenvalueNorm, Complex.norm_real, Real.norm_eq_abs] using h

end LinearMap.SymmetricSpectrum
