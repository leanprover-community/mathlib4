/-
Copyright (c) 2026 Tabei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tabei
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.LDL
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Real.Sqrt

/-!
# Simultaneous diagonalization of two real quadratic forms

If `A` is a positive definite real matrix and `B` is a symmetric real matrix, then a single
congruence takes `A` to the identity and `B` to a diagonal matrix. Equivalently, two real
quadratic forms, one of which is positive definite, can be diagonalized simultaneously.

## Main results

* `Matrix.PosDef.exists_simultaneous_diagonalization`: there is an invertible `P` with
  `Pᵀ * A * P = 1` and `Pᵀ * B * P` diagonal.

## Implementation notes

The classical argument replaces `A` by its square root. Instead we use the LDL decomposition
of `A`, which produces an invertible `L` with `L * A * Lᴴ` diagonal with positive entries, and
then rescale the rows by the inverse square roots of those entries to reach the identity. The
resulting congruence of `B` is again symmetric, so the spectral theorem finishes the proof.
-/

@[expose] public section

open Matrix Unitary

namespace Matrix

variable {n : Type*} [Fintype n] [LinearOrder n] [WellFoundedLT n] [LocallyFiniteOrderBot n]

/-- Rescaling a positive real by the inverse of its square root on both sides gives `1`. -/
private lemma inv_sqrt_mul_mul_inv_sqrt {x : ℝ} (hx : 0 < x) :
    (Real.sqrt x)⁻¹ * x * (Real.sqrt x)⁻¹ = 1 := by
  have h : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr hx
  field_simp
  exact (Real.sq_sqrt hx.le).symm

/-- **Simultaneous diagonalization of two real quadratic forms.** If `A` is positive definite
and `B` is symmetric, then some invertible matrix `P` satisfies `Pᵀ * A * P = 1` and takes `B`
to a diagonal matrix by congruence. -/
theorem PosDef.exists_simultaneous_diagonalization {A B : Matrix n n ℝ} (hA : A.PosDef)
    (hB : B.IsSymm) :
    ∃ P : Matrix n n ℝ, IsUnit P.det ∧ Pᵀ * A * P = 1 ∧ ∃ d : n → ℝ, Pᵀ * B * P = diagonal d := by
  classical
  -- The LDL decomposition makes `L * A * Lᴴ` diagonal with positive entries.
  set L : Matrix n n ℝ := LDL.lowerInv hA with hLdef
  have hLunit : IsUnit L := isUnit_of_invertible L
  have hdiag : L * A * Lᴴ = diagonal (LDL.diagEntries hA) :=
    (LDL.diag_eq_lowerInv_conj hA).symm
  have hDpos : (diagonal (LDL.diagEntries hA)).PosDef := by
    rw [← hdiag]
    exact hA.mul_mul_conjTranspose_same (vecMul_injective_iff_isUnit.mpr hLunit)
  have hd : ∀ i, 0 < LDL.diagEntries hA i := posDef_diagonal_iff.mp hDpos
  have hsq : ∀ i, Real.sqrt (LDL.diagEntries hA i) ≠ 0 := fun i => Real.sqrt_ne_zero'.mpr (hd i)
  -- Rescaling the rows by `1 / √dᵢ` turns `A` into the identity.
  set e : n → ℝ := fun i => (Real.sqrt (LDL.diagEntries hA i))⁻¹ with hedef
  set W : Matrix n n ℝ := diagonal e * L with hWdef
  have hLt : Lᵀ = Lᴴ := (conjTranspose_eq_transpose_of_trivial L).symm
  have hWt : Wᵀ = Wᴴ := (conjTranspose_eq_transpose_of_trivial W).symm
  have hone : (fun i => e i * LDL.diagEntries hA i * e i) = fun _ => (1 : ℝ) := by
    funext i
    simp only [hedef]
    exact inv_sqrt_mul_mul_inv_sqrt (hd i)
  have hWA : W * A * Wᵀ = 1 := by
    rw [hWdef, transpose_mul, diagonal_transpose, hLt,
      show diagonal e * L * A * (Lᴴ * diagonal e)
        = diagonal e * (L * A * Lᴴ) * diagonal e by simp only [mul_assoc],
      hdiag, diagonal_mul_diagonal, diagonal_mul_diagonal, hone, diagonal_one]
  -- The congruence of `B` is symmetric, so the spectral theorem diagonalizes it.
  have hBher : B.IsHermitian := by
    change Bᴴ = B
    rw [conjTranspose_eq_transpose_of_trivial]
    exact hB
  have hC : (W * B * Wᴴ).IsHermitian := isHermitian_mul_mul_conjTranspose W hBher
  have hspec := hC.spectral_theorem
  rw [conjStarAlgAut_apply] at hspec
  set V : Matrix n n ℝ := ↑(hC.eigenvectorUnitary) with hVdef
  have hstar : star V = Vᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  rw [hstar] at hspec
  have hV1 : Vᵀ * V = 1 := by
    have h := Unitary.coe_star_mul_self hC.eigenvectorUnitary
    rwa [← hVdef, hstar] at h
  -- `P = Wᵀ * V` diagonalizes both forms at once.
  refine ⟨Wᵀ * V, ?_, ?_, RCLike.ofReal ∘ hC.eigenvalues, ?_⟩
  · have hdetV : IsUnit V.det := by
      have h : Vᵀ.det * V.det = 1 := by rw [← det_mul, hV1, det_one]
      exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one h)
    have hLdet : IsUnit L.det :=
      letI : Invertible L := LDL.invertibleLowerInv hA
      isUnit_det_of_invertible L
    have hEdet : IsUnit (diagonal e).det := by
      rw [det_diagonal]
      refine isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
      simp only [hedef]
      exact inv_ne_zero (hsq i)
    have hdetW : IsUnit W.det := by
      rw [hWdef, det_mul]
      exact hEdet.mul hLdet
    rw [det_mul, det_transpose]
    exact hdetW.mul hdetV
  · rw [transpose_mul, transpose_transpose,
      show Vᵀ * W * A * (Wᵀ * V) = Vᵀ * (W * A * Wᵀ) * V by simp only [mul_assoc],
      hWA, mul_one, hV1]
  · rw [transpose_mul, transpose_transpose,
      show Vᵀ * W * B * (Wᵀ * V) = Vᵀ * (W * B * Wᵀ) * V by simp only [mul_assoc], hWt]
    conv_lhs => rw [hspec]
    rw [show Vᵀ * (V * diagonal (RCLike.ofReal ∘ hC.eigenvalues) * Vᵀ) * V
        = (Vᵀ * V) * diagonal (RCLike.ofReal ∘ hC.eigenvalues) * (Vᵀ * V) by
          simp only [mul_assoc],
      hV1, one_mul, mul_one]

end Matrix
