/-
Copyright (c) 2026 Moe Tabei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moe Tabei
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Simultaneous diagonalization of two real quadratic forms

If `A` is a positive definite real matrix and `B` is a symmetric real matrix, then a single
congruence takes `A` to the identity and `B` to a diagonal matrix. Equivalently, two real
quadratic forms, one of which is positive definite, can be diagonalized simultaneously.

## Main results

* `Matrix.PosDef.exists_simultaneous_diagonalization`: there is an invertible `P` with
  `Pᵀ * A * P = 1` and `Pᵀ * B * P` diagonal.
* `Matrix.PosDef.exists_simultaneous_diagonalization_quadratic`: the same statement read off
  on the quadratic forms themselves, as a change of variables taking `A` to `∑ xᵢ ^ 2` and
  `B` to `∑ dᵢ * xᵢ ^ 2`.
* `Matrix.PosDef.exists_simultaneous_diagonalization_of_posDef`: when `B` is positive definite
  as well, the resulting diagonal entries are positive.

## Implementation notes

Conjugating by the inverse of `CFC.sqrt A` turns `A` into the identity. The resulting congruence
of `B` is again symmetric, so `Matrix.IsHermitian.spectral_theorem` diagonalizes it by an
orthogonal matrix, and the two changes of basis compose.
-/

@[expose] public section

open Matrix Unitary
open scoped MatrixOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Simultaneous diagonalization of two real quadratic forms.** If `A` is positive definite
and `B` is symmetric, then some invertible matrix `P` satisfies `Pᵀ * A * P = 1` and takes `B`
to a diagonal matrix by congruence. -/
theorem PosDef.exists_simultaneous_diagonalization {A B : Matrix n n ℝ} (hA : A.PosDef)
    (hB : B.IsSymm) :
    ∃ P : Matrix n n ℝ, IsUnit P.det ∧ Pᵀ * A * P = 1 ∧ ∃ d : n → ℝ, Pᵀ * B * P = diagonal d := by
  classical
  -- The positive definite square root of `A` is invertible, and conjugating by its inverse
  -- turns `A` into the identity.
  set S : Matrix n n ℝ := CFC.sqrt A with hSdef
  have hSherm : S.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hdetS : IsUnit S.det := by
    have hprod : S.det * S.det = A.det := by rw [← det_mul, hSS]
    refine isUnit_iff_ne_zero.mpr fun h => hA.det_pos.ne' ?_
    rw [← hprod, h, zero_mul]
  set W : Matrix n n ℝ := S⁻¹ with hWdef
  have hSsymm : Sᵀ = S := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hSherm
  have hWsymm : Wᵀ = W := by rw [hWdef, transpose_nonsing_inv, hSsymm]
  have hWh : Wᴴ = W := by rw [conjTranspose_eq_transpose_of_trivial, hWsymm]
  have hWt : Wᵀ = Wᴴ := by rw [hWsymm, hWh]
  have hWA : W * A * Wᵀ = 1 := by
    rw [hWsymm, hWdef, ← hSS,
      show S⁻¹ * (S * S) * S⁻¹ = S⁻¹ * S * (S * S⁻¹) by simp only [mul_assoc],
      nonsing_inv_mul S hdetS, mul_nonsing_inv S hdetS, mul_one]
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
    have hdetW : IsUnit W.det := isUnit_nonsing_inv_det S hdetS
    rw [det_mul, det_transpose]
    exact hdetW.mul hdetV
  · rw [transpose_mul, transpose_transpose,
      show Vᵀ * W * A * (Wᵀ * V) = Vᵀ * (W * A * Wᵀ) * V by simp only [mul_assoc],
      hWA, mul_one, hV1]
  · rw [transpose_mul, transpose_transpose,
      show Vᵀ * W * B * (Wᵀ * V) = Vᵀ * (W * B * Wᵀ) * V by simp only [mul_assoc], hWt]
    conv_lhs => rw [hspec]
    rw [show Vᵀ * (V * diagonal (RCLike.ofReal ∘ hC.eigenvalues) * Vᵀ) * V
        = Vᵀ * V * diagonal (RCLike.ofReal ∘ hC.eigenvalues) * (Vᵀ * V) by
          simp only [mul_assoc],
      hV1, one_mul, mul_one]

omit [DecidableEq n] in
/-- Congruence by `P` on matrices corresponds to the change of variables `x ↦ P *ᵥ x` on the
associated quadratic forms. -/
private lemma dotProduct_mulVec_congr (P M : Matrix n n ℝ) (x : n → ℝ) :
    (P *ᵥ x) ⬝ᵥ (M *ᵥ (P *ᵥ x)) = x ⬝ᵥ ((Pᵀ * M * P) *ᵥ x) := by
  conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

/-- **Simultaneous diagonalization**, stated on the quadratic forms rather than the matrices:
if `A` is positive definite and `B` is symmetric, one invertible change of variables turns the
form of `A` into `∑ xᵢ ^ 2` and the form of `B` into `∑ dᵢ * xᵢ ^ 2`. -/
theorem PosDef.exists_simultaneous_diagonalization_quadratic {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.IsSymm) :
    ∃ (P : Matrix n n ℝ) (d : n → ℝ), IsUnit P.det ∧
      (∀ x, (P *ᵥ x) ⬝ᵥ (A *ᵥ (P *ᵥ x)) = ∑ i, x i ^ 2) ∧
      (∀ x, (P *ᵥ x) ⬝ᵥ (B *ᵥ (P *ᵥ x)) = ∑ i, d i * x i ^ 2) := by
  obtain ⟨P, hPdet, hPA, d, hPB⟩ := hA.exists_simultaneous_diagonalization hB
  refine ⟨P, d, hPdet, fun x => ?_, fun x => ?_⟩
  · rw [dotProduct_mulVec_congr, hPA, one_mulVec]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => by ring
  · rw [dotProduct_mulVec_congr, hPB]
    simp only [dotProduct, mulVec_diagonal]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- If both forms are positive definite, the diagonal entries produced by
`Matrix.PosDef.exists_simultaneous_diagonalization` are positive. -/
theorem PosDef.exists_simultaneous_diagonalization_of_posDef {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ P : Matrix n n ℝ, IsUnit P.det ∧ Pᵀ * A * P = 1 ∧
      ∃ d : n → ℝ, (∀ i, 0 < d i) ∧ Pᵀ * B * P = diagonal d := by
  have hBsymm : B.IsSymm := by
    change Bᵀ = B
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hB.1
  obtain ⟨P, hPdet, hPA, d, hPB⟩ := hA.exists_simultaneous_diagonalization hBsymm
  refine ⟨P, hPdet, hPA, d, fun i => ?_, hPB⟩
  have hPD : (Pᵀ * B * P).PosDef := by
    rw [(conjTranspose_eq_transpose_of_trivial P).symm]
    let _ : Invertible P := invertibleOfIsUnitDet P hPdet
    exact hB.conjTranspose_mul_mul_same
      (mulVec_injective_iff_isUnit.mpr (isUnit_of_invertible P))
  rw [hPB] at hPD
  exact posDef_diagonal_iff.mp hPD i

end Matrix
