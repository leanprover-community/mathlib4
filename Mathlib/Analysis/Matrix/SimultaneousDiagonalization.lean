/-
Copyright (c) 2026 Moe Tabei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moe Tabei
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.Spectrum

/-!
# Simultaneous diagonalization of two Hermitian forms

If `A` is a positive definite matrix over `𝕜` and `B` is a Hermitian matrix over `𝕜`, then a
single congruence takes `A` to the identity and `B` to a real diagonal matrix. Equivalently, two
Hermitian forms, one of which is positive definite, can be diagonalized simultaneously.

## Main results

* `Matrix.PosDef.exists_simultaneous_diagonalization`: there is a matrix `P` with
  `Pᴴ * A * P = 1` and `Pᴴ * B * P` diagonal with real entries. Such a `P` is automatically
  invertible.
* `Matrix.mul_eq_mul_diagonal_of_simultaneous_diagonalization`: the columns of `P` solve the
  generalized eigenvalue problem `B * P = A * P * D`.
* `Matrix.det_sub_smul_eq_zero_of_simultaneous_diagonalization`: the diagonal entries are roots
  of `det (B - μ • A)`, that is, they are the generalized eigenvalues of the pencil `(A, B)`.

## Implementation notes

Conjugating by the inverse of `CFC.sqrt A` turns `A` into the identity. The resulting congruence
of `B` is again Hermitian, so `Matrix.IsHermitian.spectral_theorem` diagonalizes it by a unitary
matrix, and the two changes of basis compose.
-/

@[expose] public section

open Matrix Unitary
open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Simultaneous diagonalization of two Hermitian forms.** If `A` is positive definite and `B`
is Hermitian, then some matrix `P` satisfies `Pᴴ * A * P = 1` and takes `B` to a diagonal matrix
with real entries by congruence. -/
theorem PosDef.exists_simultaneous_diagonalization {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.IsHermitian) :
    ∃ P : Matrix n n 𝕜, Pᴴ * A * P = 1 ∧
      ∃ d : n → ℝ, Pᴴ * B * P = diagonal (RCLike.ofReal ∘ d) := by
  -- The square root of `A` is positive definite, hence invertible, and conjugating by its
  -- inverse turns `A` into the identity.
  set S : Matrix n n 𝕜 := CFC.sqrt A
  have hS : S.PosDef := isStrictlyPositive_iff_posDef.mp <| by cfc_tac
  have hdetS : IsUnit S.det := isUnit_iff_isUnit_det _ |>.mp hS.isUnit
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  set W : Matrix n n 𝕜 := S⁻¹ with hWdef
  have hWh : Wᴴ = W := by rw [hWdef, conjTranspose_nonsing_inv, hS.1]
  have hWA : W * A * Wᴴ = 1 := by
    rw [hWh, hWdef, ← hSS,
      show S⁻¹ * (S * S) * S⁻¹ = S⁻¹ * S * (S * S⁻¹) by simp only [mul_assoc],
      nonsing_inv_mul S hdetS, mul_nonsing_inv S hdetS, mul_one]
  -- The congruence of `B` is Hermitian, so the spectral theorem diagonalizes it.
  have hC : (W * B * Wᴴ).IsHermitian := isHermitian_mul_mul_conjTranspose W hB
  have hspec := hC.spectral_theorem
  rw [conjStarAlgAut_apply] at hspec
  set V : Matrix n n 𝕜 := ↑(hC.eigenvectorUnitary) with hVdef
  have hstar : star V = Vᴴ := star_eq_conjTranspose V
  rw [hstar] at hspec
  have hV1 : Vᴴ * V = 1 := by
    have h := Unitary.coe_star_mul_self hC.eigenvectorUnitary
    rwa [← hVdef, hstar] at h
  -- `P = Wᴴ * V` diagonalizes both forms at once.
  refine ⟨Wᴴ * V, ?_, hC.eigenvalues, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_conjTranspose,
      show Vᴴ * W * A * (Wᴴ * V) = Vᴴ * (W * A * Wᴴ) * V by simp only [mul_assoc],
      hWA, mul_one, hV1]
  · rw [conjTranspose_mul, conjTranspose_conjTranspose,
      show Vᴴ * W * B * (Wᴴ * V) = Vᴴ * (W * B * Wᴴ) * V by simp only [mul_assoc]]
    conv_lhs => rw [hspec]
    rw [show Vᴴ * (V * diagonal (RCLike.ofReal ∘ hC.eigenvalues) * Vᴴ) * V
        = Vᴴ * V * diagonal (RCLike.ofReal ∘ hC.eigenvalues) * (Vᴴ * V) by
          simp only [mul_assoc],
      hV1, one_mul, mul_one]

/-- A matrix `P` with `Pᴴ * A * P = 1` is invertible. -/
lemma isUnit_det_of_conjTranspose_mul_mul_eq_one {A P : Matrix n n 𝕜} (hPA : Pᴴ * A * P = 1) :
    IsUnit P.det := by
  have h := congrArg det hPA
  rw [det_mul, det_one] at h
  exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one h)

/-- The columns of a simultaneous diagonalizer solve the generalized eigenvalue problem: if
`Pᴴ * A * P = 1` and `Pᴴ * B * P` is the diagonal matrix `D`, then `B * P = A * P * D`. -/
theorem mul_eq_mul_diagonal_of_simultaneous_diagonalization {A B P : Matrix n n 𝕜} {d : n → ℝ}
    (hPA : Pᴴ * A * P = 1) (hPB : Pᴴ * B * P = diagonal (RCLike.ofReal ∘ d)) :
    B * P = A * P * diagonal (RCLike.ofReal ∘ d) := by
  have hPh : IsUnit (Pᴴ).det := by
    rw [det_conjTranspose]; exact (isUnit_det_of_conjTranspose_mul_mul_eq_one hPA).star
  have key : Pᴴ * (B * P) = Pᴴ * (A * P * diagonal (RCLike.ofReal ∘ d)) := by
    rw [← mul_assoc, hPB, show Pᴴ * (A * P * diagonal (RCLike.ofReal ∘ d))
      = (Pᴴ * A * P) * diagonal (RCLike.ofReal ∘ d) by simp only [mul_assoc], hPA, one_mul]
  have h2 : (Pᴴ)⁻¹ * (Pᴴ * (B * P))
      = (Pᴴ)⁻¹ * (Pᴴ * (A * P * diagonal (RCLike.ofReal ∘ d))) := by rw [key]
  simp only [← mul_assoc, nonsing_inv_mul (Pᴴ) hPh, one_mul] at h2
  exact h2

/-- The diagonal entries produced by a simultaneous diagonalization are the generalized
eigenvalues of the pencil `(A, B)`: each of them is a root of `det (B - μ • A)`. -/
theorem det_sub_smul_eq_zero_of_simultaneous_diagonalization {A B P : Matrix n n 𝕜} {d : n → ℝ}
    (hPA : Pᴴ * A * P = 1) (hPB : Pᴴ * B * P = diagonal (RCLike.ofReal ∘ d)) (i : n) :
    (B - (d i : 𝕜) • A).det = 0 := by
  have hP := isUnit_det_of_conjTranspose_mul_mul_eq_one hPA
  have key : Pᴴ * (B - (d i : 𝕜) • A) * P
      = diagonal (fun j ↦ (RCLike.ofReal (d j) : 𝕜) - (RCLike.ofReal (d i) : 𝕜)) := by
    rw [mul_sub, sub_mul, hPB, Matrix.mul_smul, Matrix.smul_mul, hPA, smul_one_eq_diagonal,
      ← diagonal_sub]
    rfl
  have hdet : (Pᴴ * (B - (d i : 𝕜) • A) * P).det = 0 := by
    rw [key, det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [det_mul, det_mul, det_conjTranspose] at hdet
  rcases mul_eq_zero.mp hdet with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' (isUnit_iff_ne_zero.mp hP.star)
    · exact h'
  · exact absurd h (isUnit_iff_ne_zero.mp hP)

end Matrix
