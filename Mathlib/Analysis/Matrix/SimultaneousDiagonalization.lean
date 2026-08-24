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

* `Matrix.PosDef.exists_simultaneous_diagonalization`: there is an invertible `P` with
  `Pᴴ * A * P = 1` and `Pᴴ * B * P` diagonal with real entries.
* `Matrix.PosDef.exists_simultaneous_diagonalization_hermitianForm`: the same statement read off
  on the Hermitian forms themselves, as a change of variables taking `A` to `∑ ‖xᵢ‖ ^ 2` and
  `B` to `∑ dᵢ * ‖xᵢ‖ ^ 2`.
* `Matrix.PosDef.exists_simultaneous_diagonalization_of_posDef`: when `B` is positive definite
  as well, the resulting diagonal entries are positive.

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
is Hermitian, then some invertible matrix `P` satisfies `Pᴴ * A * P = 1` and takes `B` to a
diagonal matrix with real entries by congruence. -/
theorem PosDef.exists_simultaneous_diagonalization {A B : Matrix n n 𝕜} (hA : A.PosDef)
    (hB : B.IsHermitian) :
    ∃ P : Matrix n n 𝕜, IsUnit P.det ∧ Pᴴ * A * P = 1 ∧
      ∃ d : n → ℝ, Pᴴ * B * P = diagonal (RCLike.ofReal ∘ d) := by
  classical
  -- The positive semidefinite square root of `A` is invertible, and conjugating by its inverse
  -- turns `A` into the identity.
  set S : Matrix n n 𝕜 := CFC.sqrt A
  have hSherm : S.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have hdetS : IsUnit S.det := by
    have hprod : S.det * S.det = A.det := by rw [← det_mul, hSS]
    have hdetA : A.det ≠ 0 := hA.posSemidef.posDef_iff_det_ne_zero.mp hA
    refine isUnit_iff_ne_zero.mpr fun h => hdetA ?_
    rw [← hprod, h, zero_mul]
  set W : Matrix n n 𝕜 := S⁻¹ with hWdef
  have hWh : Wᴴ = W := by rw [hWdef, conjTranspose_nonsing_inv, hSherm]
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
  refine ⟨Wᴴ * V, ?_, ?_, hC.eigenvalues, ?_⟩
  · have hdetV : IsUnit V.det := by
      have h : Vᴴ.det * V.det = 1 := by rw [← det_mul, hV1, det_one]
      exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul_eq_one h)
    have hdetW : IsUnit W.det := isUnit_nonsing_inv_det S hdetS
    rw [det_mul, det_conjTranspose]
    exact hdetW.star.mul hdetV
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

omit [DecidableEq n] in
/-- Congruence by `P` on matrices corresponds to the change of variables `x ↦ P *ᵥ x` on the
associated Hermitian forms. -/
private lemma star_dotProduct_mulVec_congr (P M : Matrix n n 𝕜) (x : n → 𝕜) :
    star (P *ᵥ x) ⬝ᵥ (M *ᵥ (P *ᵥ x)) = star x ⬝ᵥ ((Pᴴ * M * P) *ᵥ x) := by
  rw [star_mulVec]
  conv_rhs => rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]

/-- **Simultaneous diagonalization**, stated on the Hermitian forms rather than the matrices:
if `A` is positive definite and `B` is Hermitian, one invertible change of variables turns the
form of `A` into `∑ ‖xᵢ‖ ^ 2` and the form of `B` into `∑ dᵢ * ‖xᵢ‖ ^ 2`. -/
theorem PosDef.exists_simultaneous_diagonalization_hermitianForm {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.IsHermitian) :
    ∃ (P : Matrix n n 𝕜) (d : n → ℝ), IsUnit P.det ∧
      (∀ x, star (P *ᵥ x) ⬝ᵥ (A *ᵥ (P *ᵥ x)) = ((∑ i, ‖x i‖ ^ 2 : ℝ) : 𝕜)) ∧
      (∀ x, star (P *ᵥ x) ⬝ᵥ (B *ᵥ (P *ᵥ x)) = ((∑ i, d i * ‖x i‖ ^ 2 : ℝ) : 𝕜)) := by
  obtain ⟨P, hPdet, hPA, d, hPB⟩ := hA.exists_simultaneous_diagonalization hB
  refine ⟨P, d, hPdet, fun x => ?_, fun x => ?_⟩
  · rw [star_dotProduct_mulVec_congr, hPA, one_mulVec]
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_sum,
      RCLike.ofReal_pow]
  · rw [star_dotProduct_mulVec_congr, hPB]
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, mulVec_diagonal, Function.comp_apply,
      RCLike.ofReal_sum, RCLike.ofReal_mul, RCLike.ofReal_pow]
    exact Finset.sum_congr rfl fun i _ => by
      rw [show (starRingEnd 𝕜) (x i) * ((d i : 𝕜) * x i)
        = (d i : 𝕜) * ((starRingEnd 𝕜) (x i) * x i) by ring, RCLike.conj_mul]

/-- If both forms are positive definite, the diagonal entries produced by
`Matrix.PosDef.exists_simultaneous_diagonalization` are positive. -/
theorem PosDef.exists_simultaneous_diagonalization_of_posDef {A B : Matrix n n 𝕜}
    (hA : A.PosDef) (hB : B.PosDef) :
    ∃ P : Matrix n n 𝕜, IsUnit P.det ∧ Pᴴ * A * P = 1 ∧
      ∃ d : n → ℝ, (∀ i, 0 < d i) ∧ Pᴴ * B * P = diagonal (RCLike.ofReal ∘ d) := by
  obtain ⟨P, hPdet, hPA, d, hPB⟩ := hA.exists_simultaneous_diagonalization hB.1
  refine ⟨P, hPdet, hPA, d, fun i => ?_, hPB⟩
  have hPD : (Pᴴ * B * P).PosDef := by
    let _ : Invertible P := invertibleOfIsUnitDet P hPdet
    exact hB.conjTranspose_mul_mul_same
      (mulVec_injective_iff_isUnit.mpr (isUnit_of_invertible P))
  rw [hPB] at hPD
  simpa using posDef_diagonal_iff.mp hPD i

end Matrix
