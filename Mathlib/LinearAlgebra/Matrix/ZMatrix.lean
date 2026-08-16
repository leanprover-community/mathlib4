/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Suzuka Yu, Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!

# Z-matrices

A matrix whose off-diagonal entries are all non-positive is known as a Z-matrix. Cartan matrices
are examples of Z-matrices.

## Main results:
* `Matrix.lt_two_mul_of_mul_diagonal_posDef_of_for_le_of_hasEigen`: a spectral bound result for
  Z-matrices satisfying a positive-definiteness condition.

-/

namespace Matrix

open Module.End

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [StarRing R] [TrivialStar R]
  (A : Matrix ι ι R) (d : ι → R) (hA : (diagonal d * A).PosDef) (hD : ∀ i, 0 < d i)

include hA hD

public lemma diag_pos_of_mul_diagonal_posDef (i : ι) :
    0 < A i i := by
  rw [← mul_pos_iff_of_pos_left (hD i)]
  simpa using hA.2 (x := Finsupp.single i 1) (by simp)

/-- A spectral bound result for Z-matrices satisfying a positive-definiteness condition.

It is important because it applies to Cartan matrices, and shows that all (real) eigenvalues must
be strictly less than 4 (a fact which is necessary in the proof of
`RootPairing.GeckConstruction.instIsIrreducible`). -/
public lemma lt_two_mul_of_mul_diagonal_posDef_of_for_le_of_hasEigen
    (μ ρ : R) (hμ : ∀ i j, A i j ≤ if i = j then μ else 0) (hρ : HasEigenvalue A.toLin' ρ) :
    ρ < 2 * μ := by
  by_contra! contra
  set N := μ • 1 - A with N_def
  have hN (i j : ι) : 0 ≤ N i j := by specialize hμ i j; aesop
  obtain ⟨v, hv, hv₀⟩ : ∃ v, N *ᵥ v = (μ - ρ) • v ∧ v ≠ 0 := by
    replace hρ : HasEigenvalue (toLin' N) (μ - ρ) := by simpa [N_def, hasEigenvalue_sub'_iff]
    simpa [hasEigenvector_iff, mulVec_transpose] using hρ.exists_hasEigenvector
  set q := |v| ⬝ᵥ (diagonal d * N) *ᵥ |v| with q_def
  set Q := μ * ∑ i, d i * |v i| ^ 2 with Q_def
  have hq₀ : q < Q := by
    replace hv₀ : |v| ≠ 0 := by simpa
    have h₁ : 0 < ∑ j, ∑ i, |v i| * (d i * A i j) * |v j| := by
      simpa [dot_mulVec_eq_sum_sum] using hA.dotProduct_mulVec_pos hv₀
    have h₂ : Q = ∑ i, |v i| * (d i * μ) * |v i| := by
      rw [Q_def, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [q_def, N_def, dot_mulVec_eq_sum_sum]
    simpa [mul_sub, sub_mul, Matrix.one_apply, h₂]
  have hq₁ : Q ≤ q := by
    rw [Q_def, q_def, ← mulVec_mulVec, dotProduct_mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have h₀ : 0 ≤ ρ - μ := by grind [diag_pos_of_mul_diagonal_posDef A d hA hD hρ.nonempty.some]
    have h₁ : μ ≤ ρ - μ := by grind
    have h₂ : 0 ≤ d i := (hD i).le
    have h₃ : (ρ - μ) * |v i| ≤ (N *ᵥ |v|) i := by
      calc (ρ - μ) * |v i|
          = |μ - ρ| * |v i| := by rw [← abs_eq_self.mpr h₀, abs_sub_comm]
        _ = |(N *ᵥ v) i| := by simp [hv]
        _ = |∑ j, N i j * v j| := by simp [mulVec_eq_sum, mul_comm]
        _ ≤ ∑ j, |N i j * v j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, N i j * |v j| := by simp [abs_eq_self.mpr (hN i _)]
        _ = (N *ᵥ |v|) i := by simp [mulVec_eq_sum, mul_comm]
    calc μ * (d i * |v i| ^ 2)
        = μ * |v i| * (d i * |v i|) := by ring
      _ ≤ (ρ - μ) * |v i| * (d i * |v i|) := by gcongr
      _ ≤ (N *ᵥ |v|) i * (d i * |v i|) := by gcongr
      _ = (N *ᵥ |v|) i * (diagonal d *ᵥ |v|) i := by simp [mulVec_eq_sum, diagonal_apply, mul_comm]
      _ = (|v| ᵥ* diagonal d) i * (N *ᵥ |v|) i := by simp [mulVec_eq_sum, vecMul_eq_sum, mul_comm]
  rw [← not_lt] at hq₁
  contradiction

end Matrix
