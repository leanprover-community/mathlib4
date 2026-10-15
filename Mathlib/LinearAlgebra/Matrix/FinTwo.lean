/-
Copyright (c) 2026 Karles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karles Marín
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc

/-!
# Identities for `2 × 2` matrices

This file collects polynomial identities satisfied by `2 × 2` matrices over a commutative ring,
all consequences of the Cayley–Hamilton theorem in dimension two.

## Main results

* `Matrix.adjugate_fin_two_eq_trace_smul_one_sub`: `adjugate A = trace A • 1 - A`.
* `Matrix.adjugate_add_fin_two`: the adjugate is additive.
* `Matrix.mul_add_mul_eq_trace_smul_add_trace_smul_fin_two`: the polarized Cayley–Hamilton
  identity
  `A * B + B * A = trace A • B + trace B • A + (trace (A * B) - trace A * trace B) • 1`.
* `Matrix.mul_mul_eq_trace_smul_sub_det_smul_adjugate_fin_two`:
  `M * A * M = trace (A * M) • M - det M • adjugate A`.
* `Matrix.det_add_fin_two`: `det (A + B) = det A + trace (adjugate A * B) + det B`.
* `Matrix.det_add_smul_fin_two`: the determinant of a pencil `A + c • B`.
* `Matrix.lie_lie_lie_eq_discr_smul_lie_fin_two`: `⁅X, ⁅X, ⁅X, T⁆⁆⁆ = discr X • ⁅X, T⁆`.
* `Matrix.det_lie_lie_eq_neg_discr_mul_det_lie_fin_two`:
  `det ⁅X, ⁅X, T⁆⁆ = -discr X * det ⁅X, T⁆`.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [CommRing R]

/-- The adjugate of a `2 × 2` matrix is `trace A • 1 - A`. -/
theorem adjugate_fin_two_eq_trace_smul_one_sub (A : Matrix (Fin 2) (Fin 2) R) :
    adjugate A = trace A • (1 : Matrix (Fin 2) (Fin 2) R) - A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two, trace_fin_two]

/-- The adjugate of `2 × 2` matrices is additive. -/
theorem adjugate_add_fin_two (A B : Matrix (Fin 2) (Fin 2) R) :
    adjugate (A + B) = adjugate A + adjugate B := by
  simp only [adjugate_fin_two_eq_trace_smul_one_sub, trace_add, add_smul]
  abel

/-- Polarized Cayley–Hamilton identity for `2 × 2` matrices. -/
theorem mul_add_mul_eq_trace_smul_add_trace_smul_fin_two (A B : Matrix (Fin 2) (Fin 2) R) :
    A * B + B * A = trace A • B + trace B • A +
      (trace (A * B) - trace A * trace B) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, trace_fin_two] <;> ring

/-- For `2 × 2` matrices, `M * A * M = trace (A * M) • M - det M • adjugate A`. -/
theorem mul_mul_eq_trace_smul_sub_det_smul_adjugate_fin_two (M A : Matrix (Fin 2) (Fin 2) R) :
    M * A * M = trace (A * M) • M - det M • adjugate A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, trace_fin_two, det_fin_two, adjugate_fin_two] <;> ring

/-- The determinant of a sum of `2 × 2` matrices. -/
theorem det_add_fin_two (A B : Matrix (Fin 2) (Fin 2) R) :
    det (A + B) = det A + trace (adjugate A * B) + det B := by
  simp [det_fin_two, trace_fin_two, adjugate_fin_two, vecMul, dotProduct, Fin.sum_univ_two]
  ring

/-- The determinant of a pencil of `2 × 2` matrices. -/
theorem det_add_smul_fin_two (A B : Matrix (Fin 2) (Fin 2) R) (c : R) :
    det (A + c • B) = det A + c * (trace A * trace B - trace (A * B)) + c ^ 2 * det B := by
  simp [det_fin_two, trace_fin_two, mul_apply, Fin.sum_univ_two]
  ring

/-- For `2 × 2` matrices, `ad X ^ 3 = discr X • ad X`. -/
theorem lie_lie_lie_eq_discr_smul_lie_fin_two (X T : Matrix (Fin 2) (Fin 2) R) :
    ⁅X, ⁅X, ⁅X, T⁆⁆⁆ = discr X • ⁅X, T⁆ := by
  rw [discr_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ring.lie_def, mul_apply, Fin.sum_univ_two, trace_fin_two, det_fin_two] <;> ring

/-- For `2 × 2` matrices, `det ⁅X, ⁅X, T⁆⁆ = -discr X * det ⁅X, T⁆`. -/
theorem det_lie_lie_eq_neg_discr_mul_det_lie_fin_two (X T : Matrix (Fin 2) (Fin 2) R) :
    det ⁅X, ⁅X, T⁆⁆ = -discr X * det ⁅X, T⁆ := by
  rw [discr_fin_two]
  simp [Ring.lie_def, det_fin_two, trace_fin_two, mul_apply, Fin.sum_univ_two]
  ring

end Matrix
