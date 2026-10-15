/-
Copyright (c) 2026 Karles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karles Marín
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Jacobi's formula and Newton's identity for traces of matrix powers

Let `R` be a commutative ring and `M` a square matrix over `R`.

The *resolvent series* `Matrix.resolventSeries M` is the matrix of formal power series whose
`(i, j)` entry is `∑ₖ (Mᵏ) i j Xᵏ`. It is the two-sided inverse of `1 - X • M` in
`Matrix n n R⟦X⟧`, and its trace is the generating function `∑ₖ trace (Mᵏ) Xᵏ`.

*Jacobi's formula* expresses the derivative of the determinant of a matrix of polynomials as
`derivative (det A) = trace (adjugate A * A.map derivative)`.

Combining the two gives *Newton's identity for traces*: the logarithmic derivative of the reversed
characteristic polynomial `Matrix.charpolyRev M = det (1 - X • M)` is minus the generating function
of the traces of the powers of `M`. No eigenvalues and no assumption on `R` are needed.

## Main definitions

* `Matrix.resolventSeries M`: the matrix `∑ₖ Mᵏ Xᵏ` over `R⟦X⟧`.

## Main results

* `Matrix.one_sub_X_smul_mul_resolventSeries`, `Matrix.resolventSeries_mul_one_sub_X_smul`,
  `Matrix.resolventSeries_eq_inv`: `resolventSeries M = (1 - X • M)⁻¹`.
* `Matrix.trace_resolventSeries`: `trace (resolventSeries M) = ∑ₖ trace (Mᵏ) Xᵏ`.
* `Matrix.det_smul_resolventSeries`: `det (1 - X • M) • resolventSeries M = adjugate (1 - X • M)`.
* `Matrix.derivative_det`: Jacobi's formula.
* `Matrix.coe_derivative_charpolyRev_eq_neg_mul_mk_trace_pow`: Newton's identity
  `(charpolyRev M)′ = - charpolyRev M * ∑ₖ trace (Mᵏ⁺¹) Xᵏ` in `R⟦X⟧`. Its constant coefficient is
  `Matrix.coeff_charpolyRev_eq_neg_trace`.
-/

@[expose] public section

namespace Matrix

open scoped PowerSeries

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-! ### The resolvent series -/

section Resolvent

open PowerSeries

/-- The resolvent series of `M`: the matrix over `R⟦X⟧` whose `(i, j)` entry is
`∑ₖ (Mᵏ) i j Xᵏ`. It is the inverse of `1 - X • M`, see `Matrix.resolventSeries_eq_inv`. -/
noncomputable def resolventSeries (M : Matrix n n R) : Matrix n n R⟦X⟧ :=
  of fun i j => mk fun k => (M ^ k) i j

@[simp]
theorem coeff_resolventSeries_apply (M : Matrix n n R) (i j : n) (k : ℕ) :
    coeff k (resolventSeries M i j) = (M ^ k) i j := by
  rw [resolventSeries, of_apply, coeff_mk]

/-- Multiplying the resolvent series on the left by `M` shifts the powers by one. -/
theorem map_C_mul_resolventSeries (M : Matrix n n R) :
    M.map (C : R →+* R⟦X⟧) * resolventSeries M = of fun i j => mk fun k => (M ^ (k + 1)) i j := by
  ext i j k
  rw [mul_apply, map_sum]
  simp only [map_apply, coeff_C_mul, coeff_resolventSeries_apply, coeff_mk, of_apply]
  rw [← mul_apply, ← pow_succ']

/-- Multiplying the resolvent series on the right by `M` shifts the powers by one. -/
theorem resolventSeries_mul_map_C (M : Matrix n n R) :
    resolventSeries M * M.map (C : R →+* R⟦X⟧) = of fun i j => mk fun k => (M ^ (k + 1)) i j := by
  ext i j k
  rw [mul_apply, map_sum]
  simp only [map_apply, coeff_mul_C, coeff_resolventSeries_apply, coeff_mk, of_apply]
  rw [← mul_apply, ← pow_succ]

/-- The telescoping step shared by the left and right Neumann series. -/
private theorem resolventSeries_sub_X_smul_shift (M : Matrix n n R) :
    resolventSeries M - (X : R⟦X⟧) • (of fun i j => mk fun k => (M ^ (k + 1)) i j) = 1 := by
  ext i j k
  rw [sub_apply, smul_apply, of_apply, smul_eq_mul, map_sub, coeff_resolventSeries_apply]
  rcases k with _ | m
  · rw [coeff_zero_X_mul, sub_zero, pow_zero]
    by_cases h : i = j <;> simp [one_apply, h]
  · rw [coeff_succ_X_mul, coeff_mk]
    by_cases h : i = j <;> simp [one_apply, coeff_one, h]

/-- The resolvent series is a right inverse of `1 - X • M`. -/
theorem one_sub_X_smul_mul_resolventSeries (M : Matrix n n R) :
    (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)) * resolventSeries M = 1 := by
  rw [sub_mul, one_mul, smul_mul_assoc, map_C_mul_resolventSeries,
    resolventSeries_sub_X_smul_shift]

/-- The resolvent series is a left inverse of `1 - X • M`. -/
theorem resolventSeries_mul_one_sub_X_smul (M : Matrix n n R) :
    resolventSeries M * (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)) = 1 := by
  rw [mul_sub, mul_one, mul_smul_comm, resolventSeries_mul_map_C,
    resolventSeries_sub_X_smul_shift]

/-- The resolvent series is the inverse of `1 - X • M` in `Matrix n n R⟦X⟧`. -/
theorem resolventSeries_eq_inv (M : Matrix n n R) :
    resolventSeries M = (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧))⁻¹ :=
  (inv_eq_left_inv (resolventSeries_mul_one_sub_X_smul M)).symm

/-- The trace of the resolvent series is the generating function of the traces of the powers. -/
theorem trace_resolventSeries (M : Matrix n n R) :
    (resolventSeries M).trace = mk fun k => (M ^ k).trace := by
  ext k
  simp only [trace, diag_apply, map_sum, coeff_resolventSeries_apply, coeff_mk]

/-- The trace of `resolventSeries M * M` is `∑ₖ trace (Mᵏ⁺¹) Xᵏ`. -/
theorem trace_resolventSeries_mul_map_C (M : Matrix n n R) :
    (resolventSeries M * M.map (C : R →+* R⟦X⟧)).trace = mk fun k => (M ^ (k + 1)).trace := by
  rw [resolventSeries_mul_map_C]
  ext k
  simp only [trace, diag_apply, of_apply, map_sum, coeff_mk]

/-- `adjugate (1 - X • M) = det (1 - X • M) • resolventSeries M`. -/
theorem det_smul_resolventSeries (M : Matrix n n R) :
    (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)).det • resolventSeries M =
      adjugate (1 - (X : R⟦X⟧) • M.map (C : R →+* R⟦X⟧)) := by
  rw [← one_mul (resolventSeries M), ← smul_mul_assoc, ← adjugate_mul, mul_assoc,
    one_sub_X_smul_mul_resolventSeries, mul_one]

end Resolvent

/-! ### Jacobi's formula -/

section Jacobi

open Polynomial

/-- Column-wise Leibniz rule: `derivative (det A)` is the sum over `k` of the determinants of
`A` with its `k`-th column differentiated. -/
private theorem derivative_det_eq_sum_updateCol (A : Matrix n n R[X]) :
    derivative A.det = ∑ k, (A.updateCol k fun a => derivative (A a k)).det := by
  rw [det_apply', map_sum]
  simp only [derivative_intCast_mul, derivative_prod_finset, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [← Finset.prod_erase_mul Finset.univ
    (fun i => (A.updateCol k fun a => derivative (A a k)) (σ i) i) (Finset.mem_univ k)]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [updateCol_ne (Finset.ne_of_mem_erase hi)]
  · rw [updateCol_self]

/-- **Jacobi's formula**: for a square matrix `A` of polynomials,
`derivative (det A) = trace (adjugate A * A.map derivative)`. -/
theorem derivative_det (A : Matrix n n R[X]) :
    derivative A.det = (A.adjugate * A.map derivative).trace := by
  rw [derivative_det_eq_sum_updateCol]
  simp only [trace, diag_apply, mul_apply, map_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← cramer_apply, cramer_eq_adjugate_mulVec]
  rfl

omit [Fintype n] in
/-- The entrywise derivative of `1 - X • M` is `-M`. -/
theorem map_derivative_one_sub_X_smul (M : Matrix n n R) :
    (1 - (X : R[X]) • M.map (C : R →+* R[X])).map derivative = -M.map (C : R →+* R[X]) := by
  ext a b
  simp only [map_apply, sub_apply, one_apply, smul_apply, smul_eq_mul, neg_apply,
    derivative_sub, apply_ite derivative, derivative_one, derivative_zero, ite_self, zero_sub,
    derivative_mul, derivative_X, one_mul, derivative_C, mul_zero, add_zero]

/-! ### Newton's identity for traces -/

/-- **Newton's identity for traces of matrix powers**: in `R⟦X⟧`,
`(charpolyRev M)′ = - charpolyRev M * ∑ₖ trace (Mᵏ⁺¹) Xᵏ`.
Equivalently, `∑ₖ₌₁^∞ trace (Mᵏ) Xᵏ = - X (charpolyRev M)′ / charpolyRev M`. -/
theorem coe_derivative_charpolyRev_eq_neg_mul_mk_trace_pow (M : Matrix n n R) :
    ((derivative M.charpolyRev : R[X]) : R⟦X⟧) =
      -(M.charpolyRev : R⟦X⟧) * PowerSeries.mk fun k => (M ^ (k + 1)).trace := by
  have hcp : (charpolyRev M : R[X]) = (1 - (X : R[X]) • M.map (C : R →+* R[X])).det := rfl
  have hMC : (M.map (C : R →+* R[X])).map Polynomial.coeToPowerSeries.ringHom =
      M.map (PowerSeries.C : R →+* R⟦X⟧) := by
    ext a b
    simp only [map_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
  have hFs : (1 - (X : R[X]) • M.map (C : R →+* R[X])).map Polynomial.coeToPowerSeries.ringHom =
      1 - (PowerSeries.X : R⟦X⟧) • M.map (PowerSeries.C : R →+* R⟦X⟧) := by
    ext a b
    simp only [map_apply, sub_apply, one_apply, smul_apply, smul_eq_mul, map_sub, map_mul,
      map_one, map_zero, apply_ite ⇑Polynomial.coeToPowerSeries.ringHom,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C]
  have hadj : (1 - (X : R[X]) • M.map (C : R →+* R[X])).adjugate.map
        Polynomial.coeToPowerSeries.ringHom =
      adjugate (1 - (PowerSeries.X : R⟦X⟧) • M.map (PowerSeries.C : R →+* R⟦X⟧)) := by
    rw [← hFs]
    exact RingHom.map_adjugate _ _
  have hdet : (((1 - (X : R[X]) • M.map (C : R →+* R[X])).det : R[X]) : R⟦X⟧) =
      (1 - (PowerSeries.X : R⟦X⟧) • M.map (PowerSeries.C : R →+* R⟦X⟧)).det := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, RingHom.map_det]
    exact congrArg det hFs
  rw [hcp, derivative_det, map_derivative_one_sub_X_smul, mul_neg, trace_neg,
    ← Polynomial.coeToPowerSeries.ringHom_apply, map_neg, AddMonoidHom.map_trace, Matrix.map_mul,
    hMC, hadj, ← det_smul_resolventSeries, smul_mul_assoc, trace_smul,
    trace_resolventSeries_mul_map_C, smul_eq_mul, hdet, neg_mul]

end Jacobi

end Matrix
