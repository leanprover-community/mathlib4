/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
module

public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Instances.Matrix

/-!
# Regularized matrix inverse: limit as the regularization vanishes

For a square matrix `M` with `det M ≠ 0` over a normed field, the
**Tikhonov-regularized** expression `(M + lam • 1)⁻¹ * M` converges to the
identity matrix as the regularization scalar `lam` tends to zero, and
consequently its trace converges to `tr 1 = Fintype.card d`.

The proof composes existing Mathlib infrastructure:

* `NormedRing.inverse_continuousAt` — continuity of `Ring.inverse` at any unit
  of a normed ring with summable geometric series (automatic for a normed
  field),
* `continuousAt_matrix_inv` — continuity of matrix inversion at any matrix
  whose determinant is a unit (from `Mathlib.Topology.Instances.Matrix`),
* `Matrix.nonsing_inv_mul` — the algebraic identity `M⁻¹ * M = 1` at a
  matrix with unit determinant,
* `Continuous.matrix_trace` — continuity of the matrix trace.

## Main results

* `Matrix.regularizedInv_mul_tendsto_one`:
  `(M + lam • 1)⁻¹ * M ⟶ 1` as `lam → 0`, for `M` with `det M ≠ 0`.
* `Matrix.trace_regularizedInv_mul_tendsto`:
  `tr ((M + lam • 1)⁻¹ * M) ⟶ tr 1` as `lam → 0`.
* `Matrix.trace_regularizedInv_mul_tendsto_card`: the specialization stating
  that the limit equals `(Fintype.card d : R)`.

These lemmas are useful in matrix-regularization limit arguments arising in
numerical linear algebra (Tikhonov-regularized least squares, ridge
regression) and in statistics.
-/

@[expose] public section

namespace Matrix

open Filter Topology

variable {d R : Type*} [Fintype d] [DecidableEq d] [NormedField R]

/-- For a square matrix `M` with nonzero determinant over a normed field, the
regularized inverse `(M + lam • 1)⁻¹ * M` tends to the identity matrix as the
scalar `lam` tends to zero. -/
theorem regularizedInv_mul_tendsto_one
    (M : Matrix d d R) (hM : M.det ≠ 0) :
    Tendsto (fun lam : R => (M + lam • (1 : Matrix d d R))⁻¹ * M)
      (𝓝 0) (𝓝 (1 : Matrix d d R)) := by
  -- The perturbation `lam ↦ M + lam • 1` is continuous.
  have h_add : Continuous (fun lam : R => M + lam • (1 : Matrix d d R)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  -- `Ring.inverse` is continuous at the (nonzero) determinant of `M`.
  have h_det_unit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have h_ring_inv : ContinuousAt Ring.inverse M.det := by
    have := NormedRing.inverse_continuousAt h_det_unit.unit
    simpa [IsUnit.unit_spec] using this
  -- Hence `Inv.inv` on matrices is continuous at `M`.
  have h_mat_inv : ContinuousAt (Inv.inv : Matrix d d R → Matrix d d R) M :=
    continuousAt_matrix_inv M h_ring_inv
  -- The perturbation evaluates to `M` at `lam = 0`, so the composition
  -- `lam ↦ (M + lam • 1)⁻¹` is continuous at `0`.
  have h_g0 : M + (0 : R) • (1 : Matrix d d R) = M := by simp
  have h_inv_comp :
      ContinuousAt (fun lam : R => (M + lam • (1 : Matrix d d R))⁻¹) 0 :=
    h_mat_inv.comp_of_eq h_add.continuousAt h_g0
  -- Multiply on the right by the constant `M`.
  have h_mul :
      ContinuousAt (fun lam : R => (M + lam • (1 : Matrix d d R))⁻¹ * M) 0 :=
    h_inv_comp.mul continuousAt_const
  -- Identify the limit value `M⁻¹ * M` with `1` via `Matrix.nonsing_inv_mul`.
  have h_value :
      (M + (0 : R) • (1 : Matrix d d R))⁻¹ * M = (1 : Matrix d d R) := by
    rw [h_g0]; exact Matrix.nonsing_inv_mul M h_det_unit
  have h_tendsto := h_mul.tendsto
  rw [h_value] at h_tendsto
  exact h_tendsto

/-- Trace version of `regularizedInv_mul_tendsto_one`: the trace of
`(M + lam • 1)⁻¹ * M` tends to `tr 1` as `lam → 0`. -/
theorem trace_regularizedInv_mul_tendsto
    (M : Matrix d d R) (hM : M.det ≠ 0) :
    Tendsto (fun lam : R => ((M + lam • (1 : Matrix d d R))⁻¹ * M).trace)
      (𝓝 0) (𝓝 ((1 : Matrix d d R).trace)) :=
  (continuous_id.matrix_trace.tendsto _).comp
    (regularizedInv_mul_tendsto_one M hM)

/-- Specialization of `trace_regularizedInv_mul_tendsto` via `Matrix.trace_one`:
the trace of the regularized inverse tends to `(Fintype.card d : R)`. -/
theorem trace_regularizedInv_mul_tendsto_card
    (M : Matrix d d R) (hM : M.det ≠ 0) :
    Tendsto (fun lam : R => ((M + lam • (1 : Matrix d d R))⁻¹ * M).trace)
      (𝓝 0) (𝓝 ((Fintype.card d : ℕ) : R)) := by
  have h := trace_regularizedInv_mul_tendsto M hM
  simpa [Matrix.trace_one] using h

end Matrix
