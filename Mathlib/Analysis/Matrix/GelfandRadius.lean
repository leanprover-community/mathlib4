/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.GelfandRadius

/-!
# Golfand radius of matrices

This file proves some results on the Gelfand radius of matrices.
-/

@[expose] public section

namespace Matrix

open scoped Matrix.Norms.Operator

variable {R m n : Type*} [SeminormedCommRing R] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

open Filter Topology in
private theorem gelfandRadius_mul_comm_le (A : Matrix m n R) (B : Matrix n m R) :
    gelfandRadius (A * B) ≤ gelfandRadius (B * A) := by
  by_cases! hAB₀ : gelfandRadius (A * B) ≤ 0
  · exact hAB₀.trans (gelfandRadius_nonneg (B * A))
  have hAB : 0 < ‖A * B‖ := by
    contrapose! hAB₀
    exact (gelfandRadius_of_norm_le_zero hAB₀).le
  grw [linfty_opNorm_mul] at hAB
  have h k : (A * B) ^ (k + 1) = A * (B * A) ^ k * B := by
    induction k with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, pow_succ]; simp_rw [Matrix.mul_assoc]
  replace h k : ‖(A * B) ^ (k + 1)‖ ≤ ‖A‖ * ‖(B * A) ^ k‖ * ‖B‖ := by
    grw [h, linfty_opNorm_mul, linfty_opNorm_mul]
  have key {c : ℝ} (hc : c ≠ 0) : Tendsto (fun n : ℕ ↦ c ^ (n : ℝ)⁻¹) atTop (𝓝 1) :=
    ((c.continuous_const_rpow hc).tendsto' 0 1 c.rpow_zero).comp tendsto_inv_atTop_nhds_zero_nat
  have key1 {c : ℝ} (hc : c ≠ 0) : Tendsto (fun n : ℕ ↦ c ^ ((n + 1) / n : ℝ)) atTop (𝓝 c) := by
    sorry
  have hA : 0 < ‖A‖ := pos_of_mul_pos_left hAB (norm_nonneg B)
  have hC : 0 < ‖B‖ := pos_of_mul_pos_right hAB (norm_nonneg A)
  replace key := ((key hA.ne').mul (tendsto_gelfandRadius (B * A))).mul (key hC.ne')
  rw [one_mul, mul_one] at key
  suffices Tendsto (fun k : ℕ ↦ ‖(A * B) ^ (k + 1)‖ ^ (k : ℝ)⁻¹)
      atTop (𝓝 (gelfandRadius (A * B))) by
    refine le_of_tendsto_of_tendsto' this key fun k ↦ ?_
    grw [h, Real.mul_rpow, Real.mul_rpow] <;> positivity
  have := (tendsto_gelfandRadius (A * B)).comp (tendsto_add_atTop_nat 1)
  simp [Function.comp_def] at this
  sorry

theorem gelfandRadius_mul_comm (A : Matrix m n R) (B : Matrix n m R) :
    gelfandRadius (A * B) = gelfandRadius (B * A) :=
  le_antisymm (gelfandRadius_mul_comm_le A B) (gelfandRadius_mul_comm_le B A)

end Matrix
