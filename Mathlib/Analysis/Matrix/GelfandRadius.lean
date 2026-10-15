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
  have h k : (A * B) ^ (k + 1) = A * (B * A) ^ k * B := by
    induction k with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, pow_succ]; simp_rw [Matrix.mul_assoc]
  replace h k : ‖(A * B) ^ (k + 1)‖ ≤ ‖A‖ * ‖B * A‖ ^ k * ‖B‖ := by
    cases k
    · simpa using linfty_opNorm_mul A B
    · grw [h, linfty_opNorm_mul, linfty_opNorm_mul, norm_pow_le']
      (expose_names; exact Nat.zero_lt_succ n_1)
    sorry

  by_cases! h1 : ‖(1 : Matrix n n R)‖ ≤ 0
  · replace h1 : ‖B‖ ≤ 0 := by grw [← mul_one B, linfty_opNorm_mul, h1, mul_zero]
    rw [gelfandRadius_of_norm_le_zero h1, gelfandRadius_of_norm_le_zero]
    grw [linfty_opNorm_mul, linfty_opNorm_mul, h1, mul_zero, zero_mul]
  have h k (hk : 1 ≤ k) : (A * B * C) ^ k = A * B ^ k * C := by
    refine Nat.le_induction (by simp) (fun k _ ih ↦ ?_) k hk
    transitivity A * B ^ k * (C * A) * B * C <;> grind [Matrix.mul_assoc]
  have key {c : ℝ} (hc : c ≠ 0) : Tendsto (fun n : ℕ ↦ c ^ (n : ℝ)⁻¹) atTop (𝓝 1) :=
    ((c.continuous_const_rpow hc).tendsto' 0 1 c.rpow_zero).comp tendsto_inv_atTop_nhds_zero_nat
  grw [← hCA, linfty_opNorm_mul] at h1
  have hA : 0 < ‖A‖ := pos_of_mul_pos_right h1 (norm_nonneg C)
  have hC : 0 < ‖C‖ := pos_of_mul_pos_left h1 (norm_nonneg A)
  replace key := ((key hA.ne').mul (tendsto_gelfandRadius B)).mul (key hC.ne')
  rw [one_mul, mul_one] at key
  refine le_of_tendsto_of_tendsto (tendsto_gelfandRadius (A * B * C)) key ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  grw [h k hk, linfty_opNorm_mul, linfty_opNorm_mul, Real.mul_rpow, Real.mul_rpow] <;> positivity

open Filter Topology in
theorem gelfandRadius_conj_le
    (A : Matrix m n R) (B : Matrix n n R) (C : Matrix n m R)
    (hCA : C * A = 1) : gelfandRadius (A * B * C) ≤ gelfandRadius B := by
  by_cases! h1 : ‖(1 : Matrix n n R)‖ ≤ 0
  · replace h1 : ‖B‖ ≤ 0 := by grw [← mul_one B, linfty_opNorm_mul, h1, mul_zero]
    rw [gelfandRadius_of_norm_le_zero h1, gelfandRadius_of_norm_le_zero]
    grw [linfty_opNorm_mul, linfty_opNorm_mul, h1, mul_zero, zero_mul]
  have h k (hk : 1 ≤ k) : (A * B * C) ^ k = A * B ^ k * C := by
    refine Nat.le_induction (by simp) (fun k _ ih ↦ ?_) k hk
    transitivity A * B ^ k * (C * A) * B * C <;> grind [Matrix.mul_assoc]
  have key {c : ℝ} (hc : c ≠ 0) : Tendsto (fun n : ℕ ↦ c ^ (n : ℝ)⁻¹) atTop (𝓝 1) :=
    ((c.continuous_const_rpow hc).tendsto' 0 1 c.rpow_zero).comp tendsto_inv_atTop_nhds_zero_nat
  grw [← hCA, linfty_opNorm_mul] at h1
  have hA : 0 < ‖A‖ := pos_of_mul_pos_right h1 (norm_nonneg C)
  have hC : 0 < ‖C‖ := pos_of_mul_pos_left h1 (norm_nonneg A)
  replace key := ((key hA.ne').mul (tendsto_gelfandRadius B)).mul (key hC.ne')
  rw [one_mul, mul_one] at key
  refine le_of_tendsto_of_tendsto (tendsto_gelfandRadius (A * B * C)) key ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  grw [h k hk, linfty_opNorm_mul, linfty_opNorm_mul, Real.mul_rpow, Real.mul_rpow] <;> positivity

theorem gelfandRadius_conj
    (A : Matrix m n R) (B : Matrix n n R) (C : Matrix n m R)
    (hAC : A * C = 1) (hCA : C * A = 1) : gelfandRadius (A * B * C) = gelfandRadius B := by
  refine le_antisymm (gelfandRadius_conj_le A B C hCA) ?_
  calc gelfandRadius B = gelfandRadius ((C * A) * B * (C * A)) := by simp [hCA]
    _ = gelfandRadius (C * (A * B * C) * A) := by grind [Matrix.mul_assoc]
    _ ≤ gelfandRadius (A * B * C) := gelfandRadius_conj_le C (A * B * C) A hAC

end Matrix
