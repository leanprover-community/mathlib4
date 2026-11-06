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

This file proves some results on the Gelfand radius of matrices with respect to the operator norm.
-/

public section

namespace Matrix

open scoped Matrix.Norms.Operator

variable {R m n : Type*} [SeminormedCommRing R] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

private theorem gelfandRadius_mul_comm_le (A : Matrix m n R) (B : Matrix n m R) :
    gelfandRadius (A * B) ≤ gelfandRadius (B * A) := by
  refine le_of_forall_gt_imp_ge_of_dense fun s hAB ↦ ?_
  have hs : 0 < s := (gelfandRadius_nonneg _).trans_lt hAB
  have ⟨D, hD, h⟩ := norm_pow_le_mul_pow_of_gelfandRadius_lt (B * A) hAB
  apply gelfandRadius_le_of_bound (C := max ‖(1 : Matrix m m R)‖ (‖A‖ * ‖B‖ * D * s⁻¹)) hs.le
  intro n; induction n with
  | zero => simp
  | succ k hk =>
    grw [pow_succ, ← Matrix.mul_assoc, Matrix.mul_pow_mul, linfty_opNorm_mul, linfty_opNorm_mul,
      h k, ← le_max_right]
    grind [le_of_eq]

theorem gelfandRadius_mul_comm (A : Matrix m n R) (B : Matrix n m R) :
    gelfandRadius (A * B) = gelfandRadius (B * A) :=
  le_antisymm (gelfandRadius_mul_comm_le A B) (gelfandRadius_mul_comm_le B A)

theorem gelfandRadius_blockDiagonal (M : n → Matrix m m R) :
    gelfandRadius (Matrix.blockDiagonal M) = ⨆ i, gelfandRadius (M i) := by
  have h : Isometry (Matrix.blockDiagonalRingHom m n R) := linfty_opNorm_isometry_blockDiagonal
  exact (h.gelfandRadius_map M).trans (Pi.gelfandRadius_eq M)

end Matrix
