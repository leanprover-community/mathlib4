/-
Copyright (c) 2020 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis, Alex Meiburg
-/

import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace

variable {V : Type*}
variable [NormedAddCommGroup V]
variable [InnerProductSpace ℝ V]

lemma inner_eq_sq_norm_iff {x y : V} {a : ℝ} (hx : ‖x‖ = a) (hy : ‖y‖ = a) :
    ⟪x, y⟫ = a^2 ↔ x = y := by
  constructor
  · intro h
    rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
    simp [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm, *]
  · rintro rfl
    rw [← hx, real_inner_self_eq_norm_sq x]

lemma inner_eq_neg_sq_norm_iff {x y : V} {a : ℝ} (hx : ‖x‖ = a) (hy : ‖y‖ = a) :
    ⟪x, y⟫ = -a^2 ↔ x = -y := by
  constructor
  · intro h
    rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ)]
    simp only [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm, inner_neg_right, *]
    abel
  · rintro rfl
    rw [inner_neg_left, real_inner_self_eq_norm_sq, hy]

-- real_inner_le_norm - upper bound of inner product

-- lower bound of inner product
lemma neg_norm_le_real_inner (x y : V) : - (‖x‖ * ‖y‖) ≤ ⟪x, y⟫ :=
  neg_le_of_abs_le (abs_real_inner_le_norm x y)
