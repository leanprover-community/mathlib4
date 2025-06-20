/-
Copyright (c) 2020 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis, Alex Meiburg
-/

import Mathlib.Analysis.RCLike.Basic

variable {V: Type*}
variable [NormedAddCommGroup V]
variable [NormedSpace ℝ V]

-- ?? how to describe this?
/-- The unit length vector from a given vector. Note that `normalized 0 = 0`. -/
noncomputable def normalized (x : V) : V := ‖x‖⁻¹ • x

@[simp]
theorem normalized_zero_eq_zero : normalized (0 : V) = 0 := by
  simp [normalized]

@[simp]
lemma norm_normalized_eq_one_iff {x : V} : ‖normalized x‖ = 1 ↔ x ≠ 0 := by
  constructor
  · contrapose!
    rintro rfl
    simp
  · intro h
    simp [normalized, norm_smul, show ‖x‖ ≠ 0 by simp [h]]

@[simp]
lemma normalized_eq_self_of_norm_eq_one {x : V} (h : ‖x‖ = 1) : normalized x = x := by
  simp [normalized, h]

@[simp]
theorem normalized_normalized (x : V) : normalized (normalized x) = normalized x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [← ne_eq, ← norm_normalized_eq_one_iff] at hx
  simp [hx]

theorem normalized_smul_of_pos {r : ℝ} (hr : 0 < r) (x : V) :
    normalized (r • x) = normalized x := by
  by_cases hx : x = 0
  · simp [hx]
  rw [normalized, normalized, smul_smul, norm_smul]
  congr
  field_simp [abs_of_pos hr]
