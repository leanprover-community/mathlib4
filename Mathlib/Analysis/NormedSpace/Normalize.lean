/-
Copyright (c) 2025 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis, Alex Meiburg
-/
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Sign.Defs

/-!
# Normalized vector

Function that returns unit length vector that points in the same direction
(if the given vector is nonzero vector) or returns zero vector
(if the given vector is zero vector).
-/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- For a nonzero vector `x`, `normalize x` is the unit-length vector that points
in the same direction as `x`. If `x = 0`, then `normalize x = 0`. -/
noncomputable def NormedSpace.normalize (x : V) : V := ‖x‖⁻¹ • x

namespace NormedSpace

@[simp]
theorem normalize_zero_eq_zero : normalize (0 : V) = 0 := by
  simp [normalize]

@[simp]
theorem normalize_eq_zero_iff (x : V) : normalize x = 0 ↔ x = 0 := by
  by_cases hx : x = 0 <;> simp [normalize, hx]

@[simp]
theorem norm_smul_normalize (x : V) : ‖x‖ • normalize x = x := by
  by_cases hx : x = 0 <;> simp [normalize, hx]

@[simp]
lemma norm_normalize_eq_one_iff {x : V} : ‖normalize x‖ = 1 ↔ x ≠ 0 := by
  by_cases hx : x = 0 <;> simp [normalize, hx, norm_smul]

alias ⟨_, norm_normalize⟩ := norm_normalize_eq_one_iff

lemma normalize_eq_self_of_norm_eq_one {x : V} (h : ‖x‖ = 1) : normalize x = x := by
  simp [normalize, h]

@[simp]
theorem normalize_normalize (x : V) : normalize (normalize x) = normalize x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [normalize_eq_self_of_norm_eq_one, hx]

@[simp]
theorem normalize_neg (x : V) : normalize (- x) = - normalize x := by
  simp [normalize]

theorem normalize_smul_of_pos {r : ℝ} (hr : 0 < r) (x : V) :
    normalize (r • x) = normalize x := by
  simp [normalize, norm_smul, smul_smul, abs_of_pos hr, hr.ne']

theorem normalize_smul_of_neg {r : ℝ} (hr : r < 0) (x : V) :
    normalize (r • x) = - normalize x := by
  simpa using normalize_smul_of_pos (show 0 < -r by linarith) (-x)

theorem normalize_smul (r : ℝ) (x : V) :
    normalize (r • x) = (SignType.sign r : ℝ) • normalize x := by
  rcases lt_trichotomy 0 r with (h_pos | rfl | h_neg)
  · simp [normalize_smul_of_pos, h_pos]
  · simp
  · simp [normalize_smul_of_neg, h_neg]

end NormedSpace
