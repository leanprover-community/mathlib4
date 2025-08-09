/-
Copyright (c) 2020 Ilmārs Cīrulis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilmārs Cīrulis, Alex Meiburg
-/
import Mathlib.Analysis.RCLike.Basic

/-!
# Normalized vector

Function that calculates unit length vector from a vector
(if the given vector is nonzero vector) or returns zero vector
(if the given vector is zero vector).
-/

section RCLike

variable {V : Type*}
variable (𝕜 : Type*)
variable [NormedAddCommGroup V]
variable [RCLike 𝕜]
variable [NormedSpace 𝕜 V]

/-- The normalized vector from a given vector. `normalize 0 = 0`, otherwise it is
the corresponding unit length vector. -/
noncomputable def normalize (x : V) : V := (‖x‖⁻¹ : 𝕜) • x

@[simp]
theorem normalize_zero_eq_zero : normalize 𝕜 (0 : V) = 0 := by
  simp [normalize]

@[simp]
theorem norm_smul_normalized (x : V) : (‖x‖ : 𝕜) • normalize 𝕜 x = x := by
  by_cases hx : x = 0
  all_goals simp [normalize, hx]

@[simp]
lemma norm_normalize_eq_one_iff {x : V} : ‖normalize 𝕜 x‖ = 1 ↔ x ≠ 0 :=
  ⟨by rintro hx rfl; simp at hx, fun h ↦ by simp [normalize, h, norm_smul]⟩

lemma normalize_eq_self_of_norm_eq_one {x : V} (h : ‖x‖ = 1) : normalize 𝕜 x = x := by
  simp [normalize, h]

@[simp]
theorem normalize_normalize (x : V) : normalize 𝕜 (normalize 𝕜 x) = normalize 𝕜 x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [normalize_eq_self_of_norm_eq_one, hx]

@[simp]
theorem normalize_neg (x : V) : normalize 𝕜 (- x) = - normalize 𝕜 x := by
  simp [normalize]

end RCLike


variable {V : Type*}
variable [NormedAddCommGroup V]
variable [NormedSpace ℝ V]

theorem normalize_smul_of_pos {r : ℝ} (hr : 0 < r) (x : V) :
    normalize ℝ (r • x) = normalize ℝ x := by
  simp [normalize, norm_smul, smul_smul, abs_of_pos hr, mul_assoc, inv_mul_cancel₀ hr.ne']

theorem normalize_smul_of_neg {r : ℝ} (hr : r < 0) (x : V) :
    normalize ℝ (r • x) = - normalize ℝ x := by
  simpa using normalize_smul_of_pos (show 0 < -r by linarith) (-x)
