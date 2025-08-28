/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Analysis.Normed.Affine.Simplex
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

/-!
# Simplices in Euclidean spaces.

This file defines properties of simplices in a Euclidean space.

## Main definitions

* `Affine.Simplex.AcuteAngled`

-/


namespace Affine

open EuclideanGeometry
open scoped Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

namespace Simplex

variable {m n : ℕ}

lemma Equilateral.angle_eq_pi_div_three {s : Simplex ℝ P n} (he : s.Equilateral)
    {i₁ i₂ i₃ : Fin (n + 1)} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    ∠ (s.points i₁) (s.points i₂) (s.points i₃) = π / 3 := by
  rcases he with ⟨r, hr⟩
  rw [angle, InnerProductGeometry.angle,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two]
  refine Real.arccos_eq_of_eq_cos (by linarith [Real.pi_nonneg]) (by linarith [Real.pi_nonneg]) ?_
  simp only [vsub_sub_vsub_cancel_right, ← dist_eq_norm_vsub, hr _ _ h₁₂, hr _ _ h₁₃,
    hr _ _ h₂₃.symm, Real.cos_pi_div_three]
  have hr0 : r ≠ 0 := by
    rintro rfl
    replace hr := hr _ _ h₁₂
    rw [dist_eq_zero] at hr
    exact h₁₂ (s.independent.injective hr)
  field_simp
  ring

/-- The property of all angles of a simplex being acute. -/
def AcuteAngled (s : Simplex ℝ P n) : Prop :=
  ∀ i₁ i₂ i₃ : Fin (n + 1), i₁ ≠ i₂ → i₁ ≠ i₃ → i₂ ≠ i₃ →
    ∠ (s.points i₁) (s.points i₂) (s.points i₃) < π / 2

@[simp] lemma acuteAngled_reindex_iff {s : Simplex ℝ P m} (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).AcuteAngled ↔ s.AcuteAngled := by
  refine ⟨fun h {i₁ i₂ i₃} h₁₂ h₁₃ h₂₃ ↦ ?_, fun h {i₁ i₂ i₃} h₁₂ h₁₃ h₂₃ ↦ ?_⟩
  · convert h (i₁ := e i₁) (i₂ := e i₂) (i₃ := e i₃) ?_ ?_ ?_ using 1 <;> simp [*]
  · convert h (i₁ := e.symm i₁) (i₂ := e.symm i₂) (i₃ := e.symm i₃) ?_ ?_ ?_ using 1 <;> simp [*]

lemma Equilateral.acuteAngled {s : Simplex ℝ P n} (he : s.Equilateral) : s.AcuteAngled := by
  intro i₁ i₂ i₃ h₁₂ h₁₃ h₂₃
  rw [he.angle_eq_pi_div_three h₁₂ h₁₃ h₂₃]
  linarith [Real.pi_pos]

end Simplex

namespace Triangle

lemma acuteAngled_iff_angle_lt {t : Triangle ℝ P} : t.AcuteAngled ↔
    ∠ (t.points 0) (t.points 1) (t.points 2) < π / 2 ∧
    ∠ (t.points 1) (t.points 2) (t.points 0) < π / 2 ∧
    ∠ (t.points 2) (t.points 0) (t.points 1) < π / 2 := by
  refine ⟨fun h ↦ ⟨h _ _ _ (by decide) (by decide) (by decide),
                   h _ _ _ (by decide) (by decide) (by decide),
                   h _ _ _ (by decide) (by decide) (by decide)⟩,
          fun ⟨h012, h120, h201⟩ ↦ ?_⟩
  have h210 := angle_comm (t.points 0) _ _ ▸ h012
  have h021 := angle_comm (t.points 1) _ _ ▸ h120
  have h102 := angle_comm (t.points 2) _ _ ▸ h201
  intro i₁ i₂ i₃ h₁₂ h₁₃ h₂₃
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases i₃ <;> simp [*] at *

end Triangle

end Affine
