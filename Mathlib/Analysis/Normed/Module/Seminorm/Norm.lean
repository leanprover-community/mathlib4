/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Anatole Dedecker, Moritz Doll
-/

module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-! # The norm as a seminorm

In this file, we define the norm of a normed space as a bundled seminorm.

-/

public section

variable {𝕜 E F : Type*}

section Seminormed

variable [NormedField 𝕜]

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {r : ℝ} {x : E} {c : 𝕜} {ε : ℝ}

variable (𝕜 E)

/-- The norm of a seminormed space as a seminorm. -/
@[expose] def normSeminorm : Seminorm 𝕜 E :=
  { normAddGroupSeminorm E with smul' := norm_smul }

-- Todo: exposing this definition is questionable, but unexposing needs some work

@[simp]
theorem coe_normSeminorm : ⇑(normSeminorm 𝕜 E) = norm := by rfl

@[simp]
theorem ball_normSeminorm : (normSeminorm 𝕜 E).ball = Metric.ball := by
  ext x r y
  simp only [Seminorm.mem_ball, Metric.mem_ball, coe_normSeminorm, dist_eq_norm]

@[simp]
theorem closedBall_normSeminorm : (normSeminorm 𝕜 E).closedBall = Metric.closedBall := by
  ext x r y
  simp only [Seminorm.mem_closedBall, Metric.mem_closedBall, coe_normSeminorm, dist_eq_norm]

variable {𝕜 E}

/-- Balls at the origin are absorbent. -/
theorem absorbent_ball_zero (hr : 0 < r) : Absorbent 𝕜 (Metric.ball (0 : E) r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm 𝕜 _).absorbent_ball_zero hr

/-- Balls containing the origin are absorbent. -/
theorem absorbent_ball (hx : ‖x‖ < r) : Absorbent 𝕜 (Metric.ball x r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm 𝕜 _).absorbent_ball hx

/-- Balls at the origin are balanced. -/
theorem balanced_ball_zero : Balanced 𝕜 (Metric.ball (0 : E) r) := by
  rw [← ball_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_ball_zero r

/-- Closed balls at the origin are balanced. -/
theorem balanced_closedBall_zero : Balanced 𝕜 (Metric.closedBall (0 : E) r) := by
  rw [← closedBall_normSeminorm 𝕜]
  exact (normSeminorm _ _).balanced_closedBall_zero r

/-- If there is a scalar `c` with `‖c‖ > 1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `‖c‖`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
lemma rescale_to_shell_semi_normed_zpow (hc : 1 < ‖c‖) (εpos : 0 < ε) (hx : ‖x‖ ≠ 0) :
    ∃ n : ℤ, c ^ n ≠ 0 ∧ ‖c ^ n • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖c ^ n • x‖) ∧
      (‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  (normSeminorm 𝕜 E).rescale_to_shell_zpow hc εpos hx

/-- If there is a scalar `c` with `‖c‖ > 1`, then any element with nonzero norm can be
moved by scalar multiplication to any shell of width `‖c‖`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
lemma rescale_to_shell_semi_normed (hc : 1 < ‖c‖) (εpos : 0 < ε) (hx : ‖x‖ ≠ 0) :
    ∃ d : 𝕜, d ≠ 0 ∧ ‖d • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖d • x‖) ∧ (‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  (normSeminorm 𝕜 E).rescale_to_shell hc εpos hx

end Seminormed

section Normed

variable [NormedField 𝕜]

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {r : ℝ} {x : E} {c : 𝕜} {ε : ℝ}

lemma rescale_to_shell_zpow (hc : 1 < ‖c‖) (εpos : 0 < ε) (hx : x ≠ 0) :
    ∃ n : ℤ, c ^ n ≠ 0 ∧ ‖c ^ n • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖c ^ n • x‖) ∧
      (‖c ^ n‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  rescale_to_shell_semi_normed_zpow hc εpos (norm_ne_zero_iff.mpr hx)

/-- If there is a scalar `c` with `‖c‖ > 1`, then any element can be moved by scalar multiplication
to any shell of width `‖c‖`. Also recap information on the norm of the rescaling element that shows
up in applications. -/
lemma rescale_to_shell (hc : 1 < ‖c‖) (εpos : 0 < ε) (hx : x ≠ 0) :
    ∃ d : 𝕜, d ≠ 0 ∧ ‖d • x‖ < ε ∧ (ε / ‖c‖ ≤ ‖d • x‖) ∧ (‖d‖⁻¹ ≤ ε⁻¹ * ‖c‖ * ‖x‖) :=
  rescale_to_shell_semi_normed hc εpos (norm_ne_zero_iff.mpr hx)

end Normed

section VonNBornologyEqMetric

namespace NormedSpace

section NormedField

variable (𝕜)
variable [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem isVonNBounded_of_isBounded {s : Set E} (h : Bornology.IsBounded s) :
    Bornology.IsVonNBounded 𝕜 s := by
  rcases h.subset_ball 0 with ⟨r, hr⟩
  rw [Metric.nhds_basis_ball.isVonNBounded_iff]
  rw [← ball_normSeminorm 𝕜 E] at hr ⊢
  exact fun ε hε ↦ ((normSeminorm 𝕜 E).ball_zero_absorbs_ball_zero hε).mono_right hr

variable (E)

theorem isVonNBounded_ball (r : ℝ) : Bornology.IsVonNBounded 𝕜 (Metric.ball (0 : E) r) :=
  isVonNBounded_of_isBounded _ Metric.isBounded_ball

theorem isVonNBounded_closedBall (r : ℝ) :
    Bornology.IsVonNBounded 𝕜 (Metric.closedBall (0 : E) r) :=
  isVonNBounded_of_isBounded _ Metric.isBounded_closedBall

end NormedField

section NontriviallyNormedField

open scoped Pointwise

variable (𝕜)
variable [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem isVonNBounded_iff {s : Set E} : Bornology.IsVonNBounded 𝕜 s ↔ Bornology.IsBounded s := by
  refine ⟨fun h ↦ ?_, isVonNBounded_of_isBounded _⟩
  rcases (h (Metric.ball_mem_nhds 0 zero_lt_one)).exists_pos with ⟨ρ, hρ, hρball⟩
  rcases NormedField.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩
  specialize hρball a ha.le
  rw [← ball_normSeminorm 𝕜 E, Seminorm.smul_ball_zero (norm_pos_iff.1 <| hρ.trans ha),
    ball_normSeminorm] at hρball
  exact Metric.isBounded_ball.subset hρball

theorem isVonNBounded_iff' {s : Set E} :
    Bornology.IsVonNBounded 𝕜 s ↔ ∃ r : ℝ, ∀ x ∈ s, ‖x‖ ≤ r := by
  rw [NormedSpace.isVonNBounded_iff, isBounded_iff_forall_norm_le]

theorem image_isVonNBounded_iff {α : Type*} {f : α → E} {s : Set α} :
    Bornology.IsVonNBounded 𝕜 (f '' s) ↔ ∃ r : ℝ, ∀ x ∈ s, ‖f x‖ ≤ r := by
  simp_rw [isVonNBounded_iff', Set.forall_mem_image]

/-- In a normed space, the von Neumann bornology (`Bornology.vonNBornology`) is equal to the
metric bornology. -/
theorem vonNBornology_eq : Bornology.vonNBornology 𝕜 E = PseudoMetricSpace.toBornology := by
  rw [Bornology.ext_iff_isBounded]
  intro s
  rw [Bornology.isBounded_iff_isVonNBounded]
  exact isVonNBounded_iff _

theorem isBounded_iff_subset_smul_ball {s : Set E} :
    Bornology.IsBounded s ↔ ∃ a : 𝕜, s ⊆ a • Metric.ball (0 : E) 1 := by
  rw [← isVonNBounded_iff 𝕜]
  constructor
  · intro h
    rcases (h (Metric.ball_mem_nhds 0 zero_lt_one)).exists_pos with ⟨ρ, _, hρball⟩
    rcases NormedField.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩
    exact ⟨a, hρball a ha.le⟩
  · rintro ⟨a, ha⟩
    exact ((isVonNBounded_ball 𝕜 E 1).image (a • (1 : E →L[𝕜] E))).subset ha

theorem isBounded_iff_subset_smul_closedBall {s : Set E} :
    Bornology.IsBounded s ↔ ∃ a : 𝕜, s ⊆ a • Metric.closedBall (0 : E) 1 := by
  constructor
  · rw [isBounded_iff_subset_smul_ball 𝕜]
    exact Exists.imp fun a ha => ha.trans <| Set.smul_set_mono <| Metric.ball_subset_closedBall
  · rw [← isVonNBounded_iff 𝕜]
    rintro ⟨a, ha⟩
    exact ((isVonNBounded_closedBall 𝕜 E 1).image (a • (1 : E →L[𝕜] E))).subset ha

end NontriviallyNormedField

end NormedSpace

end VonNBornologyEqMetric
