/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circle integral transform

In this file we define the circle integral transform of a function `f` with complex domain. This is
defined as $(2πi)^{-1}\frac{f(x)}{x-w}$ where `x` moves along a circle. We then prove some basic
facts about these functions.

These results are useful for proving that the uniform limit of a sequence of holomorphic functions
is holomorphic.

-/


open Set MeasureTheory Metric Filter Function

open scoped Interval Real

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (R : ℝ) (z w : ℂ)

namespace Complex

/-- Given a function `f : ℂ → E`, `circleTransform R z w f` is the function mapping `θ` to
`(2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • ((circleMap z R θ) - w)⁻¹ • f (circleMap z R θ)`.

If `f` is differentiable and `w` is in the interior of the ball, then the integral from `0` to
`2 * π` of this gives the value `f(w)`. -/
def circleTransform (f : ℂ → E) (θ : ℝ) : E :=
  (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • (circleMap z R θ - w)⁻¹ • f (circleMap z R θ)

/-- The derivative of `circleTransform` w.r.t `w`. -/
def circleTransformDeriv (f : ℂ → E) (θ : ℝ) : E :=
  (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • ((circleMap z R θ - w) ^ 2)⁻¹ • f (circleMap z R θ)

theorem circleTransformDeriv_periodic (f : ℂ → E) :
    Periodic (circleTransformDeriv R z w f) (2 * π) := by
  have := periodic_circleMap
  simp_rw [Periodic] at *
  intro x
  simp_rw [circleTransformDeriv, this]
  congr 2
  simp [this]

theorem circleTransformDeriv_eq (f : ℂ → E) : circleTransformDeriv R z w f =
    fun θ => (circleMap z R θ - w)⁻¹ • circleTransform R z w f θ := by
  ext
  simp_rw [circleTransformDeriv, circleTransform, ← mul_smul, ← mul_assoc]
  ring_nf
  rw [inv_pow]
  congr
  ring

theorem integral_circleTransform (f : ℂ → E) :
    (∫ θ : ℝ in (0)..2 * π, circleTransform R z w f θ) =
      (2 * ↑π * I)⁻¹ • ∮ z in C(z, R), (z - w)⁻¹ • f z := by
  simp_rw [circleTransform, circleIntegral, deriv_circleMap, circleMap]
  simp

theorem continuous_circleTransform {R : ℝ} (hR : 0 < R) {f : ℂ → E} {z w : ℂ}
    (hf : ContinuousOn f <| sphere z R) (hw : w ∈ ball z R) :
    Continuous (circleTransform R z w f) := by
  apply_rules [Continuous.smul, continuous_const]
  · rw [funext <| deriv_circleMap _ _]
    apply_rules [Continuous.mul, continuous_circleMap 0 R, continuous_const]
  · exact continuous_circleMap_inv hw
  · apply ContinuousOn.comp_continuous hf (continuous_circleMap z R)
    exact fun _ => (circleMap_mem_sphere _ hR.le) _

theorem continuous_circleTransformDeriv {R : ℝ} (hR : 0 < R) {f : ℂ → E} {z w : ℂ}
    (hf : ContinuousOn f (sphere z R)) (hw : w ∈ ball z R) :
    Continuous (circleTransformDeriv R z w f) := by
  rw [circleTransformDeriv_eq]
  exact (continuous_circleMap_inv hw).smul (continuous_circleTransform hR hf hw)

/-- A useful bound for circle integrals (with complex codomain) -/
def circleTransformBoundingFunction (R : ℝ) (z : ℂ) (w : ℂ × ℝ) : ℂ :=
  circleTransformDeriv R z w.1 (fun _ => 1) w.2

theorem continuousOn_prod_circle_transform_function {R r : ℝ} (hr : r < R) {z : ℂ} :
    ContinuousOn (fun w : ℂ × ℝ => (circleMap z R w.snd - w.fst)⁻¹ ^ 2)
      (closedBall z r ×ˢ univ) := by
  simp_rw [← one_div]
  apply_rules [ContinuousOn.pow, ContinuousOn.div, continuousOn_const]
  · exact ((continuous_circleMap z R).comp_continuousOn continuousOn_snd).sub continuousOn_fst
  · rintro ⟨a, b⟩ ⟨ha, -⟩
    have ha2 : a ∈ ball z R := closedBall_subset_ball hr ha
    exact sub_ne_zero.2 (circleMap_ne_mem_ball ha2 b)

theorem continuousOn_norm_circleTransformBoundingFunction {R r : ℝ} (hr : r < R) (z : ℂ) :
    ContinuousOn ((‖·‖) ∘ circleTransformBoundingFunction R z) (closedBall z r ×ˢ univ) := by
  have : ContinuousOn (circleTransformBoundingFunction R z) (closedBall z r ×ˢ univ) := by
    apply_rules [ContinuousOn.smul, continuousOn_const]
    · simp only [deriv_circleMap]
      apply_rules [ContinuousOn.mul, (continuous_circleMap 0 R).comp_continuousOn continuousOn_snd,
        continuousOn_const]
    · simpa only [inv_pow] using continuousOn_prod_circle_transform_function hr
  exact this.norm

@[deprecated (since := "2025-02-17")] alias continuousOn_abs_circleTransformBoundingFunction :=
  continuousOn_norm_circleTransformBoundingFunction

theorem norm_circleTransformBoundingFunction_le {R r : ℝ} (hr : r < R) (hr' : 0 ≤ r) (z : ℂ) :
    ∃ x : closedBall z r ×ˢ [[0, 2 * π]], ∀ y : closedBall z r ×ˢ [[0, 2 * π]],
    ‖circleTransformBoundingFunction R z y‖ ≤ ‖circleTransformBoundingFunction R z x‖ := by
  have cts := continuousOn_norm_circleTransformBoundingFunction hr z
  have comp : IsCompact (closedBall z r ×ˢ [[0, 2 * π]]) := by
    apply_rules [IsCompact.prod, ProperSpace.isCompact_closedBall z r, isCompact_uIcc]
  have none : (closedBall z r ×ˢ [[0, 2 * π]]).Nonempty :=
    (nonempty_closedBall.2 hr').prod nonempty_uIcc
  have := IsCompact.exists_isMaxOn comp none (cts.mono <| prod_mono_right (subset_univ _))
  simpa [isMaxOn_iff] using this

@[deprecated (since := "2025-02-17")] alias abs_circleTransformBoundingFunction_le :=
  norm_circleTransformBoundingFunction_le

/-- The derivative of a `circleTransform` is locally bounded. -/
theorem circleTransformDeriv_bound {R : ℝ} (hR : 0 < R) {z x : ℂ} {f : ℂ → ℂ} (hx : x ∈ ball z R)
    (hf : ContinuousOn f (sphere z R)) : ∃ B ε : ℝ, 0 < ε ∧
      ball x ε ⊆ ball z R ∧ ∀ (t : ℝ), ∀ y ∈ ball x ε, ‖circleTransformDeriv R z y f t‖ ≤ B := by
  obtain ⟨r, hr, hrx⟩ := exists_lt_mem_ball_of_mem_ball hx
  obtain ⟨ε', hε', H⟩ := exists_ball_subset_ball hrx
  obtain ⟨⟨⟨a, b⟩, ⟨ha, hb⟩⟩, hab⟩ :=
    norm_circleTransformBoundingFunction_le hr (pos_of_mem_ball hrx).le z
  let V : ℝ → ℂ → ℂ := fun θ w => circleTransformDeriv R z w (fun _ => 1) θ
  obtain ⟨X, -, HX2⟩ := (isCompact_sphere z R).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 hR.le) hf.norm
  refine ⟨‖V b a‖ * ‖f X‖, ε', hε', H.trans (ball_subset_ball hr.le), fun y v hv ↦ ?_⟩
  obtain ⟨y1, hy1, hfun⟩ :=
    Periodic.exists_mem_Ico₀ (circleTransformDeriv_periodic R z v f) Real.two_pi_pos y
  have hy2 : y1 ∈ [[0, 2 * π]] := Icc_subset_uIcc <| Ico_subset_Icc_self hy1
  simp only [isMaxOn_iff, mem_sphere_iff_norm] at HX2
  have := mul_le_mul (hab ⟨⟨v, y1⟩, ⟨ball_subset_closedBall (H hv), hy2⟩⟩)
    (HX2 (circleMap z R y1) (circleMap_mem_sphere z hR.le y1)) (norm_nonneg _)
    (norm_nonneg _)
  rw [hfun]
  simpa [V, circleTransformBoundingFunction, circleTransformDeriv, mul_assoc] using this

end Complex
