/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral

#align_import measure_theory.integral.circle_transform from "leanprover-community/mathlib"@"d11893b411025250c8e61ff2f12ccbd7ee35ab15"

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

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (R : ℝ) (z w : ℂ)

namespace Complex

/-- Given a function `f : ℂ → E`, `circleTransform R z w f` is the function mapping `θ` to
`(2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • ((circleMap z R θ) - w)⁻¹ • f (circleMap z R θ)`.

If `f` is differentiable and `w` is in the interior of the ball, then the integral from `0` to
`2 * π` of this gives the value `f(w)`. -/
def circleTransform (f : ℂ → E) (θ : ℝ) : E :=
  (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • (circleMap z R θ - w)⁻¹ • f (circleMap z R θ)
#align complex.circle_transform Complex.circleTransform

/-- The derivative of `circleTransform` w.r.t `w`.-/
def circleTransformDeriv (f : ℂ → E) (θ : ℝ) : E :=
  (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • ((circleMap z R θ - w) ^ 2)⁻¹ • f (circleMap z R θ)
#align complex.circle_transform_deriv Complex.circleTransformDeriv

theorem circleTransformDeriv_periodic (f : ℂ → E) :
    Periodic (circleTransformDeriv R z w f) (2 * π) := by
  have := periodic_circleMap
  simp_rw [Periodic] at *
  intro x
  simp_rw [circleTransformDeriv, this]
  congr 2
  simp [this]
#align complex.circle_transform_deriv_periodic Complex.circleTransformDeriv_periodic

theorem circleTransformDeriv_eq (f : ℂ → E) : circleTransformDeriv R z w f =
    fun θ => (circleMap z R θ - w)⁻¹ • circleTransform R z w f θ := by
  ext
  simp_rw [circleTransformDeriv, circleTransform, ← mul_smul, ← mul_assoc]
  ring_nf
  rw [inv_pow]
  congr
  ring
#align complex.circle_transform_deriv_eq Complex.circleTransformDeriv_eq

theorem integral_circleTransform (f : ℂ → E) :
    (∫ θ : ℝ in (0)..2 * π, circleTransform R z w f θ) =
      (2 * ↑π * I)⁻¹ • ∮ z in C(z, R), (z - w)⁻¹ • f z := by
  simp_rw [circleTransform, circleIntegral, deriv_circleMap, circleMap]
  simp
#align complex.integral_circle_transform Complex.integral_circleTransform

theorem continuous_circleTransform {R : ℝ} (hR : 0 < R) {f : ℂ → E} {z w : ℂ}
    (hf : ContinuousOn f <| sphere z R) (hw : w ∈ ball z R) :
    Continuous (circleTransform R z w f) := by
  apply_rules [Continuous.smul, continuous_const]
  simp_rw [deriv_circleMap]
  apply_rules [Continuous.mul, continuous_circleMap 0 R, continuous_const]
  · apply continuous_circleMap_inv hw
  · apply ContinuousOn.comp_continuous hf (continuous_circleMap z R)
    exact fun _ => (circleMap_mem_sphere _ hR.le) _
#align complex.continuous_circle_transform Complex.continuous_circleTransform

theorem continuous_circleTransformDeriv {R : ℝ} (hR : 0 < R) {f : ℂ → E} {z w : ℂ}
    (hf : ContinuousOn f (sphere z R)) (hw : w ∈ ball z R) :
    Continuous (circleTransformDeriv R z w f) := by
  rw [circleTransformDeriv_eq]
  exact (continuous_circleMap_inv hw).smul (continuous_circleTransform hR hf hw)
#align complex.continuous_circle_transform_deriv Complex.continuous_circleTransformDeriv

/-- A useful bound for circle integrals (with complex codomain)-/
def circleTransformBoundingFunction (R : ℝ) (z : ℂ) (w : ℂ × ℝ) : ℂ :=
  circleTransformDeriv R z w.1 (fun _ => 1) w.2
#align complex.circle_transform_bounding_function Complex.circleTransformBoundingFunction

theorem continuousOn_prod_circle_transform_function {R r : ℝ} (hr : r < R) {z : ℂ} :
    ContinuousOn (fun w : ℂ × ℝ => (circleMap z R w.snd - w.fst)⁻¹ ^ 2)
      (closedBall z r ×ˢ univ) := by
  simp_rw [← one_div]
  apply_rules [ContinuousOn.pow, ContinuousOn.div, continuousOn_const]
  refine' ((continuous_circleMap z R).continuousOn.comp continuousOn_snd fun _ => And.right).sub
    (continuousOn_id.comp continuousOn_fst fun _ => And.left)
  simp only [mem_prod, Ne.def, and_imp, Prod.forall]
  intro a b ha _
  have ha2 : a ∈ ball z R := by simp at *; linarith
  exact sub_ne_zero.2 (circleMap_ne_mem_ball ha2 b)
#align complex.continuous_on_prod_circle_transform_function Complex.continuousOn_prod_circle_transform_function

theorem continuousOn_abs_circleTransformBoundingFunction {R r : ℝ} (hr : r < R) (z : ℂ) :
    ContinuousOn (abs ∘ fun t => circleTransformBoundingFunction R z t)
      (closedBall z r ×ˢ univ) := by
  have : ContinuousOn (circleTransformBoundingFunction R z) (closedBall z r ×ˢ (⊤ : Set ℝ)) := by
    apply_rules [ContinuousOn.smul, continuousOn_const]
    simp only [deriv_circleMap]
    have c := (continuous_circleMap 0 R).continuousOn (s := ⊤)
    apply_rules [ContinuousOn.mul, c.comp continuousOn_snd fun _ => And.right, continuousOn_const]
    simp_rw [← inv_pow]
    apply continuousOn_prod_circle_transform_function hr
  refine' continuous_abs.continuousOn (s := ⊤).comp this _
  show MapsTo _ _ (⊤ : Set ℂ)
  simp [MapsTo]
#align complex.continuous_on_abs_circle_transform_bounding_function Complex.continuousOn_abs_circleTransformBoundingFunction

theorem abs_circleTransformBoundingFunction_le {R r : ℝ} (hr : r < R) (hr' : 0 ≤ r) (z : ℂ) :
    ∃ x : closedBall z r ×ˢ [[0, 2 * π]], ∀ y : closedBall z r ×ˢ [[0, 2 * π]],
    abs (circleTransformBoundingFunction R z y) ≤ abs (circleTransformBoundingFunction R z x) := by
  have cts := continuousOn_abs_circleTransformBoundingFunction hr z
  have comp : IsCompact (closedBall z r ×ˢ [[0, 2 * π]]) := by
    apply_rules [IsCompact.prod, ProperSpace.isCompact_closedBall z r, isCompact_uIcc]
  have none : (closedBall z r ×ˢ [[0, 2 * π]]).Nonempty :=
    (nonempty_closedBall.2 hr').prod nonempty_uIcc
  have := IsCompact.exists_isMaxOn comp none (cts.mono
    (by intro z; simp only [mem_prod, mem_closedBall, mem_univ, and_true_iff, and_imp]; tauto))
  simp only [IsMaxOn, IsMaxFilter] at this
  simpa [SetCoe.forall, Subtype.coe_mk, SetCoe.exists]
#align complex.abs_circle_transform_bounding_function_le Complex.abs_circleTransformBoundingFunction_le

/-- The derivative of a `circleTransform` is locally bounded. -/
theorem circleTransformDeriv_bound {R : ℝ} (hR : 0 < R) {z x : ℂ} {f : ℂ → ℂ} (hx : x ∈ ball z R)
    (hf : ContinuousOn f (sphere z R)) : ∃ B ε : ℝ, 0 < ε ∧
      ball x ε ⊆ ball z R ∧ ∀ (t : ℝ), ∀ y ∈ ball x ε, ‖circleTransformDeriv R z y f t‖ ≤ B := by
  obtain ⟨r, hr, hrx⟩ := exists_lt_mem_ball_of_mem_ball hx
  obtain ⟨ε', hε', H⟩ := exists_ball_subset_ball hrx
  obtain ⟨⟨⟨a, b⟩, ⟨ha, hb⟩⟩, hab⟩ :=
    abs_circleTransformBoundingFunction_le hr (pos_of_mem_ball hrx).le z
  let V : ℝ → ℂ → ℂ := fun θ w => circleTransformDeriv R z w (fun _ => 1) θ
  have funccomp : ContinuousOn (fun r => abs (f r)) (sphere z R) := by
    have cabs : ContinuousOn abs ⊤ := by apply continuous_abs.continuousOn
    apply cabs.comp hf; rw [MapsTo]; tauto
  have sbou :=
    IsCompact.exists_isMaxOn (isCompact_sphere z R) (NormedSpace.sphere_nonempty.2 hR.le) funccomp
  obtain ⟨X, HX, HX2⟩ := sbou
  refine' ⟨abs (V b a) * abs (f X), ε', hε', Subset.trans H (ball_subset_ball hr.le), _⟩
  intro y v hv
  obtain ⟨y1, hy1, hfun⟩ :=
    Periodic.exists_mem_Ico₀ (circleTransformDeriv_periodic R z v f) Real.two_pi_pos y
  have hy2 : y1 ∈ [[0, 2 * π]] := by
    convert Ico_subset_Icc_self hy1 using 1
    simp [uIcc_of_le Real.two_pi_pos.le]
  simp only [IsMaxOn, IsMaxFilter, eventually_principal, mem_sphere_iff_norm, norm_eq_abs] at HX2
  have := mul_le_mul (hab ⟨⟨v, y1⟩, ⟨ball_subset_closedBall (H hv), hy2⟩⟩)
    (HX2 (circleMap z R y1) (circleMap_mem_sphere z hR.le y1)) (Complex.abs.nonneg _)
    (Complex.abs.nonneg _)
  simp_rw [hfun]
  simp only [circleTransformBoundingFunction, circleTransformDeriv, norm_eq_abs,
    Algebra.id.smul_eq_mul, deriv_circleMap, map_mul, abs_circleMap_zero, abs_I, mul_one, ←
    mul_assoc, mul_inv_rev, inv_I, abs_neg, abs_inv, abs_ofReal, one_mul, abs_two, abs_pow,
    mem_ball, gt_iff_lt, Subtype.coe_mk, SetCoe.forall, mem_prod, mem_closedBall, and_imp,
    Prod.forall, NormedSpace.sphere_nonempty, mem_sphere_iff_norm] at *
  exact this
#align complex.circle_transform_deriv_bound Complex.circleTransformDeriv_bound

end Complex
