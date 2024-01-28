/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The two-variable Jacobi theta function

This file defines the two-variable Jacobi theta function

$$\theta(z, \tau) = \sum_{n \in \mathbb{Z}} \exp (2 i \pi n z + i \pi n ^ 2 \tau),$$

and proves the functional equation relating the values at `(z, τ)` and `(z / τ, -1 / τ)`,
using Poisson's summation formula. We also show holomorphy (in both variables individually,
not jointly).
-/

open Complex Real Asymptotics Filter Topology

open scoped Real BigOperators

/-- The two-variable Jacobi theta function,
`θ z τ = ∑' (n : ℤ), cexp (2 * π * I * n * z + π * I * n ^ 2 * τ)`.

The sum is only convergent for `0 < im τ`; we are implictly extending it by 0 for other values of
`τ`. -/
noncomputable def jacobiTheta₂ (z τ : ℂ) : ℂ :=
  ∑' n : ℤ, cexp (2 * π * I * n * z + π * I * n ^ 2 * τ)

/-- A uniform bound for the summands in the Jacobi theta function on compact subsets. -/
lemma jacobiTheta₂_term_bound {S T : ℝ} (hT : 0 < T) {z τ : ℂ}
    (hz : |im z| ≤ S) (hτ : T ≤ im τ) (n : ℤ) :
    ‖cexp (2 * π * I * n * z + π * I * n ^ 2 * τ)‖ ≤ Real.exp (-π * (T * n ^ 2 - 2 * S * |n|)) := by
  rw [Complex.norm_eq_abs, Complex.abs_exp, (by push_cast; ring :
    2 * π * I * n * z + π * I * n ^ 2 * τ = (π * (2 * n) :) * z * I + (π * n ^ 2 :) * τ * I),
    add_re, mul_I_re, im_ofReal_mul, mul_I_re, im_ofReal_mul, Real.exp_le_exp, neg_mul, ← neg_add,
    neg_le_neg_iff, mul_assoc π, mul_assoc π, ← mul_add, mul_le_mul_left pi_pos, add_comm,
    mul_comm T]
  refine add_le_add (mul_le_mul le_rfl hτ hT.le (sq_nonneg _)) ?_
  rw [← mul_neg, mul_assoc, mul_assoc, mul_le_mul_left two_pos, mul_comm, neg_mul, ← mul_neg]
  refine le_trans ?_ (neg_abs_le _)
  rw [mul_neg, neg_le_neg_iff, abs_mul, Int.cast_abs]
  exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)

lemma summable_jacobiTheta₂_term_bound (S : ℝ) {T : ℝ} (hT : 0 < T) :
    Summable (fun n : ℤ ↦ Real.exp (-π * (T * n ^ 2 - 2 * S * |n|))) := by
  suffices : Summable (fun n : ℕ ↦ Real.exp (-π * (T * n ^ 2 - 2 * S * n)))
  · apply summable_int_of_summable_nat <;>
    simpa only [Int.cast_neg, neg_sq, abs_neg, Int.cast_ofNat, Nat.abs_cast]
  apply summable_of_isBigO_nat summable_exp_neg_nat
  refine Real.isBigO_exp_comp_exp_comp.mpr (Tendsto.isBoundedUnder_le_atBot ?_)
  rw [← tendsto_neg_atTop_iff]
  simp only [neg_mul, Pi.sub_apply, sub_neg_eq_add, neg_add_rev, neg_neg]
  suffices : Tendsto (fun n ↦ n * (π * T * n - (2 * π * S + 1)) : ℕ → ℝ) atTop atTop
  · convert this using 2 with n; ring
  refine tendsto_nat_cast_atTop_atTop.atTop_mul_atTop (tendsto_atTop_add_const_right _ _ ?_)
  exact tendsto_nat_cast_atTop_atTop.const_mul_atTop (mul_pos pi_pos hT)

/-- Differentiability of `Θ z τ` in `τ`, for fixed `z`. (This is weaker than differentiability
in both variables simultaneously, but we do not have a version of
`differentiableOn_tsum_of_summable_norm` in multiple variables yet.) -/
lemma differentiableAt_jacobiTheta₂ (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
    DifferentiableAt ℂ (jacobiTheta₂ z) τ := by
  obtain ⟨T, hT⟩ := exists_between hτ
  let V := {b | T < im b}
  have : V ∈ 𝓝 τ := continuous_im.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hT.2)
  refine DifferentiableOn.differentiableAt ?_ this
  apply differentiableOn_tsum_of_summable_norm
  · exact summable_jacobiTheta₂_term_bound |im z| hT.1
  · refine fun i ↦ (Complex.differentiable_exp.comp ?_).differentiableOn
    exact (differentiable_const _).add ((differentiable_const _).mul differentiable_id)
  · exact continuous_im.isOpen_preimage _ isOpen_Ioi
  · exact fun i ξ (hξ : T < im ξ) ↦ jacobiTheta₂_term_bound hT.1 (le_refl _) hξ.le i

/-- The two-variable Jacobi theta function is periodic in `τ` with period 2. -/
lemma jacobiTheta₂_add_right (z τ : ℂ) : jacobiTheta₂ z (τ + 2) = jacobiTheta₂ z τ := by
  refine tsum_congr (fun n ↦ ?_)
  simp_rw [Complex.exp_add]
  suffices cexp (π * I * n ^ 2 * 2 : ℂ) = 1 by rw [mul_add, Complex.exp_add, this, mul_one]
  rw [(by push_cast; ring : (π * I * n ^ 2 * 2 : ℂ) = (n ^ 2 :) * (2 * π * I)), exp_int_mul,
    exp_two_pi_mul_I, one_zpow]

/-- The two-variable Jacobi theta function is periodic in `z` with period 1. -/
lemma jacobiTheta₂_add_left (z τ : ℂ) : jacobiTheta₂ (z + 1) τ = jacobiTheta₂ z τ := by
  refine tsum_congr (fun n ↦ ?_)
  simp_rw [mul_add, mul_one, Complex.exp_add]
  suffices cexp (2 * ↑π * I * n) = 1 by rw [this, mul_one]
  simpa only [mul_comm] using exp_int_mul_two_pi_mul_I n

/-- The two-variable Jacobi theta function is quasi-periodic in `z` with period `τ`. -/
lemma jacobiTheta₂_add_left' (z τ : ℂ) :
    jacobiTheta₂ (z + τ) τ = cexp (-π * I * (τ + 2 * z)) * jacobiTheta₂ z τ := by
  conv_rhs => erw [← tsum_mul_left, ← (Equiv.addRight (1 : ℤ)).tsum_eq]
  refine tsum_congr (fun n ↦ ?_)
  rw [← Complex.exp_add, Equiv.coe_addRight, Int.cast_add]
  ring_nf

/-- The two-variable Jacobi theta function is even in `z`. -/
lemma jacobiTheta₂_neg_left (z τ : ℂ) : jacobiTheta₂ (-z) τ = jacobiTheta₂ z τ := by
  conv_lhs => rw [jacobiTheta₂, ← Equiv.tsum_eq (Equiv.neg ℤ)]
  refine tsum_congr (fun n ↦ ?_)
  rw [Equiv.neg_apply, Int.cast_neg, neg_sq]
  ring_nf

/-- The functional equation for the Jacobi theta function: `jacobiTheta₂ x τ` is an explict factor
times `jacobiTheta₂ (x / τ) (-1 / τ)`. This is the key lemma behind the proof of the functional
equation for Dirichlet L-series. -/
theorem jacobiTheta₂_functional_equation (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
    jacobiTheta₂ z τ =
      1 / (-I * τ) ^ (1 / 2 : ℂ) * cexp (-π * I * z ^ 2 / τ) * jacobiTheta₂ (z / τ) (-1 / τ) := by
  have h0 : τ ≠ 0; contrapose! hτ; rw [hτ, zero_im]
  have h2 : 0 < (-I * τ).re
  · simpa only [neg_mul, neg_re, mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, neg_neg] using hτ
  calc
    _ = ∑' n : ℤ, cexp (-π * (-I * τ) * ↑n ^ 2 + 2 * π * (I * z) * ↑n) :=
      tsum_congr (fun n ↦ by ring_nf)
    _ = 1 / (-I * τ) ^ (1 / 2 : ℂ) * ∑' (n : ℤ), cexp (-π / (-I * τ) * (n + I * (I * z)) ^ 2) := by
      rw [tsum_exp_neg_quadratic h2]
    _ = 1 / (-I * τ) ^ (1 / 2 : ℂ) * cexp (π * I * (-1 / τ) * z ^ 2) *
        ∑' (n : ℤ), cexp (2 * π * I * n * (z / τ) + π * I * n ^ 2 * (-1 / τ)) := by
      simp_rw [mul_assoc _ (cexp _), ← tsum_mul_left (a := cexp _), ← Complex.exp_add]
      congr 2 with n : 1; congr 1
      field_simp [I_ne_zero]
      ring_nf
      simp_rw [I_sq, I_pow_four]
      ring_nf
    _ = _ := by
      congr 3
      ring
