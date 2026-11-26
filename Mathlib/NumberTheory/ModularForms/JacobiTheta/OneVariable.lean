/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-! # Jacobi's theta function

This file defines the one-variable Jacobi theta function

$$\theta(\tau) = \sum_{n \in \mathbb{Z}} \exp (i \pi n ^ 2 \tau),$$

and proves the modular transformation properties `θ (τ + 2) = θ τ` and
`θ (-1 / τ) = (-I * τ) ^ (1 / 2) * θ τ`, using Poisson's summation formula for the latter. We also
show that `θ` is differentiable on `ℍ`, and `θ(τ) - 1` has exponential decay as `im τ → ∞`.

We also define the Jacobi theta functions `θ₂ = jacobiTheta₁₀` and `θ₄ = jacobiTheta₀₁` (with
`θ₃ = jacobiTheta`), and prove the transformation laws of `θ₂`, `θ₃` and `θ₄` under `τ ↦ 1 + τ`
and `τ ↦ -1 / τ`. Finally, we show that `θ₂` and `θ₄` are differentiable on `ℍ`, and that
`θ₂(τ)` and `θ₄(τ) - 1` have exponential decay as `im τ → ∞`.

## Notation

With `open scoped JacobiTheta`, we write `θ₂`, `θ₃` and `θ₄` for `jacobiTheta₁₀`, `jacobiTheta`
and `jacobiTheta₀₁` respectively.
-/

@[expose] public section

open Complex Real Asymptotics Filter Topology

open scoped Real UpperHalfPlane

/-- Jacobi's one-variable theta function `∑' (n : ℤ), exp (π * I * n ^ 2 * τ)`. -/
noncomputable def jacobiTheta (τ : ℂ) : ℂ := ∑' n : ℤ, cexp (π * I * (n : ℂ) ^ 2 * τ)

lemma jacobiTheta_eq_jacobiTheta₂ (τ : ℂ) : jacobiTheta τ = jacobiTheta₂ 0 τ :=
  tsum_congr (by simp [jacobiTheta₂_term])

theorem jacobiTheta_two_add (τ : ℂ) : jacobiTheta (2 + τ) = jacobiTheta τ := by
  simp_rw [jacobiTheta_eq_jacobiTheta₂, add_comm, jacobiTheta₂_add_right]

theorem jacobiTheta_T_sq_smul (τ : ℍ) : jacobiTheta (ModularGroup.T ^ 2 • τ :) = jacobiTheta τ := by
  suffices (ModularGroup.T ^ 2 • τ :) = (2 : ℂ) + ↑τ by simp_rw [this, jacobiTheta_two_add]
  have : ModularGroup.T ^ (2 : ℕ) = ModularGroup.T ^ (2 : ℤ) := rfl
  simp_rw [this, UpperHalfPlane.modular_T_zpow_smul, UpperHalfPlane.coe_vadd]
  norm_cast

theorem jacobiTheta_S_smul (τ : ℍ) :
    jacobiTheta ↑(ModularGroup.S • τ) = (-I * τ) ^ (1 / 2 : ℂ) * jacobiTheta τ := by
  have h0 : (τ : ℂ) ≠ 0 := ne_of_apply_ne im (zero_im.symm ▸ ne_of_gt τ.coe_im_pos)
  have h1 : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl <| mul_ne_zero (neg_ne_zero.mpr I_ne_zero) h0
  simp_rw [UpperHalfPlane.modular_S_smul, jacobiTheta_eq_jacobiTheta₂, ← ofReal_zero]
  norm_cast
  simp_rw [jacobiTheta₂_functional_equation 0 τ, zero_pow two_ne_zero, mul_zero, zero_div,
    Complex.exp_zero, mul_one, ← mul_assoc, mul_one_div, div_self h1, one_mul,
    inv_neg, neg_div, one_div]

/-!
## The theta functions `θ₂` and `θ₄`

In the characteristic notation, `θ₂`, `θ₃` and `θ₄` are `θ₁₀`, `θ₀₀` and `θ₀₁` respectively, which
explains the names `jacobiTheta₁₀` and `jacobiTheta₀₁`.
-/

/-- The Jacobi theta function `θ₄(τ) = ∑' (n : ℤ), (-1) ^ n * exp (π * I * n ^ 2 * τ)`, also
denoted `θ₀₁`. -/
noncomputable def jacobiTheta₀₁ (τ : ℂ) : ℂ :=
  ∑' n : ℤ, (-1 : ℂ) ^ n * cexp (π * I * (n : ℂ) ^ 2 * τ)

lemma jacobiTheta₀₁_apply (τ : ℂ) :
    jacobiTheta₀₁ τ = ∑' n : ℤ, (-1 : ℂ) ^ n * cexp (π * I * (n : ℂ) ^ 2 * τ) := rfl

/-- The Jacobi theta function `θ₂(τ) = ∑' (n : ℤ), exp (π * I * (n + 1 / 2) ^ 2 * τ)`, also
denoted `θ₁₀`. -/
noncomputable def jacobiTheta₁₀ (τ : ℂ) : ℂ :=
  ∑' n : ℤ, cexp (π * I * ((n : ℂ) + 1 / 2) ^ 2 * τ)

lemma jacobiTheta₁₀_apply (τ : ℂ) :
    jacobiTheta₁₀ τ = ∑' n : ℤ, cexp (π * I * ((n : ℂ) + 1 / 2) ^ 2 * τ) := rfl

namespace JacobiTheta

@[inherit_doc] scoped notation "θ₂" => jacobiTheta₁₀
@[inherit_doc] scoped notation "θ₃" => jacobiTheta
@[inherit_doc] scoped notation "θ₄" => jacobiTheta₀₁

end JacobiTheta

open scoped JacobiTheta

lemma jacobiTheta₀₁_eq_jacobiTheta₂ (τ : ℂ) : θ₄ τ = jacobiTheta₂ (1 / 2) τ := by
  refine tsum_congr fun n ↦ ?_
  rw [jacobiTheta₂_term, ← exp_pi_mul_I, ← Complex.exp_intCast_mul, ← Complex.exp_add]
  ring_nf

lemma jacobiTheta₁₀_eq_jacobiTheta₂ (τ : ℂ) :
    θ₂ τ = cexp (π * I * τ / 4) * jacobiTheta₂ (τ / 2) τ := by
  rw [jacobiTheta₂, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rw [jacobiTheta₂_term, ← Complex.exp_add]
  ring_nf

theorem jacobiTheta_one_add (τ : ℂ) : θ₃ (1 + τ) = θ₄ τ := by
  rw [jacobiTheta_eq_jacobiTheta₂, add_comm, jacobiTheta₂_add_one_right, zero_add,
    jacobiTheta₀₁_eq_jacobiTheta₂]

theorem jacobiTheta₀₁_one_add (τ : ℂ) : θ₄ (1 + τ) = θ₃ τ := by
  rw [jacobiTheta₀₁_eq_jacobiTheta₂, add_comm, jacobiTheta₂_add_one_right, add_halves,
    jacobiTheta_eq_jacobiTheta₂, ← jacobiTheta₂_add_left 0, zero_add]

theorem jacobiTheta₁₀_one_add (τ : ℂ) : θ₂ (1 + τ) = cexp (π * I / 4) * θ₂ τ := by
  have : (τ + 1) / 2 + 1 / 2 = τ / 2 + 1 := by ring
  rw [jacobiTheta₁₀_eq_jacobiTheta₂, add_comm, jacobiTheta₂_add_one_right, this,
    jacobiTheta₂_add_left, jacobiTheta₁₀_eq_jacobiTheta₂, ← mul_assoc, ← Complex.exp_add]
  ring_nf

theorem jacobiTheta₀₁_S_smul (τ : ℍ) :
    θ₄ ↑(ModularGroup.S • τ) = (-I * τ) ^ (1 / 2 : ℂ) * θ₂ τ := by
  have h : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by simp [cpow_eq_zero_iff, τ.ne_zero]
  have h0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, jacobiTheta₀₁_eq_jacobiTheta₂,
    jacobiTheta₁₀_eq_jacobiTheta₂, jacobiTheta₂_functional_equation _ τ,
    (by field : (τ : ℂ) / 2 / τ = 1 / 2), (by field : -1 / (τ : ℂ) = (-(τ : ℂ))⁻¹),
    (by field : -π * I * ((τ : ℂ) / 2) ^ 2 / τ = -(π * I * τ / 4)), Complex.exp_neg]
  field

theorem jacobiTheta₁₀_S_smul (τ : ℍ) :
    θ₂ ↑(ModularGroup.S • τ) = (-I * τ) ^ (1 / 2 : ℂ) * θ₄ τ := by
  have h : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by simp [cpow_eq_zero_iff, τ.ne_zero]
  rw [UpperHalfPlane.modular_S_smul, jacobiTheta₀₁_eq_jacobiTheta₂,jacobiTheta₁₀_eq_jacobiTheta₂,
    jacobiTheta₂_functional_equation _ τ, ← mul_assoc, ← jacobiTheta₂_neg_left, ← mul_assoc,
      mul_one_div_cancel h]
  ring_nf

/-!
## Bounds and differentiability on the upper half-plane
-/

section

variable {τ : ℂ} (hτ : 0 < τ.im)
include hτ

theorem norm_exp_mul_sq_le (n : ℤ) :
    ‖cexp (π * I * (n : ℂ) ^ 2 * τ)‖ ≤ rexp (-π * τ.im) ^ n.natAbs := by
  let y := rexp (-π * τ.im)
  have h : y < 1 := exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hτ)
  refine (le_of_eq ?_).trans (?_ : y ^ n ^ 2 ≤ _)
  · rw [norm_exp]
    have : (π * I * n ^ 2 * τ : ℂ).re = -π * τ.im * (n : ℝ) ^ 2 := by
      rw [(by push_cast; ring : (π * I * n ^ 2 * τ : ℂ) = (π * n ^ 2 : ℝ) * (τ * I)),
        re_ofReal_mul, mul_I_re]
      ring
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (sq_nonneg n)
    rw [this, exp_mul, ← Int.cast_pow, rpow_intCast, hm, zpow_natCast]
  · have : n ^ 2 = (n.natAbs ^ 2 :) := by rw [Nat.cast_pow, Int.natAbs_sq]
    rw [this, zpow_natCast]
    exact pow_le_pow_of_le_one (exp_pos _).le h.le ((sq n.natAbs).symm ▸ n.natAbs.le_mul_self)

theorem hasSum_nat_jacobiTheta :
    HasSum (fun n : ℕ => cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ)) ((jacobiTheta τ - 1) / 2) := by
  have := hasSum_jacobiTheta₂_term 0 hτ
  simp_rw [jacobiTheta₂_term, mul_zero, zero_add, ← jacobiTheta_eq_jacobiTheta₂] at this
  have := this.nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at this
  simp_rw [Finset.sum_range_one, Int.cast_neg, Int.cast_natCast, Nat.cast_zero, neg_zero,
    Int.cast_zero, sq (0 : ℂ), mul_zero, zero_mul, neg_sq, ← mul_two,
    Complex.exp_zero, add_sub_assoc, (by norm_num : (1 : ℂ) - 1 * 2 = -1), ← sub_eq_add_neg,
    Nat.cast_add, Nat.cast_one] at this
  convert this.div_const 2 using 1
  simp_rw [mul_div_cancel_right₀ _ (two_ne_zero' ℂ)]

theorem jacobiTheta_eq_tsum_nat :
    jacobiTheta τ = ↑1 + ↑2 * ∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ) := by
  rw [(hasSum_nat_jacobiTheta hτ).tsum_eq, mul_div_cancel₀ _ (two_ne_zero' ℂ), ← add_sub_assoc,
    add_sub_cancel_left]

/-- An explicit upper bound for `‖jacobiTheta τ - 1‖`. -/
theorem norm_jacobiTheta_sub_one_le :
    ‖jacobiTheta τ - 1‖ ≤ 2 / (1 - rexp (-π * τ.im)) * rexp (-π * τ.im) := by
  suffices ‖∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ)‖ ≤
      rexp (-π * τ.im) / (1 - rexp (-π * τ.im)) by
    calc
      ‖jacobiTheta τ - 1‖ = ↑2 * ‖∑' n : ℕ, cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ)‖ := by
        rw [sub_eq_iff_eq_add'.mpr (jacobiTheta_eq_tsum_nat hτ), norm_mul, Complex.norm_two]
      _ ≤ 2 * (rexp (-π * τ.im) / (1 - rexp (-π * τ.im))) := by gcongr
      _ = 2 / (1 - rexp (-π * τ.im)) * rexp (-π * τ.im) := by rw [div_mul_comm, mul_comm]
  have : ∀ n : ℕ, ‖cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ)‖ ≤ rexp (-π * τ.im) ^ (n + 1) := by
    intro n
    simpa only [Int.cast_add, Int.cast_one] using! norm_exp_mul_sq_le hτ (n + 1)
  have s : HasSum (fun n : ℕ =>
      rexp (-π * τ.im) ^ (n + 1)) (rexp (-π * τ.im) / (1 - rexp (-π * τ.im))) := by
    simp_rw [pow_succ', div_eq_mul_inv, hasSum_mul_left_iff (Real.exp_ne_zero _)]
    exact hasSum_geometric_of_lt_one (exp_pos (-π * τ.im)).le
      (exp_lt_one_iff.mpr <| mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hτ)
  have aux : Summable fun n : ℕ => ‖cexp (π * I * ((n : ℂ) + 1) ^ 2 * τ)‖ :=
    .of_nonneg_of_le (fun n => norm_nonneg _) this s.summable
  exact (norm_tsum_le_tsum_norm aux).trans ((aux.tsum_mono s.summable this).trans_eq s.tsum_eq)

theorem differentiableAt_jacobiTheta :
    DifferentiableAt ℂ jacobiTheta τ := by
  simp_rw [funext jacobiTheta_eq_jacobiTheta₂]
  exact differentiableAt_jacobiTheta₂_snd 0 hτ

theorem continuousAt_jacobiTheta : ContinuousAt jacobiTheta τ :=
  (differentiableAt_jacobiTheta hτ).continuousAt

theorem differentiableAt_jacobiTheta₀₁ : DifferentiableAt ℂ jacobiTheta₀₁ τ := by
  rw [funext jacobiTheta₀₁_eq_jacobiTheta₂]
  exact differentiableAt_jacobiTheta₂_snd _ hτ

theorem continuousAt_jacobiTheta₀₁ : ContinuousAt jacobiTheta₀₁ τ :=
  (differentiableAt_jacobiTheta₀₁ hτ).continuousAt

theorem differentiableAt_jacobiTheta₁₀ :
    DifferentiableAt ℂ jacobiTheta₁₀ τ := by
  rw [funext jacobiTheta₁₀_eq_jacobiTheta₂]
  fun_prop

theorem continuousAt_jacobiTheta₁₀ : ContinuousAt jacobiTheta₁₀ τ :=
  (differentiableAt_jacobiTheta₁₀ hτ).continuousAt

end

/-!
## Asymptotics as `im τ → ∞`
-/

/-- The norm of `jacobiTheta τ - 1` decays exponentially as `im τ → ∞`. -/
theorem isBigO_at_im_infty_jacobiTheta_sub_one :
    (fun τ => jacobiTheta τ - 1) =O[comap im atTop] fun τ => rexp (-π * τ.im) := by
  simp_rw [isBigO_iff, Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨2 / (1 - rexp (-(π * 1))), 1, fun y hy τ hτ =>
    (norm_jacobiTheta_sub_one_le (hτ.symm ▸ zero_lt_one.trans_le hy : 0 < im τ)).trans ?_⟩
  rw [Real.norm_eq_abs, Real.abs_exp, hτ, neg_mul]
  gcongr
  simp [pi_pos]

private lemma tendsto_rexp_neg_mul_im {c : ℝ} (hc : 0 < c) :
    Tendsto (fun τ : ℂ ↦ rexp (-c * τ.im)) (comap im atTop) (𝓝 0) :=
  tendsto_exp_atBot.comp (tendsto_comap.const_mul_atTop_of_neg (neg_lt_zero.mpr hc))

/-- `jacobiTheta τ` tends to `1` as `im τ → ∞`. -/
theorem tendsto_jacobiTheta_at_im_infty : Tendsto jacobiTheta (comap im atTop) (𝓝 1) :=
  tendsto_sub_nhds_zero_iff.mp <|
    isBigO_at_im_infty_jacobiTheta_sub_one.trans_tendsto (tendsto_rexp_neg_mul_im pi_pos)

/-- The norm of `θ₄ τ - 1` decays exponentially as `im τ → ∞`. -/
theorem isBigO_at_im_infty_jacobiTheta₀₁_sub_one :
    (θ₄ · - 1) =O[comap im atTop] fun τ ↦ rexp (-π * τ.im) := by
  have h : Tendsto (1 + ·) (comap im atTop) (comap im atTop) :=
    tendsto_comap_iff.mpr <| by simp [Function.comp_def, tendsto_comap]
  simpa [Function.comp_def, jacobiTheta_one_add] using
    isBigO_at_im_infty_jacobiTheta_sub_one.comp_tendsto h

/-- `θ₄ τ` tends to `1` as `im τ → ∞`. -/
theorem tendsto_jacobiTheta₀₁_at_im_infty : Tendsto jacobiTheta₀₁ (comap im atTop) (𝓝 1) :=
  tendsto_sub_nhds_zero_iff.mp <|
    isBigO_at_im_infty_jacobiTheta₀₁_sub_one.trans_tendsto (tendsto_rexp_neg_mul_im pi_pos)

/-- The norm of `θ₂ τ` decays exponentially as `im τ → ∞`. -/
theorem isBigO_at_im_infty_jacobiTheta₁₀ :
    θ₂ =O[comap im atTop] fun τ ↦ rexp (-π * τ.im / 4) := by
  have hs : Summable fun n : ℤ ↦ ‖jacobiTheta₂_term n (I / 2) I‖ :=
    summable_norm_iff.mpr <| (summable_jacobiTheta₂_term_iff _ _).mpr (by simp)
  simp_rw [isBigO_iff, Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨∑' n : ℤ, ‖jacobiTheta₂_term n (I / 2) I‖, 1, fun y hy τ hτ ↦ ?_⟩
  -- `jacobiTheta₂ (τ / 2) τ` is bounded for `1 ≤ im τ`
  have h₁ : ‖jacobiTheta₂ (τ / 2) τ‖ ≤ ∑' n : ℤ, ‖jacobiTheta₂_term n (I / 2) I‖ := by
    refine tsum_of_norm_bounded hs.hasSum fun n ↦ ?_
    rw [norm_jacobiTheta₂_term, norm_jacobiTheta₂_term, Real.exp_le_exp, div_ofNat_im,
      div_ofNat_im, I_im]
    have hn : (0 : ℝ) ≤ n ^ 2 + n := by norm_cast; nlinarith
    nlinarith [mul_nonneg (mul_nonneg pi_pos.le hn) (sub_nonneg.mpr (hτ ▸ hy))]
  grw [jacobiTheta₁₀_eq_jacobiTheta₂, norm_mul, mul_comm, h₁]
  simp [Complex.norm_exp, Real.norm_eq_abs, Real.abs_exp]

/-- `θ₂ τ` tends to `0` as `im τ → ∞`. -/
theorem tendsto_jacobiTheta₁₀_at_im_infty : Tendsto jacobiTheta₁₀ (comap im atTop) (𝓝 0) :=
  isBigO_at_im_infty_jacobiTheta₁₀.trans_tendsto <|
    (tendsto_rexp_neg_mul_im (c := π / 4) (by positivity)).congr fun τ ↦ by ring_nf
