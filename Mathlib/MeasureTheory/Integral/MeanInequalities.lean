/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

#align_import measure_theory.integral.mean_inequalities from "leanprover-community/mathlib"@"13bf7613c96a9fd66a81b9020a82cad9a6ea1fcf"

/-!
# Mean value inequalities for integrals

In this file we prove several inequalities on integrals, notably the Hölder inequality and
the Minkowski inequality. The versions for finite sums are in `Analysis.MeanInequalities`.

## Main results

Hölder's inequality for the Lebesgue integral of `ℝ≥0∞` and `ℝ≥0` functions: we prove
`∫ (f * g) ∂μ ≤ (∫ f^p ∂μ) ^ (1/p) * (∫ g^q ∂μ) ^ (1/q)` for `p`, `q` conjugate real exponents
and `α → (E)NNReal` functions in two cases,
* `ENNReal.lintegral_mul_le_Lp_mul_Lq` : ℝ≥0∞ functions,
* `NNReal.lintegral_mul_le_Lp_mul_Lq`  : ℝ≥0 functions.

Minkowski's inequality for the Lebesgue integral of measurable functions with `ℝ≥0∞` values:
we prove `(∫ (f + g)^p ∂μ) ^ (1/p) ≤ (∫ f^p ∂μ) ^ (1/p) + (∫ g^p ∂μ) ^ (1/p)` for `1 ≤ p`.
-/


section LIntegral

/-!
### Hölder's inequality for the Lebesgue integral of ℝ≥0∞ and ℝ≥0 functions

We prove `∫ (f * g) ∂μ ≤ (∫ f^p ∂μ) ^ (1/p) * (∫ g^q ∂μ) ^ (1/q)` for `p`, `q`
conjugate real exponents and `α → (E)NNReal` functions in several cases, the first two being useful
only to prove the more general results:
* `ENNReal.lintegral_mul_le_one_of_lintegral_rpow_eq_one` : ℝ≥0∞ functions for which the
    integrals on the right are equal to 1,
* `ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top` : ℝ≥0∞ functions for which the
    integrals on the right are neither ⊤ nor 0,
* `ENNReal.lintegral_mul_le_Lp_mul_Lq` : ℝ≥0∞ functions,
* `NNReal.lintegral_mul_le_Lp_mul_Lq`  : ℝ≥0 functions.
-/


noncomputable section

open Classical BigOperators NNReal ENNReal MeasureTheory

set_option linter.uppercaseLean3 false

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace ENNReal

theorem lintegral_mul_le_one_of_lintegral_rpow_eq_one {p q : ℝ} (hpq : p.IsConjugateExponent q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_norm : ∫⁻ a, f a ^ p ∂μ = 1)
    (hg_norm : ∫⁻ a, g a ^ q ∂μ = 1) : (∫⁻ a, (f * g) a ∂μ) ≤ 1 := by
  calc
    (∫⁻ a : α, (f * g) a ∂μ) ≤
        ∫⁻ a : α, f a ^ p / ENNReal.ofReal p + g a ^ q / ENNReal.ofReal q ∂μ :=
      lintegral_mono fun a => young_inequality (f a) (g a) hpq
    _ = 1 := by
      simp only [div_eq_mul_inv]
      rw [lintegral_add_left']
      · rw [lintegral_mul_const'' _ (hf.pow_const p), lintegral_mul_const', hf_norm, hg_norm, ←
          div_eq_mul_inv, ← div_eq_mul_inv, hpq.inv_add_inv_conj_ennreal]
        simp [hpq.symm.pos]
      · exact (hf.pow_const _).mul_const _
#align ennreal.lintegral_mul_le_one_of_lintegral_rpow_eq_one ENNReal.lintegral_mul_le_one_of_lintegral_rpow_eq_one

/-- Function multiplied by the inverse of its p-seminorm `(∫⁻ f^p ∂μ) ^ 1/p`-/
def funMulInvSnorm (f : α → ℝ≥0∞) (p : ℝ) (μ : Measure α) : α → ℝ≥0∞ := fun a =>
  f a * ((∫⁻ c, f c ^ p ∂μ) ^ (1 / p))⁻¹
#align ennreal.fun_mul_inv_snorm ENNReal.funMulInvSnorm

theorem fun_eq_funMulInvSnorm_mul_snorm {p : ℝ} (f : α → ℝ≥0∞) (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) ≠ 0)
    (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) {a : α} :
    f a = funMulInvSnorm f p μ a * (∫⁻ c, f c ^ p ∂μ) ^ (1 / p) := by
  simp [funMulInvSnorm, mul_assoc, ENNReal.inv_mul_cancel, hf_nonzero, hf_top]
  -- 🎉 no goals
#align ennreal.fun_eq_fun_mul_inv_snorm_mul_snorm ENNReal.fun_eq_funMulInvSnorm_mul_snorm

theorem funMulInvSnorm_rpow {p : ℝ} (hp0 : 0 < p) {f : α → ℝ≥0∞} {a : α} :
    funMulInvSnorm f p μ a ^ p = f a ^ p * (∫⁻ c, f c ^ p ∂μ)⁻¹ := by
  rw [funMulInvSnorm, mul_rpow_of_nonneg _ _ (le_of_lt hp0)]
  -- ⊢ f a ^ p * ((∫⁻ (c : α), f c ^ p ∂μ) ^ (1 / p))⁻¹ ^ p = f a ^ p * (∫⁻ (c : α) …
  suffices h_inv_rpow : ((∫⁻ c : α, f c ^ p ∂μ) ^ (1 / p))⁻¹ ^ p = (∫⁻ c : α, f c ^ p ∂μ)⁻¹
  -- ⊢ f a ^ p * ((∫⁻ (c : α), f c ^ p ∂μ) ^ (1 / p))⁻¹ ^ p = f a ^ p * (∫⁻ (c : α) …
  · rw [h_inv_rpow]
    -- 🎉 no goals
  rw [inv_rpow, ← rpow_mul, one_div_mul_cancel hp0.ne', rpow_one]
  -- 🎉 no goals
#align ennreal.fun_mul_inv_snorm_rpow ENNReal.funMulInvSnorm_rpow

theorem lintegral_rpow_funMulInvSnorm_eq_one {p : ℝ} (hp0_lt : 0 < p) {f : α → ℝ≥0∞}
    (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) ≠ 0) (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) :
    ∫⁻ c, funMulInvSnorm f p μ c ^ p ∂μ = 1 := by
  simp_rw [funMulInvSnorm_rpow hp0_lt]
  -- ⊢ ∫⁻ (c : α), f c ^ p * (∫⁻ (c : α), f c ^ p ∂μ)⁻¹ ∂μ = 1
  rw [lintegral_mul_const', ENNReal.mul_inv_cancel hf_nonzero hf_top]
  -- ⊢ (∫⁻ (c : α), f c ^ p ∂μ)⁻¹ ≠ ⊤
  rwa [inv_ne_top]
  -- 🎉 no goals
#align ennreal.lintegral_rpow_fun_mul_inv_snorm_eq_one ENNReal.lintegral_rpow_funMulInvSnorm_eq_one

/-- Hölder's inequality in case of finite non-zero integrals -/
theorem lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top {p q : ℝ} (hpq : p.IsConjugateExponent q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hf_nontop : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤)
    (hg_nontop : (∫⁻ a, g a ^ q ∂μ) ≠ ⊤) (hf_nonzero : (∫⁻ a, f a ^ p ∂μ) ≠ 0)
    (hg_nonzero : (∫⁻ a, g a ^ q ∂μ) ≠ 0) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) := by
  let npf := (∫⁻ c : α, f c ^ p ∂μ) ^ (1 / p)
  -- ⊢ ∫⁻ (a : α), (f * g) a ∂μ ≤ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p) * (∫⁻ (a : α), …
  let nqg := (∫⁻ c : α, g c ^ q ∂μ) ^ (1 / q)
  -- ⊢ ∫⁻ (a : α), (f * g) a ∂μ ≤ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p) * (∫⁻ (a : α), …
  calc
    (∫⁻ a : α, (f * g) a ∂μ) =
        ∫⁻ a : α, (funMulInvSnorm f p μ * funMulInvSnorm g q μ) a * (npf * nqg) ∂μ := by
      refine' lintegral_congr fun a => _
      rw [Pi.mul_apply, fun_eq_funMulInvSnorm_mul_snorm f hf_nonzero hf_nontop,
        fun_eq_funMulInvSnorm_mul_snorm g hg_nonzero hg_nontop, Pi.mul_apply]
      ring
    _ ≤ npf * nqg := by
      rw [lintegral_mul_const' (npf * nqg) _
          (by simp [hf_nontop, hg_nontop, hf_nonzero, hg_nonzero, ENNReal.mul_eq_top])]
      refine' mul_le_of_le_one_left' _
      have hf1 := lintegral_rpow_funMulInvSnorm_eq_one hpq.pos hf_nonzero hf_nontop
      have hg1 := lintegral_rpow_funMulInvSnorm_eq_one hpq.symm.pos hg_nonzero hg_nontop
      exact lintegral_mul_le_one_of_lintegral_rpow_eq_one hpq (hf.mul_const _) hf1 hg1
#align ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top

theorem ae_eq_zero_of_lintegral_rpow_eq_zero {p : ℝ} (hp0 : 0 ≤ p) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_zero : ∫⁻ a, f a ^ p ∂μ = 0) : f =ᵐ[μ] 0 := by
  rw [lintegral_eq_zero_iff' (hf.pow_const p)] at hf_zero
  -- ⊢ f =ᵐ[μ] 0
  refine' Filter.Eventually.mp hf_zero (Filter.eventually_of_forall fun x => _)
  -- ⊢ (fun x => f x ^ p) x = OfNat.ofNat 0 x → f x = OfNat.ofNat 0 x
  dsimp only
  -- ⊢ f x ^ p = OfNat.ofNat 0 x → f x = OfNat.ofNat 0 x
  rw [Pi.zero_apply, ← not_imp_not]
  -- ⊢ ¬f x = 0 → ¬f x ^ p = 0
  exact fun hx => (rpow_pos_of_nonneg (pos_iff_ne_zero.2 hx) hp0).ne'
  -- 🎉 no goals
#align ennreal.ae_eq_zero_of_lintegral_rpow_eq_zero ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero

theorem lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero {p : ℝ} (hp0 : 0 ≤ p) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_zero : ∫⁻ a, f a ^ p ∂μ = 0) : (∫⁻ a, (f * g) a ∂μ) = 0 := by
  rw [← @lintegral_zero_fun α _ μ]
  -- ⊢ ∫⁻ (a : α), (f * g) a ∂μ = lintegral μ 0
  refine' lintegral_congr_ae _
  -- ⊢ (fun a => (f * g) a) =ᵐ[μ] fun a => OfNat.ofNat 0 a
  suffices h_mul_zero : f * g =ᵐ[μ] 0 * g
  -- ⊢ (fun a => (f * g) a) =ᵐ[μ] fun a => OfNat.ofNat 0 a
  · rwa [zero_mul] at h_mul_zero
    -- 🎉 no goals
  have hf_eq_zero : f =ᵐ[μ] 0 := ae_eq_zero_of_lintegral_rpow_eq_zero hp0 hf hf_zero
  -- ⊢ f * g =ᵐ[μ] 0 * g
  exact hf_eq_zero.mul (ae_eq_refl g)
  -- 🎉 no goals
#align ennreal.lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero ENNReal.lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero

theorem lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top {p q : ℝ} (hp0_lt : 0 < p) (hq0 : 0 ≤ q)
    {f g : α → ℝ≥0∞} (hf_top : ∫⁻ a, f a ^ p ∂μ = ⊤) (hg_nonzero : (∫⁻ a, g a ^ q ∂μ) ≠ 0) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) := by
  refine' le_trans le_top (le_of_eq _)
  -- ⊢ ⊤ = (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p) * (∫⁻ (a : α), g a ^ q ∂μ) ^ (1 / q)
  have hp0_inv_lt : 0 < 1 / p := by simp [hp0_lt]
  -- ⊢ ⊤ = (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p) * (∫⁻ (a : α), g a ^ q ∂μ) ^ (1 / q)
  rw [hf_top, ENNReal.top_rpow_of_pos hp0_inv_lt]
  -- ⊢ ⊤ = ⊤ * (∫⁻ (a : α), g a ^ q ∂μ) ^ (1 / q)
  simp [hq0, hg_nonzero]
  -- 🎉 no goals
#align ennreal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top

/-- Hölder's inequality for functions `α → ℝ≥0∞`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem lintegral_mul_le_Lp_mul_Lq (μ : Measure α) {p q : ℝ} (hpq : p.IsConjugateExponent q)
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, (f * g) a ∂μ) ≤ (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ q ∂μ) ^ (1 / q) := by
  by_cases hf_zero : ∫⁻ a, f a ^ p ∂μ = 0
  -- ⊢ ∫⁻ (a : α), (f * g) a ∂μ ≤ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p) * (∫⁻ (a : α), …
  · refine' Eq.trans_le _ (zero_le _)
    -- ⊢ ∫⁻ (a : α), (f * g) a ∂μ = 0
    exact lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero hpq.nonneg hf hf_zero
    -- 🎉 no goals
  by_cases hg_zero : ∫⁻ a, g a ^ q ∂μ = 0
  -- ⊢ ∫⁻ (a : α), (f * g) a ∂μ ≤ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p) * (∫⁻ (a : α), …
  · refine' Eq.trans_le _ (zero_le _)
    -- ⊢ ∫⁻ (a : α), (f * g) a ∂μ = 0
    rw [mul_comm]
    -- ⊢ ∫⁻ (a : α), (g * f) a ∂μ = 0
    exact lintegral_mul_eq_zero_of_lintegral_rpow_eq_zero hpq.symm.nonneg hg hg_zero
    -- 🎉 no goals
  by_cases hf_top : ∫⁻ a, f a ^ p ∂μ = ⊤
  -- ⊢ ∫⁻ (a : α), (f * g) a ∂μ ≤ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p) * (∫⁻ (a : α), …
  · exact lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top hpq.pos hpq.symm.nonneg hf_top hg_zero
    -- 🎉 no goals
  by_cases hg_top : ∫⁻ a, g a ^ q ∂μ = ⊤
  -- ⊢ ∫⁻ (a : α), (f * g) a ∂μ ≤ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p) * (∫⁻ (a : α), …
  · rw [mul_comm, mul_comm ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p))]
    -- ⊢ ∫⁻ (a : α), (g * f) a ∂μ ≤ (∫⁻ (a : α), g a ^ q ∂μ) ^ (1 / q) * (∫⁻ (a : α), …
    exact lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_eq_top hpq.symm.pos hpq.nonneg hg_top hf_zero
    -- 🎉 no goals
  -- non-⊤ non-zero case
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq_of_ne_zero_of_ne_top hpq hf hf_top hg_top hf_zero hg_zero
  -- 🎉 no goals
#align ennreal.lintegral_mul_le_Lp_mul_Lq ENNReal.lintegral_mul_le_Lp_mul_Lq

theorem lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top {p : ℝ} {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_top : (∫⁻ a, f a ^ p ∂μ) < ⊤) (hg_top : (∫⁻ a, g a ^ p ∂μ) < ⊤)
    (hp1 : 1 ≤ p) : (∫⁻ a, (f + g) a ^ p ∂μ) < ⊤ := by
  have hp0_lt : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  -- ⊢ ∫⁻ (a : α), (f + g) a ^ p ∂μ < ⊤
  have hp0 : 0 ≤ p := le_of_lt hp0_lt
  -- ⊢ ∫⁻ (a : α), (f + g) a ^ p ∂μ < ⊤
  calc
    (∫⁻ a : α, (f a + g a) ^ p ∂μ) ≤
        ∫⁻ a, (2 : ℝ≥0∞) ^ (p - 1) * f a ^ p + (2 : ℝ≥0∞) ^ (p - 1) * g a ^ p ∂μ := by
      refine' lintegral_mono fun a => _
      dsimp only
      have h_zero_lt_half_rpow : (0 : ℝ≥0∞) < (1 / 2 : ℝ≥0∞) ^ p := by
        rw [← ENNReal.zero_rpow_of_pos hp0_lt]
        exact ENNReal.rpow_lt_rpow (by simp [zero_lt_one]) hp0_lt
      have h_rw : (1 / 2 : ℝ≥0∞) ^ p * (2 : ℝ≥0∞) ^ (p - 1) = 1 / 2 := by
        rw [sub_eq_add_neg, ENNReal.rpow_add _ _ two_ne_zero ENNReal.coe_ne_top, ← mul_assoc, ←
          ENNReal.mul_rpow_of_nonneg _ _ hp0, one_div,
          ENNReal.inv_mul_cancel two_ne_zero ENNReal.coe_ne_top, ENNReal.one_rpow, one_mul,
          ENNReal.rpow_neg_one]
      rw [← ENNReal.mul_le_mul_left (ne_of_lt h_zero_lt_half_rpow).symm _]
      · rw [mul_add, ← mul_assoc, ← mul_assoc, h_rw, ← ENNReal.mul_rpow_of_nonneg _ _ hp0, mul_add]
        refine'
          ENNReal.rpow_arith_mean_le_arith_mean2_rpow (1 / 2 : ℝ≥0∞) (1 / 2 : ℝ≥0∞) (f a) (g a) _
            hp1
        rw [ENNReal.div_add_div_same, one_add_one_eq_two,
          ENNReal.div_self two_ne_zero ENNReal.coe_ne_top]
      · rw [← lt_top_iff_ne_top]
        refine' ENNReal.rpow_lt_top_of_nonneg hp0 _
        rw [one_div, ENNReal.inv_ne_top]
        exact two_ne_zero
    _ < ⊤ := by
      have h_two : (2 : ℝ≥0∞) ^ (p - 1) ≠ ⊤ :=
        ENNReal.rpow_ne_top_of_nonneg (by simp [hp1]) ENNReal.coe_ne_top
      rw [lintegral_add_left', lintegral_const_mul'' _ (hf.pow_const p),
        lintegral_const_mul' _ _ h_two, ENNReal.add_lt_top]
      · exact ⟨ENNReal.mul_lt_top h_two hf_top.ne, ENNReal.mul_lt_top h_two hg_top.ne⟩
      · exact (hf.pow_const p).const_mul _
#align ennreal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top ENNReal.lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top

theorem lintegral_Lp_mul_le_Lq_mul_Lr {α} [MeasurableSpace α] {p q r : ℝ} (hp0_lt : 0 < p)
    (hpq : p < q) (hpqr : 1 / p = 1 / q + 1 / r) (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, (f * g) a ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ a, f a ^ q ∂μ) ^ (1 / q) * (∫⁻ a, g a ^ r ∂μ) ^ (1 / r) := by
  have hp0_ne : p ≠ 0 := (ne_of_lt hp0_lt).symm
  -- ⊢ (∫⁻ (a : α), (f * g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ (a : α), f a ^ q ∂μ) ^ (1 / q …
  have hp0 : 0 ≤ p := le_of_lt hp0_lt
  -- ⊢ (∫⁻ (a : α), (f * g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ (a : α), f a ^ q ∂μ) ^ (1 / q …
  have hq0_lt : 0 < q := lt_of_le_of_lt hp0 hpq
  -- ⊢ (∫⁻ (a : α), (f * g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ (a : α), f a ^ q ∂μ) ^ (1 / q …
  have hq0_ne : q ≠ 0 := (ne_of_lt hq0_lt).symm
  -- ⊢ (∫⁻ (a : α), (f * g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ (a : α), f a ^ q ∂μ) ^ (1 / q …
  have h_one_div_r : 1 / r = 1 / p - 1 / q := by rw [hpqr]; simp
  -- ⊢ (∫⁻ (a : α), (f * g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ (a : α), f a ^ q ∂μ) ^ (1 / q …
  have _ : r ≠ 0 := by
    have hr_inv_pos : 0 < 1 / r := by rwa [h_one_div_r, sub_pos, one_div_lt_one_div hq0_lt hp0_lt]
    rw [one_div, _root_.inv_pos] at hr_inv_pos
    exact (ne_of_lt hr_inv_pos).symm
  let p2 := q / p
  -- ⊢ (∫⁻ (a : α), (f * g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ (a : α), f a ^ q ∂μ) ^ (1 / q …
  let q2 := p2.conjugateExponent
  -- ⊢ (∫⁻ (a : α), (f * g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ (a : α), f a ^ q ∂μ) ^ (1 / q …
  have hp2q2 : p2.IsConjugateExponent q2 :=
    Real.isConjugateExponent_conjugateExponent (by simp [_root_.lt_div_iff, hpq, hp0_lt])
  calc
    (∫⁻ a : α, (f * g) a ^ p ∂μ) ^ (1 / p) = (∫⁻ a : α, f a ^ p * g a ^ p ∂μ) ^ (1 / p) := by
      simp_rw [Pi.mul_apply, ENNReal.mul_rpow_of_nonneg _ _ hp0]
    _ ≤ ((∫⁻ a, f a ^ (p * p2) ∂μ) ^ (1 / p2) *
        (∫⁻ a, g a ^ (p * q2) ∂μ) ^ (1 / q2)) ^ (1 / p) := by
      refine' ENNReal.rpow_le_rpow _ (by simp [hp0])
      simp_rw [ENNReal.rpow_mul]
      exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hp2q2 (hf.pow_const _) (hg.pow_const _)
    _ = (∫⁻ a : α, f a ^ q ∂μ) ^ (1 / q) * (∫⁻ a : α, g a ^ r ∂μ) ^ (1 / r) := by
      rw [@ENNReal.mul_rpow_of_nonneg _ _ (1 / p) (by simp [hp0]), ← ENNReal.rpow_mul, ←
        ENNReal.rpow_mul]
      have hpp2 : p * p2 = q := by
        symm
        rw [mul_comm, ← div_eq_iff hp0_ne]
      have hpq2 : p * q2 = r := by
        rw [← inv_inv r, ← one_div, ← one_div, h_one_div_r]
        field_simp [Real.conjugateExponent, hp0_ne, hq0_ne]
      simp_rw [div_mul_div_comm, mul_one, mul_comm p2, mul_comm q2, hpp2, hpq2]
#align ennreal.lintegral_Lp_mul_le_Lq_mul_Lr ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr

theorem lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow {p q : ℝ}
    (hpq : p.IsConjugateExponent q) {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) :
    (∫⁻ a, f a * g a ^ (p - 1) ∂μ) ≤
      (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) * (∫⁻ a, g a ^ p ∂μ) ^ (1 / q) := by
  refine' le_trans (ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf (hg.pow_const _)) _
  -- ⊢ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p) * (∫⁻ (a : α), (g a ^ (p - 1)) ^ q ∂μ) ^  …
  by_cases hf_zero_rpow : (∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) = 0
  -- ⊢ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p) * (∫⁻ (a : α), (g a ^ (p - 1)) ^ q ∂μ) ^  …
  · rw [hf_zero_rpow, zero_mul]
    -- ⊢ 0 ≤ 0 * (∫⁻ (a : α), g a ^ p ∂μ) ^ (1 / q)
    exact zero_le _
    -- 🎉 no goals
  have hf_top_rpow : (∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) ≠ ⊤ := by
    by_contra h
    refine' hf_top _
    have hp_not_neg : ¬p < 0 := by simp [hpq.nonneg]
    simpa [hpq.pos, hp_not_neg] using h
  refine' (ENNReal.mul_le_mul_left hf_zero_rpow hf_top_rpow).mpr (le_of_eq _)
  -- ⊢ (∫⁻ (a : α), (g a ^ (p - 1)) ^ q ∂μ) ^ (1 / q) = (∫⁻ (a : α), g a ^ p ∂μ) ^  …
  congr
  -- ⊢ (fun a => (g a ^ (p - 1)) ^ q) = fun a => g a ^ p
  ext1 a
  -- ⊢ (g a ^ (p - 1)) ^ q = g a ^ p
  rw [← ENNReal.rpow_mul, hpq.sub_one_mul_conj]
  -- 🎉 no goals
#align ennreal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow

theorem lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add {p q : ℝ}
    (hpq : p.IsConjugateExponent q) {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) (hg : AEMeasurable g μ) (hg_top : (∫⁻ a, g a ^ p ∂μ) ≠ ⊤) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ≤
      ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) *
        (∫⁻ a, (f a + g a) ^ p ∂μ) ^ (1 / q) := by
  calc
    (∫⁻ a, (f + g) a ^ p ∂μ) ≤ ∫⁻ a, (f + g) a * (f + g) a ^ (p - 1) ∂μ := by
      refine' lintegral_mono fun a => _
      dsimp only
      by_cases h_zero : (f + g) a = 0
      · rw [h_zero, ENNReal.zero_rpow_of_pos hpq.pos]
        exact zero_le _
      by_cases h_top : (f + g) a = ⊤
      · rw [h_top, ENNReal.top_rpow_of_pos hpq.sub_one_pos, ENNReal.top_mul_top]
        exact le_top
      refine' le_of_eq _
      nth_rw 2 [← ENNReal.rpow_one ((f + g) a)]
      rw [← ENNReal.rpow_add _ _ h_zero h_top, add_sub_cancel'_right]
    _ = (∫⁻ a : α, f a * (f + g) a ^ (p - 1) ∂μ) + ∫⁻ a : α, g a * (f + g) a ^ (p - 1) ∂μ := by
      have h_add_m : AEMeasurable (fun a : α => (f + g) a ^ (p - 1 : ℝ)) μ :=
        (hf.add hg).pow_const _
      have h_add_apply :
        (∫⁻ a : α, (f + g) a * (f + g) a ^ (p - 1) ∂μ) =
          ∫⁻ a : α, (f a + g a) * (f + g) a ^ (p - 1) ∂μ :=
        rfl
      simp_rw [h_add_apply, add_mul]
      rw [lintegral_add_left' (hf.mul h_add_m)]
    _ ≤
        ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) *
          (∫⁻ a, (f a + g a) ^ p ∂μ) ^ (1 / q) := by
      rw [add_mul]
      exact
        add_le_add
          (lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq hf (hf.add hg) hf_top)
          (lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow hpq hg (hf.add hg) hg_top)
#align ennreal.lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add ENNReal.lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add

private theorem lintegral_Lp_add_le_aux {p q : ℝ} (hpq : p.IsConjugateExponent q) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hf_top : (∫⁻ a, f a ^ p ∂μ) ≠ ⊤) (hg : AEMeasurable g μ)
    (hg_top : (∫⁻ a, g a ^ p ∂μ) ≠ ⊤) (h_add_zero : (∫⁻ a, (f + g) a ^ p ∂μ) ≠ 0)
    (h_add_top : (∫⁻ a, (f + g) a ^ p ∂μ) ≠ ⊤) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p) := by
  have hp_not_nonpos : ¬p ≤ 0 := by simp [hpq.pos]
  -- ⊢ (∫⁻ (a : α), (f + g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p …
  have htop_rpow : (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≠ ⊤ := by
    by_contra h
    exact h_add_top (@ENNReal.rpow_eq_top_of_nonneg _ (1 / p) (by simp [hpq.nonneg]) h)
  have h0_rpow : (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≠ 0 := by
    simp [h_add_zero, h_add_top, hpq.nonneg, hp_not_nonpos, -Pi.add_apply]
  suffices h :
    1 ≤
      (∫⁻ a : α, (f + g) a ^ p ∂μ) ^ (-(1 / p)) *
        ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a : α, g a ^ p ∂μ) ^ (1 / p))
  · rwa [← mul_le_mul_left h0_rpow htop_rpow, ← mul_assoc, ← rpow_add _ _ h_add_zero h_add_top, ←
      sub_eq_add_neg, _root_.sub_self, rpow_zero, one_mul, mul_one] at h
  have h :
    (∫⁻ a : α, (f + g) a ^ p ∂μ) ≤
      ((∫⁻ a : α, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a : α, g a ^ p ∂μ) ^ (1 / p)) *
        (∫⁻ a : α, (f + g) a ^ p ∂μ) ^ (1 / q) :=
    lintegral_rpow_add_le_add_snorm_mul_lintegral_rpow_add hpq hf hf_top hg hg_top
  have h_one_div_q : 1 / q = 1 - 1 / p := by
    nth_rw 2 [← hpq.inv_add_inv_conj]
    ring
  simp_rw [h_one_div_q, sub_eq_add_neg 1 (1 / p), ENNReal.rpow_add _ _ h_add_zero h_add_top,
    rpow_one] at h
  conv_rhs at h => enter [2]; rw [mul_comm]
  -- ⊢ 1 ≤ (∫⁻ (a : α), (f + g) a ^ p ∂μ) ^ (-(1 / p)) * ((∫⁻ (a : α), f a ^ p ∂μ)  …
  conv_lhs at h => rw [← one_mul (∫⁻ a : α, (f + g) a ^ p ∂μ)]
  -- ⊢ 1 ≤ (∫⁻ (a : α), (f + g) a ^ p ∂μ) ^ (-(1 / p)) * ((∫⁻ (a : α), f a ^ p ∂μ)  …
  rwa [← mul_assoc, ENNReal.mul_le_mul_right h_add_zero h_add_top, mul_comm] at h
  -- 🎉 no goals

/-- Minkowski's inequality for functions `α → ℝ≥0∞`: the `ℒp` seminorm of the sum of two
functions is bounded by the sum of their `ℒp` seminorms. -/
theorem lintegral_Lp_add_le {p : ℝ} {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hp1 : 1 ≤ p) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤
      (∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp1
  -- ⊢ (∫⁻ (a : α), (f + g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p …
  by_cases hf_top : ∫⁻ a, f a ^ p ∂μ = ⊤
  -- ⊢ (∫⁻ (a : α), (f + g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p …
  · simp [hf_top, hp_pos]
    -- 🎉 no goals
  by_cases hg_top : ∫⁻ a, g a ^ p ∂μ = ⊤
  -- ⊢ (∫⁻ (a : α), (f + g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p …
  · simp [hg_top, hp_pos]
    -- 🎉 no goals
  by_cases h1 : p = 1
  -- ⊢ (∫⁻ (a : α), (f + g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p …
  · refine' le_of_eq _
    -- ⊢ (∫⁻ (a : α), (f + g) a ^ p ∂μ) ^ (1 / p) = (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p …
    simp_rw [h1, one_div_one, ENNReal.rpow_one]
    -- ⊢ ∫⁻ (a : α), (f + g) a ∂μ = ∫⁻ (a : α), f a ∂μ + ∫⁻ (a : α), g a ∂μ
    exact lintegral_add_left' hf _
    -- 🎉 no goals
  have hp1_lt : 1 < p := by
    refine' lt_of_le_of_ne hp1 _
    symm
    exact h1
  have hpq := Real.isConjugateExponent_conjugateExponent hp1_lt
  -- ⊢ (∫⁻ (a : α), (f + g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p …
  by_cases h0 : (∫⁻ a, (f + g) a ^ p ∂μ) = 0
  -- ⊢ (∫⁻ (a : α), (f + g) a ^ p ∂μ) ^ (1 / p) ≤ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p …
  · rw [h0, @ENNReal.zero_rpow_of_pos (1 / p) (by simp [lt_of_lt_of_le zero_lt_one hp1])]
    -- ⊢ 0 ≤ (∫⁻ (a : α), f a ^ p ∂μ) ^ (1 / p) + (∫⁻ (a : α), g a ^ p ∂μ) ^ (1 / p)
    exact zero_le _
    -- 🎉 no goals
  have htop : (∫⁻ a, (f + g) a ^ p ∂μ) ≠ ⊤ := by
    rw [← Ne.def] at hf_top hg_top
    rw [← lt_top_iff_ne_top] at hf_top hg_top ⊢
    exact lintegral_rpow_add_lt_top_of_lintegral_rpow_lt_top hf hf_top hg_top hp1
  exact lintegral_Lp_add_le_aux hpq hf hf_top hg hg_top h0 htop
  -- 🎉 no goals
#align ennreal.lintegral_Lp_add_le ENNReal.lintegral_Lp_add_le

/-- Variant of Minkowski's inequality for functions `α → ℝ≥0∞` in `ℒp` with `p ≤ 1`: the `ℒp`
seminorm of the sum of two functions is bounded by a constant multiple of the sum
of their `ℒp` seminorms. -/
theorem lintegral_Lp_add_le_of_le_one {p : ℝ} {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤
      (2 : ℝ≥0∞) ^ (1 / p - 1) * ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) := by
  rcases eq_or_lt_of_le hp0 with (rfl | hp)
  -- ⊢ (∫⁻ (a : α), (f + g) a ^ 0 ∂μ) ^ (1 / 0) ≤ 2 ^ (1 / 0 - 1) * ((∫⁻ (a : α), f …
  · simp only [Pi.add_apply, rpow_zero, lintegral_one, _root_.div_zero, zero_sub]
    -- ⊢ 1 ≤ 2 ^ (-1) * (1 + 1)
    norm_num
    -- ⊢ 1 ≤ 2 ^ (-1) * 2
    rw [rpow_neg, rpow_one, ENNReal.inv_mul_cancel two_ne_zero two_ne_top]
    -- 🎉 no goals
  calc
    (∫⁻ a, (f + g) a ^ p ∂μ) ^ (1 / p) ≤ ((∫⁻ a, f a ^ p ∂μ) + ∫⁻ a, g a ^ p ∂μ) ^ (1 / p) := by
      apply rpow_le_rpow _ (div_nonneg zero_le_one hp0)
      rw [← lintegral_add_left' (hf.pow_const p)]
      exact lintegral_mono fun a => rpow_add_le_add_rpow _ _ hp0 hp1
    _ ≤ (2 : ℝ≥0∞) ^ (1 / p - 1) * ((∫⁻ a, f a ^ p ∂μ) ^ (1 / p) + (∫⁻ a, g a ^ p ∂μ) ^ (1 / p)) :=
      rpow_add_le_mul_rpow_add_rpow _ _ ((one_le_div hp).2 hp1)
#align ennreal.lintegral_Lp_add_le_of_le_one ENNReal.lintegral_Lp_add_le_of_le_one

end ENNReal

/-- Hölder's inequality for functions `α → ℝ≥0`. The integral of the product of two functions
is bounded by the product of their `ℒp` and `ℒq` seminorms when `p` and `q` are conjugate
exponents. -/
theorem NNReal.lintegral_mul_le_Lp_mul_Lq {p q : ℝ} (hpq : p.IsConjugateExponent q) {f g : α → ℝ≥0}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, (f * g) a ∂μ) ≤
      (∫⁻ a, (f a : ℝ≥0∞) ^ p ∂μ) ^ (1 / p) * (∫⁻ a, (g a : ℝ≥0∞) ^ q ∂μ) ^ (1 / q) := by
  simp_rw [Pi.mul_apply, ENNReal.coe_mul]
  -- ⊢ ∫⁻ (a : α), ↑(f a) * ↑(g a) ∂μ ≤ (∫⁻ (a : α), ↑(f a) ^ p ∂μ) ^ (1 / p) * (∫⁻ …
  exact ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.coe_nnreal_ennreal hg.coe_nnreal_ennreal
  -- 🎉 no goals
#align nnreal.lintegral_mul_le_Lp_mul_Lq NNReal.lintegral_mul_le_Lp_mul_Lq

end

end LIntegral
