/-
Copyright (c) 2026 Alireza Behtash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alireza Behtash
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The integral of `cosh ^ (-ν)`

For `0 < ν`, `∫ x, cosh x ^ (-ν) = √π * Γ(ν / 2) / Γ((ν + 1) / 2)`, which is the Beta value
`B(1 / 2, ν / 2)`.

## Main results

* `Real.integrable_cosh_rpow_neg`: `cosh ^ (-ν)` is integrable on `ℝ` for `0 < ν`.
* `Real.integral_cosh_rpow_neg_Ioi`, `Real.integral_cosh_rpow_neg_Iic`: the integrals over the two
  half lines.
* `Real.integral_cosh_rpow_neg`: the integral over `ℝ`.

## Implementation notes

The substitution `t = 1 - (cosh x ^ 2)⁻¹ = tanh x ^ 2` maps `(0, ∞)` bijectively onto `(0, 1)` and
turns `2 * ∫ x in Ioi 0, cosh x ^ (-ν)` into the Beta integral
`∫ t in 0..1, t ^ (1 / 2 - 1) * (1 - t) ^ (ν / 2 - 1)`.
-/

public section

open MeasureTheory Set

namespace Real

private lemma sq_rpow {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : (x ^ 2) ^ y = x ^ (2 * y) := by
  rw [← rpow_natCast_mul hx]
  norm_num

theorem cosh_rpow_neg_le {ν : ℝ} (hν : 0 ≤ ν) (x : ℝ) :
    cosh x ^ (-ν) ≤ 2 ^ ν * exp (-(ν * |x|)) := by
  have h1 : exp |x| / 2 ≤ cosh x := by
    rw [← cosh_abs, cosh_eq]
    linarith [exp_pos (-|x|)]
  refine (rpow_le_rpow_of_nonpos (by positivity) h1 (neg_nonpos.2 hν)).trans_eq ?_
  rw [div_rpow (exp_pos _).le zero_le_two, ← exp_mul, rpow_neg zero_le_two]
  field_simp

theorem integrableOn_cosh_rpow_neg_Ioi {ν : ℝ} (hν : 0 < ν) :
    IntegrableOn (fun x ↦ cosh x ^ (-ν)) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hν).const_mul (2 ^ ν)) ?_ ?_
  · exact (continuous_cosh.rpow_const fun x ↦ .inl (cosh_pos x).ne').aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
    rw [norm_of_nonneg (rpow_nonneg (cosh_pos x).le _)]
    simpa [abs_of_pos hx] using cosh_rpow_neg_le hν.le x

theorem integrableOn_cosh_rpow_neg_Iic {ν : ℝ} (hν : 0 < ν) :
    IntegrableOn (fun x ↦ cosh x ^ (-ν)) (Iic 0) := by
  refine Integrable.mono' ((integrableOn_exp_mul_Iic hν 0).const_mul (2 ^ ν)) ?_ ?_
  · exact (continuous_cosh.rpow_const fun x ↦ .inl (cosh_pos x).ne').aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Iic fun x (hx : x ≤ 0) ↦ ?_
    rw [norm_of_nonneg (rpow_nonneg (cosh_pos x).le _)]
    simpa [abs_of_nonpos hx] using cosh_rpow_neg_le hν.le x

theorem integrable_cosh_rpow_neg {ν : ℝ} (hν : 0 < ν) :
    Integrable (fun x ↦ cosh x ^ (-ν)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := 0)]
  exact (integrableOn_cosh_rpow_neg_Iic hν).union (integrableOn_cosh_rpow_neg_Ioi hν)

/-- The substitution `t = 1 - (cosh x ^ 2)⁻¹`. -/
private noncomputable def coshSub (x : ℝ) : ℝ := 1 - (cosh x ^ 2)⁻¹

private lemma hasDerivAt_coshSub (x : ℝ) :
    HasDerivAt coshSub (2 * sinh x / cosh x ^ 3) x := by
  have hc := cosh_pos x
  have h1 : HasDerivAt (fun y ↦ cosh y ^ 2) (2 * cosh x * sinh x) x := by
    convert (hasDerivAt_cosh x).pow 2 using 1
    simp
  have h2 : 2 * sinh x / cosh x ^ 3 = -(-(2 * cosh x * sinh x) / (cosh x ^ 2) ^ 2) := by
    field_simp
  rw [h2]
  exact (h1.inv (by positivity)).const_sub 1

private lemma coshSub_image : coshSub '' Ioi 0 = Ioo 0 1 := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : 1 < cosh x := one_lt_cosh.2 (ne_of_gt hx)
    have h2 : (cosh x ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
    have h3 : 0 < (cosh x ^ 2)⁻¹ := by positivity
    exact ⟨by simp only [coshSub]; linarith, by simp only [coshSub]; linarith⟩
  · rintro ⟨h0, h1⟩
    have hs : √t ∈ Ioo (0 : ℝ) 1 := ⟨sqrt_pos.2 h0, by rw [sqrt_lt' one_pos]; simpa using h1⟩
    refine ⟨artanh √t, artanh_pos hs, ?_⟩
    rw [coshSub, cosh_artanh ⟨by linarith [hs.1], hs.2⟩, sq_sqrt h0.le, div_pow, one_pow,
      sq_sqrt (by linarith), inv_div, div_one]
    ring

private lemma coshSub_injOn : InjOn coshSub (Ioi 0) := by
  intro x (hx : 0 < x) y (hy : 0 < y) hxy
  simp only [coshSub, sub_right_inj, inv_inj] at hxy
  have hc : cosh x = cosh y := (pow_left_inj₀ (cosh_pos x).le (cosh_pos y).le two_ne_zero).1 hxy
  have h := le_antisymm (cosh_le_cosh.1 hc.le) (cosh_le_cosh.1 hc.ge)
  rwa [abs_of_pos hx, abs_of_pos hy] at h

private lemma coshSub_integrand {ν x : ℝ} (hx : 0 < x) :
    |2 * sinh x / cosh x ^ 3| • (coshSub x ^ ((1 : ℝ) / 2 - 1) * (1 - coshSub x) ^ (ν / 2 - 1)) =
      2 * cosh x ^ (-ν) := by
  have hc := cosh_pos x
  have hs : 0 < sinh x := sinh_pos_iff.2 hx
  have e1 : coshSub x = (sinh x / cosh x) ^ 2 := by
    rw [coshSub, div_pow, sinh_sq]
    field_simp
  have e2 : 1 - coshSub x = (cosh x ^ 2)⁻¹ := by rw [coshSub]; ring
  rw [e2, e1, sq_rpow (div_pos hs hc).le, inv_rpow (by positivity), sq_rpow hc.le,
    ← rpow_neg hc.le, abs_of_pos (by positivity), smul_eq_mul,
    show 2 * ((1 : ℝ) / 2 - 1) = -1 by norm_num, rpow_neg_one,
    show -(2 * (ν / 2 - 1)) = 2 + -ν by ring, rpow_add hc, rpow_two]
  have := rpow_pos_of_pos hc (-ν)
  field_simp

theorem integral_cosh_rpow_neg_Ioi {ν : ℝ} (hν : 0 < ν) :
    ∫ x in Ioi 0, cosh x ^ (-ν) = √π * Gamma (ν / 2) / Gamma ((ν + 1) / 2) / 2 := by
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun x _ ↦ (hasDerivAt_coshSub x).hasDerivWithinAt) coshSub_injOn
    (fun t ↦ t ^ ((1 : ℝ) / 2 - 1) * (1 - t) ^ (ν / 2 - 1))
  rw [coshSub_image, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow_mul_one_sub_rpow one_half_pos (by positivity), Gamma_one_half_eq,
    setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ coshSub_integrand hx,
    integral_const_mul, show (1 : ℝ) / 2 + ν / 2 = (ν + 1) / 2 by ring] at key
  linarith

theorem integral_cosh_rpow_neg_Iic {ν : ℝ} (hν : 0 < ν) :
    ∫ x in Iic 0, cosh x ^ (-ν) = √π * Gamma (ν / 2) / Gamma ((ν + 1) / 2) / 2 := by
  rw [← integral_cosh_rpow_neg_Ioi hν, ← neg_zero, ← integral_comp_neg_Ioi]
  simp

/-- For `0 < ν`, `∫ x, cosh x ^ (-ν) = √π * Γ(ν / 2) / Γ((ν + 1) / 2)`. -/
theorem integral_cosh_rpow_neg {ν : ℝ} (hν : 0 < ν) :
    ∫ x, cosh x ^ (-ν) = √π * Gamma (ν / 2) / Gamma ((ν + 1) / 2) := by
  rw [← intervalIntegral.integral_Iic_add_Ioi (integrableOn_cosh_rpow_neg_Iic hν)
    (integrableOn_cosh_rpow_neg_Ioi hν), integral_cosh_rpow_neg_Iic hν,
    integral_cosh_rpow_neg_Ioi hν]
  ring

end Real
