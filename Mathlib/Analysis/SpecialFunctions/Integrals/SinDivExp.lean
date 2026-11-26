/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman, Kim Morrison
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Basic.Real.Sign

import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Laplace transform of `sin (b t) / t`

For `0 < a` and every real `b`,

`∫ t in Ioi 0, sin (b t) e^{-a t} = b / (a² + b²)` and
`∫ t in Ioi 0, sin (b t) / t · e^{-a t} = arctan (b / a)`.

The second identity is the classical Laplace transform of `sin (b t) / t`. Writing
`sin (b t) / t · e^{-a t} = ∫ u in Ioi a, sin (b t) e^{-u t}` and exchanging the order of
integration reduces it to the first one, and `-arctan (b / u)` is an antiderivative of
`b / (u² + b²)`. Letting `a → 0⁺` gives the limit `sign b · π / 2`: this is the Dirichlet integral
`∫₀^∞ sin t / t dt = π / 2` in the sense of Abel summation.

The function `sin (b t) / t` is not Lebesgue integrable on `(0, ∞)` for `b ≠ 0`. Hence at `a = 0`
the Bochner integral and `arctan (b / 0) = 0` both vanish, and the closed form holds for all
`0 ≤ a`.

## Main results

* `Real.integral_sin_mul_mul_exp_neg_mul_Ioi`: the Laplace transform of `sin (b t)`;
* `Real.not_integrableOn_sin_mul_div_Ioi`: `sin (b t) / t` is not integrable on `(0, ∞)`;
* `Real.integrableOn_sin_mul_div_mul_exp_neg_mul_Ioi`: integrability of the damped integrand;
* `Real.integral_sin_mul_div_mul_exp_neg_mul_Ioi`: the Laplace transform of `sin (b t) / t`;
* `Real.tendsto_integral_sin_mul_div_mul_exp_neg_mul_Ioi`: its limit as `a → 0⁺`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace Real

/-- **The Laplace transform of `sin (b t)`.** For `0 < a` and every real `b`,
`∫ t in Ioi 0, sin (b t) e^{-a t} = b / (a² + b²)`. -/
theorem integral_sin_mul_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫ t in Ioi (0 : ℝ), sin (b * t) * exp (-(a * t)) = b / (a ^ 2 + b ^ 2) := by
  set z : ℂ := -a + b * Complex.I
  have hz : z.re < 0 := by simp [z, ha]
  have hpt (t : ℝ) : sin (b * t) * exp (-(a * t)) = (Complex.exp (z * t)).im := by
    rw [Complex.exp_im]
    simp [z, mul_comm]
  simp_rw [hpt]
  have := integral_im (integrableOn_exp_mul_complex_Ioi hz 0)
  simp only [RCLike.im_to_complex] at this
  rw [this, integral_exp_mul_complex_Ioi hz 0]
  simp [z, Complex.normSq, sq, neg_div]

/-- For `b ≠ 0`, the function `sin (b t) / t` is not integrable on `(0, ∞)`. -/
theorem not_integrableOn_sin_mul_div_Ioi {b : ℝ} (hb : b ≠ 0) :
    ¬ IntegrableOn (fun t ↦ sin (b * t) / t) (Ioi 0) := by
  wlog hb' : 0 < b generalizing b
  · intro h
    refine this (neg_ne_zero.2 hb) (neg_pos.2 ((not_lt.1 hb').lt_of_ne hb)) ?_
    simpa [neg_mul, sin_neg, neg_div] using h.neg
  intro h
  -- Shifting by a quarter period `d` turns `sin (b t)` into `-cos (b t)`, and
  -- `|sin| + |cos| ≥ 1` then dominates `t⁻¹`, which is not integrable on `(d, ∞)`.
  set d := π / (2 * b)
  have hd : 0 < d := by positivity
  have hbd : b * d = π / 2 := by simp only [d]; field_simp
  have hshift : IntegrableOn (fun t ↦ ‖sin (b * (t - d)) / (t - d)‖) (Ioi d) := by
    have := (measurePreserving_sub_right volume d).integrableOn_comp_preimage
      (measurableEmbedding_subRight d) (f := fun t ↦ ‖sin (b * t) / t‖) (s := Ioi 0)
    simpa [preimage_sub_const_Ioi, Function.comp_def] using this.2 h.norm
  refine not_integrableOn_Ioi_inv (a := d) ?_
  refine ((IntegrableOn.mono_set h.norm (Ioi_subset_Ioi hd.le)).add hshift).mono'
    measurable_inv.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : d < t)
  have ht0 : 0 < t := hd.trans ht
  have htd : 0 < t - d := sub_pos.2 ht
  rw [Pi.add_apply, mul_sub, hbd, sin_sub_pi_div_two, norm_eq_abs, norm_eq_abs, norm_eq_abs,
    abs_div, abs_div, abs_neg, abs_inv, abs_of_pos ht0, abs_of_pos htd]
  have hsc : 1 ≤ |sin (b * t)| + |cos (b * t)| := by
    have := sin_sq_add_cos_sq (b * t)
    nlinarith [abs_sin_le_one (b * t), abs_cos_le_one (b * t), sq_abs (sin (b * t)),
      sq_abs (cos (b * t)), abs_nonneg (sin (b * t)), abs_nonneg (cos (b * t))]
  calc t⁻¹ ≤ (|sin (b * t)| + |cos (b * t)|) / t := by
        rw [inv_eq_one_div]; gcongr
    _ ≤ |sin (b * t)| / t + |cos (b * t)| / (t - d) := by
        rw [add_div]; gcongr; linarith

/-- For `0 < a` and every real `b`, the function `sin (b t) / t · e^{-a t}` is integrable on
`(0, ∞)`. -/
theorem integrableOn_sin_mul_div_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IntegrableOn (fun t ↦ sin (b * t) / t * exp (-(a * t))) (Ioi 0) := by
  have hexp : IntegrableOn (fun t : ℝ ↦ |b| * exp (-(a * t))) (Ioi 0) := by
    have h := exp_neg_integrableOn_Ioi 0 ha
    simp only [neg_mul] at h
    exact h.const_mul |b|
  refine hexp.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  have hsin : |sin (b * t)| ≤ |b| * t := by
    simpa [abs_mul, abs_of_pos ht] using abs_sin_le_abs (x := b * t)
  rw [norm_eq_abs, abs_mul, abs_div, abs_exp, abs_of_pos ht]
  gcongr
  rwa [div_le_iff₀ ht]

/-- For real `a`, `c` and `0 ≤ t`, `∫ u in Ioi a, c e^{-u t} = c / t · e^{-a t}`. -/
private theorem integral_Ioi_mul_exp_neg_mul (c : ℝ) {a t : ℝ} (ht : 0 ≤ t) :
    ∫ u in Ioi a, c * exp (-(u * t)) = c / t * exp (-(a * t)) := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [Measure.real]
  have h := integral_exp_mul_Ioi (neg_lt_zero.2 ht) a
  simp_rw [show ∀ u, -(u * t) = -t * u from fun u ↦ by ring]
  rw [integral_const_mul, h]
  field_simp

/-- For `0 < a` and every real `b`, `∫ u in Ioi a, b / (u² + b²) = arctan (b / a)`. -/
private theorem integral_Ioi_div_sq_add_sq {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫ u in Ioi a, b / (u ^ 2 + b ^ 2) = arctan (b / a) := by
  wlog hb : 0 ≤ b generalizing b
  · have := this (-b) (by linarith)
    simp only [neg_div, neg_sq, integral_neg, arctan_neg, neg_inj] at this
    exact this
  have hderiv : ∀ u ∈ Ici a, HasDerivAt (fun u ↦ -arctan (b / u)) (b / (u ^ 2 + b ^ 2)) u := by
    intro u (hu : a ≤ u)
    have hu0 : u ≠ 0 := (ha.trans_le hu).ne'
    refine (((hasDerivAt_inv hu0).const_mul b).arctan.neg).congr_deriv ?_
    field_simp
  have hlim : Tendsto (fun u ↦ -arctan (b / u)) atTop (𝓝 0) := by
    simpa using ((continuous_arctan.tendsto 0).comp
      (tendsto_const_nhds.div_atTop tendsto_id)).neg
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv (fun u _ ↦ by positivity) hlim]
  ring

/-- **The Laplace transform of `sin (b t) / t`.** For `0 ≤ a` and every real `b`,
`∫ t in Ioi 0, sin (b t) / t · e^{-a t} = arctan (b / a)`. At `a = 0` both sides vanish, since
`sin (b t) / t` is not integrable on `(0, ∞)` unless `b = 0`. -/
theorem integral_sin_mul_div_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    ∫ t in Ioi (0 : ℝ), sin (b * t) / t * exp (-(a * t)) = arctan (b / a) := by
  rcases ha.eq_or_lt with rfl | ha
  · rcases eq_or_ne b 0 with rfl | hb
    · simp
    simp only [zero_mul, neg_zero, exp_zero, mul_one, div_zero, arctan_zero]
    exact integral_undef (not_integrableOn_sin_mul_div_Ioi hb)
  set F : ℝ → ℝ → ℝ := fun t u ↦ sin (b * t) * exp (-(u * t))
  have hinner (t : ℝ) (ht : 0 < t) : Integrable (F t) (volume.restrict (Ioi a)) := by
    simpa [F, show ∀ u, -(u * t) = -t * u from fun u ↦ by ring] using
      (integrableOn_exp_mul_Ioi (neg_lt_zero.2 ht) a).const_mul (sin (b * t))
  have hF : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi a))) := by
    refine (integrable_prod_iff (by fun_prop)).2 ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hinner t ht
    · refine (integrableOn_sin_mul_div_mul_exp_neg_mul_Ioi ha b).norm.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      simp only [Function.uncurry_apply_pair, F, norm_eq_abs, abs_mul, abs_div, abs_exp,
        abs_of_pos ht]
      rw [integral_Ioi_mul_exp_neg_mul _ ht.le]
  calc ∫ t in Ioi (0 : ℝ), sin (b * t) / t * exp (-(a * t))
      = ∫ t in Ioi (0 : ℝ), ∫ u in Ioi a, F t u := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
        exact (integral_Ioi_mul_exp_neg_mul _ ht.le).symm
    _ = ∫ u in Ioi a, ∫ t in Ioi (0 : ℝ), F t u := integral_integral_swap hF
    _ = ∫ u in Ioi a, b / (u ^ 2 + b ^ 2) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : a < u) ↦ ?_
        exact integral_sin_mul_mul_exp_neg_mul_Ioi (ha.trans hu) b
    _ = arctan (b / a) := integral_Ioi_div_sq_add_sq ha b

/-- **Abel limit of the Dirichlet integral.** For every real `b`, as `a → 0⁺`,
`∫ t in Ioi 0, sin (b t) / t · e^{-a t} → sign b · π / 2`. -/
theorem tendsto_integral_sin_mul_div_mul_exp_neg_mul_Ioi (b : ℝ) :
    Tendsto (fun a ↦ ∫ t in Ioi (0 : ℝ), sin (b * t) / t * exp (-(a * t)))
      (𝓝[>] 0) (𝓝 (sign b * (π / 2))) := by
  have hcongr : (fun a ↦ arctan (b * a⁻¹)) =ᶠ[𝓝[>] 0]
      fun a ↦ ∫ t in Ioi (0 : ℝ), sin (b * t) / t * exp (-(a * t)) := by
    filter_upwards [self_mem_nhdsWithin] with a (ha : 0 < a)
    rw [integral_sin_mul_div_mul_exp_neg_mul_Ioi ha.le, div_eq_mul_inv]
  refine Tendsto.congr' hcongr ?_
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · rw [sign_of_neg hb, neg_one_mul]
    exact (tendsto_arctan_atBot.comp
      (tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg hb)).mono_right nhdsWithin_le_nhds
  · simp
  · rw [sign_of_pos hb, one_mul]
    exact (tendsto_arctan_atTop.comp (tendsto_inv_nhdsGT_zero.const_mul_atTop hb)).mono_right
      nhdsWithin_le_nhds

end Real
