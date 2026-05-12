/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Evaluation of specific improper integrals

This file contains some integrability results, and evaluations of integrals, over `ℝ` or over
half-infinite intervals in `ℝ`.

These lemmas are stated in terms of either `Iic` or `Ioi` (neglecting `Iio` and `Ici`) to match
mathlib's conventions for integrals over finite intervals (see `intervalIntegral`).

## See also

- `Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`: specific integrals over finite intervals
- `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`: integral of `exp (-x ^ 2)`
- `Mathlib/Analysis/SpecialFunctions/JapaneseBracket.lean`: integrability of `(1+‖x‖)^(-r)`.
-/

public section


open Real Set Filter MeasureTheory intervalIntegral

open scoped Topology

theorem integrableOn_exp_Iic (c : ℝ) : IntegrableOn exp (Iic c) := by
  refine
    integrableOn_Iic_of_intervalIntegral_norm_bounded (exp c) c
      (fun y => intervalIntegrable_exp.1) tendsto_id
      (eventually_of_mem (Iic_mem_atBot 0) fun y _ => ?_)
  simp_rw [norm_of_nonneg (exp_pos _).le, integral_exp, sub_le_self_iff]
  exact (exp_pos _).le

theorem integrableOn_exp_neg_Ioi (c : ℝ) : IntegrableOn (fun (x : ℝ) => exp (-x)) (Ioi c) :=
  Iff.mp integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_Iic (-c)).comp_neg_Ici

theorem integral_exp_Iic (c : ℝ) : ∫ x : ℝ in Iic c, exp x = exp c := by
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Iic _ (integrableOn_exp_Iic _) tendsto_id) ?_
  simp_rw [integral_exp, show 𝓝 (exp c) = 𝓝 (exp c - 0) by rw [sub_zero]]
  exact tendsto_exp_atBot.const_sub _

theorem integral_exp_Iic_zero : ∫ x : ℝ in Iic 0, exp x = 1 :=
  exp_zero ▸ integral_exp_Iic 0

theorem integral_exp_neg_Ioi (c : ℝ) : (∫ x : ℝ in Ioi c, exp (-x)) = exp (-c) := by
  simpa only [integral_comp_neg_Ioi] using integral_exp_Iic (-c)

theorem integral_exp_neg_Ioi_zero : (∫ x : ℝ in Ioi 0, exp (-x)) = 1 := by
  simpa only [neg_zero, exp_zero] using integral_exp_neg_Ioi 0

theorem integrableOn_exp_mul_complex_Ioi {a : ℂ} (ha : a.re < 0) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Complex.exp (a * x)) (Ioi c) := by
  refine (integrable_norm_iff ?_).mp ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · simpa [Complex.norm_exp] using
      (integrableOn_Ioi_comp_mul_left_iff (fun x => exp (-x)) c (a := -a.re) (by simpa)).mpr <|
        integrableOn_exp_neg_Ioi _

theorem integrableOn_exp_mul_complex_Iic {a : ℂ} (ha : 0 < a.re) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Complex.exp (a * x)) (Iic c) := by
  simpa using Iff.mpr integrableOn_Iic_iff_integrableOn_Iio
    (integrableOn_exp_mul_complex_Ioi (a := -a) (by simpa) (-c)).comp_neg_Iio

theorem integrableOn_exp_mul_Ioi {a : ℝ} (ha : a < 0) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Ioi c) := by
  have := Integrable.norm <| integrableOn_exp_mul_complex_Ioi (a := a) (by simpa using ha) c
  simpa [Complex.norm_exp] using this

theorem integrableOn_exp_mul_Iic {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (a * x)) (Iic c) := by
  have := Integrable.norm <| integrableOn_exp_mul_complex_Iic (a := a) (by simpa using ha) c
  simpa [Complex.norm_exp] using this

theorem integral_exp_mul_complex_Ioi {a : ℂ} (ha : a.re < 0) (c : ℝ) :
    ∫ x : ℝ in Set.Ioi c, Complex.exp (a * x) = - Complex.exp (a * c) / a := by
  refine tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi c
    (integrableOn_exp_mul_complex_Ioi ha c) tendsto_id) ?_
  simp_rw [integral_exp_mul_complex (c := a) (by aesop), id_eq]
  suffices Tendsto (fun x : ℝ ↦ Complex.exp (a * x)) atTop (𝓝 0) by
    simpa using this.sub_const _ |>.div_const _
  simpa [Complex.tendsto_exp_nhds_zero_iff] using tendsto_const_nhds.neg_mul_atTop ha tendsto_id

theorem integral_exp_mul_complex_Iic {a : ℂ} (ha : 0 < a.re) (c : ℝ) :
    ∫ x : ℝ in Set.Iic c, Complex.exp (a * x) = Complex.exp (a * c) / a := by
  simpa [neg_mul, ← mul_neg, ← Complex.ofReal_neg,
    integral_comp_neg_Ioi (f := fun x : ℝ ↦ Complex.exp (a * x))]
    using integral_exp_mul_complex_Ioi (a := -a) (by simpa) (-c)

theorem integral_exp_mul_Ioi {a : ℝ} (ha : a < 0) (c : ℝ) :
    ∫ x : ℝ in Set.Ioi c, Real.exp (a * x) = - Real.exp (a * c) / a := by
  simp_rw [Real.exp, ← RCLike.re_to_complex, Complex.ofReal_mul]
  rw [integral_re, integral_exp_mul_complex_Ioi (by simpa using ha), RCLike.re_to_complex,
    RCLike.re_to_complex, Complex.div_ofReal_re, Complex.neg_re]
  exact integrableOn_exp_mul_complex_Ioi (by simpa using ha) _

theorem integral_exp_mul_Iic {a : ℝ} (ha : 0 < a) (c : ℝ) :
    ∫ x : ℝ in Set.Iic c, Real.exp (a * x) = Real.exp (a * c) / a := by
  simpa [neg_mul, ← mul_neg, integral_comp_neg_Ioi (f := fun x : ℝ ↦ Real.exp (a * x))]
    using integral_exp_mul_Ioi (a := -a) (by simpa) (-c)

/-! ### Tail integrals of `x ^ m * exp (-(a * x))`

The integral `∫ x in Ioi R, x ^ m * exp (-(a * x))` is the upper incomplete Gamma function
evaluated at the integer `m + 1`. The lemmas below give explicit closed forms for
`m = 0, 1, 2, 3, 4, 5`. They are useful for tail bounds in the theory of Dirichlet series,
modular forms, and `L`-functions.
-/

/-- The tail integral of `exp (-(a * x))` on `(R, +∞)`. -/
theorem integral_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) (R : ℝ) :
    ∫ x : ℝ in Set.Ioi R, Real.exp (-(a * x)) = Real.exp (-(a * R)) / a := by
  have h := integral_exp_mul_Ioi (a := -a) (by linarith) R
  have ha' : a ≠ 0 := ne_of_gt ha
  have heq : ∀ x : ℝ, -a * x = -(a * x) := fun _ => by ring
  simp_rw [heq] at h
  rw [h]
  field_simp

/-- The tail integral of `x * exp (-(a * x))` on `(R, +∞)`, for `0 < a` and `0 ≤ R`. -/
theorem integral_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) {R : ℝ} (hR : 0 ≤ R) :
    ∫ x : ℝ in Set.Ioi R, x * Real.exp (-(a * x)) =
      (a * R + 1) * Real.exp (-(a * R)) / a ^ 2 := by
  set F : ℝ → ℝ := fun x => -(a * x + 1) * Real.exp (-(a * x)) / a ^ 2 with hF
  have ha' : a ≠ 0 := ne_of_gt ha
  have hderiv : ∀ x ∈ Set.Ici R, HasDerivAt F (x * Real.exp (-(a * x))) x := by
    intro x _
    -- HasDerivAt of `y ↦ -(a*y + 1)` with derivative `-a`
    have h1 : HasDerivAt (fun y : ℝ => -(a * y + 1)) (-a) x := by
      have e1 : HasDerivAt (fun y : ℝ => a * y + 1) a x := by
        have := ((hasDerivAt_id x).const_mul a).add_const (1 : ℝ)
        simpa using this
      exact e1.neg.congr_deriv (by ring)
    -- HasDerivAt of `y ↦ exp(-(a*y))` with derivative `-a * exp(-(a*x))`
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(a * y))) (-a * Real.exp (-(a * x))) x := by
      have hd : HasDerivAt (fun y : ℝ => -(a * y)) (-a) x := by
        have := ((hasDerivAt_id x).const_mul a).neg
        simpa using this
      have hc := (Real.hasDerivAt_exp (-(a * x))).comp x hd
      exact hc.congr_deriv (by ring)
    have hprod := (h1.mul h2).div_const (a ^ 2)
    refine hprod.congr_deriv ?_
    field_simp
    ring
  have hnn : ∀ x ∈ Set.Ioi R, 0 ≤ x * Real.exp (-(a * x)) := fun x hx =>
    mul_nonneg (le_of_lt (lt_of_le_of_lt hR hx)) (Real.exp_pos _).le
  have htendsto : Tendsto F atTop (𝓝 0) := by
    have key : Tendsto (fun x : ℝ => x * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
      refine h.congr' ?_
      filter_upwards with x
      rw [Real.rpow_one, show -a * x = -(a * x) from by ring]
    have key' : Tendsto (fun x : ℝ => Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx' : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
      rw [Real.rpow_zero, one_mul, show -a * x = -(a * x) from by ring]
    -- F(x) = (-a/a^2) * (x * exp(-(a*x))) + (-1/a^2) * exp(-(a*x))
    have heq : F = fun x => (-a / a ^ 2) * (x * Real.exp (-(a * x))) +
        (-1 / a ^ 2) * Real.exp (-(a * x)) := by
      ext x
      simp only [F]
      field_simp
      ring
    rw [heq]
    have := (key.const_mul (-a / a ^ 2)).add (key'.const_mul (-1 / a ^ 2))
    simpa using this
  have hint := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnn htendsto
  rw [hint]
  change 0 - F R = _
  simp only [F]
  ring

/-- The tail integral of `x ^ 2 * exp (-(a * x))` on `(R, +∞)`, for `0 < a`. -/
theorem integral_pow_two_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) (R : ℝ) :
    ∫ x : ℝ in Set.Ioi R, x ^ 2 * Real.exp (-(a * x)) =
      ((a * R) ^ 2 + 2 * (a * R) + 2) * Real.exp (-(a * R)) / a ^ 3 := by
  set F : ℝ → ℝ := fun x => -((a * x) ^ 2 + 2 * (a * x) + 2) * Real.exp (-(a * x)) / a ^ 3 with hF
  have ha' : a ≠ 0 := ne_of_gt ha
  have hderiv : ∀ x ∈ Set.Ici R, HasDerivAt F (x ^ 2 * Real.exp (-(a * x))) x := by
    intro x _
    have e1 : HasDerivAt (fun y : ℝ => a * y) a x := by
      have := (hasDerivAt_id x).const_mul a
      simpa using this
    have h1 : HasDerivAt (fun y : ℝ => -((a * y) ^ 2 + 2 * (a * y) + 2))
        (-(2 * a ^ 2 * x + 2 * a)) x := by
      have e2 : HasDerivAt (fun y : ℝ => (a * y) ^ 2) (2 * (a * x) * a) x := by
        simpa using e1.pow 2
      have e3 : HasDerivAt (fun y : ℝ => 2 * (a * y)) (2 * a) x := by
        have := e1.const_mul 2
        simpa using this
      have e4 : HasDerivAt (fun y : ℝ => (a * y) ^ 2 + 2 * (a * y) + 2)
          (2 * (a * x) * a + 2 * a) x := by
        have := (e2.add e3).add_const (2 : ℝ)
        simpa using this
      exact e4.neg.congr_deriv (by ring)
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(a * y))) (-a * Real.exp (-(a * x))) x := by
      have hd : HasDerivAt (fun y : ℝ => -(a * y)) (-a) x := by
        have := e1.neg
        simpa using this
      have hc := (Real.hasDerivAt_exp (-(a * x))).comp x hd
      exact hc.congr_deriv (by ring)
    have hprod := (h1.mul h2).div_const (a ^ 3)
    refine hprod.congr_deriv ?_
    field_simp
    ring
  have hnn : ∀ x ∈ Set.Ioi R, 0 ≤ x ^ 2 * Real.exp (-(a * x)) := fun x _ =>
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have htendsto : Tendsto F atTop (𝓝 0) := by
    have key2 : Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
        show -a * x = -(a * x) from by ring]
    have key1 : Tendsto (fun x : ℝ => x * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
      refine h.congr' ?_
      filter_upwards with x
      rw [Real.rpow_one, show -a * x = -(a * x) from by ring]
    have key0 : Tendsto (fun x : ℝ => Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx' : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
      rw [Real.rpow_zero, one_mul, show -a * x = -(a * x) from by ring]
    have heq : F = fun x => (-a ^ 2 / a ^ 3) * (x ^ 2 * Real.exp (-(a * x))) +
        (-2 * a / a ^ 3) * (x * Real.exp (-(a * x))) +
        (-2 / a ^ 3) * Real.exp (-(a * x)) := by
      ext x
      simp only [F]
      field_simp
      ring
    rw [heq]
    have := ((key2.const_mul (-a ^ 2 / a ^ 3)).add
      (key1.const_mul (-2 * a / a ^ 3))).add (key0.const_mul (-2 / a ^ 3))
    simpa using this
  have hint := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnn htendsto
  rw [hint]
  change 0 - F R = _
  simp only [F]
  ring

/-- The tail integral of `x ^ 3 * exp (-(a * x))` on `(R, +∞)`, for `0 < a` and `0 ≤ R`. -/
theorem integral_pow_three_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) {R : ℝ} (hR : 0 ≤ R) :
    ∫ x : ℝ in Set.Ioi R, x ^ 3 * Real.exp (-(a * x)) =
      ((a * R) ^ 3 + 3 * (a * R) ^ 2 + 6 * (a * R) + 6) * Real.exp (-(a * R)) / a ^ 4 := by
  set F : ℝ → ℝ := fun x =>
    -((a * x) ^ 3 + 3 * (a * x) ^ 2 + 6 * (a * x) + 6) * Real.exp (-(a * x)) / a ^ 4 with hF
  have ha' : a ≠ 0 := ne_of_gt ha
  have hderiv : ∀ x ∈ Set.Ici R, HasDerivAt F (x ^ 3 * Real.exp (-(a * x))) x := by
    intro x _
    have e1 : HasDerivAt (fun y : ℝ => a * y) a x := by
      have := (hasDerivAt_id x).const_mul a
      simpa using this
    have h1 : HasDerivAt (fun y : ℝ => -((a * y) ^ 3 + 3 * (a * y) ^ 2 + 6 * (a * y) + 6))
        (-(3 * a ^ 3 * x ^ 2 + 6 * a ^ 2 * x + 6 * a)) x := by
      have e2 : HasDerivAt (fun y : ℝ => (a * y) ^ 3) (3 * (a * x) ^ 2 * a) x := by
        simpa using e1.pow 3
      have e3 : HasDerivAt (fun y : ℝ => 3 * (a * y) ^ 2) (3 * (2 * (a * x) * a)) x := by
        have := (e1.pow 2).const_mul 3
        simpa using this
      have e4 : HasDerivAt (fun y : ℝ => 6 * (a * y)) (6 * a) x := by
        have := e1.const_mul 6
        simpa using this
      have e5 : HasDerivAt (fun y : ℝ => (a * y) ^ 3 + 3 * (a * y) ^ 2 + 6 * (a * y) + 6)
          (3 * (a * x) ^ 2 * a + 3 * (2 * (a * x) * a) + 6 * a) x := by
        have := ((e2.add e3).add e4).add_const (6 : ℝ)
        simpa using this
      exact e5.neg.congr_deriv (by ring)
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(a * y))) (-a * Real.exp (-(a * x))) x := by
      have hd : HasDerivAt (fun y : ℝ => -(a * y)) (-a) x := by
        have := e1.neg
        simpa using this
      have hc := (Real.hasDerivAt_exp (-(a * x))).comp x hd
      exact hc.congr_deriv (by ring)
    have hprod := (h1.mul h2).div_const (a ^ 4)
    refine hprod.congr_deriv ?_
    field_simp
    ring
  have hnn : ∀ x ∈ Set.Ioi R, 0 ≤ x ^ 3 * Real.exp (-(a * x)) := fun x hx => by
    have hxR : 0 ≤ x := le_of_lt (lt_of_le_of_lt hR hx)
    exact mul_nonneg (by positivity) (Real.exp_pos _).le
  have htendsto : Tendsto F atTop (𝓝 0) := by
    have key3 : Tendsto (fun x : ℝ => x ^ 3 * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
        show -a * x = -(a * x) from by ring]
    have key2 : Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
        show -a * x = -(a * x) from by ring]
    have key1 : Tendsto (fun x : ℝ => x * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
      refine h.congr' ?_
      filter_upwards with x
      rw [Real.rpow_one, show -a * x = -(a * x) from by ring]
    have key0 : Tendsto (fun x : ℝ => Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx' : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
      rw [Real.rpow_zero, one_mul, show -a * x = -(a * x) from by ring]
    have heq : F = fun x => (-a ^ 3 / a ^ 4) * (x ^ 3 * Real.exp (-(a * x))) +
        (-3 * a ^ 2 / a ^ 4) * (x ^ 2 * Real.exp (-(a * x))) +
        (-6 * a / a ^ 4) * (x * Real.exp (-(a * x))) +
        (-6 / a ^ 4) * Real.exp (-(a * x)) := by
      ext x
      simp only [F]
      field_simp
      ring
    rw [heq]
    have := (((key3.const_mul (-a ^ 3 / a ^ 4)).add
      (key2.const_mul (-3 * a ^ 2 / a ^ 4))).add
      (key1.const_mul (-6 * a / a ^ 4))).add (key0.const_mul (-6 / a ^ 4))
    simpa using this
  have hint := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnn htendsto
  rw [hint]
  change 0 - F R = _
  simp only [F]
  ring

/-- The tail integral of `x ^ 4 * exp (-(a * x))` on `(R, +∞)`, for `0 < a`. -/
theorem integral_pow_four_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) (R : ℝ) :
    ∫ x : ℝ in Set.Ioi R, x ^ 4 * Real.exp (-(a * x)) =
      ((a * R) ^ 4 + 4 * (a * R) ^ 3 + 12 * (a * R) ^ 2 + 24 * (a * R) + 24) *
        Real.exp (-(a * R)) / a ^ 5 := by
  set F : ℝ → ℝ := fun x =>
    -((a * x) ^ 4 + 4 * (a * x) ^ 3 + 12 * (a * x) ^ 2 + 24 * (a * x) + 24) *
      Real.exp (-(a * x)) / a ^ 5 with hF
  have ha' : a ≠ 0 := ne_of_gt ha
  have hderiv : ∀ x ∈ Set.Ici R, HasDerivAt F (x ^ 4 * Real.exp (-(a * x))) x := by
    intro x _
    have e1 : HasDerivAt (fun y : ℝ => a * y) a x := by
      have := (hasDerivAt_id x).const_mul a
      simpa using this
    have h1 : HasDerivAt
        (fun y : ℝ => -((a * y) ^ 4 + 4 * (a * y) ^ 3 + 12 * (a * y) ^ 2 + 24 * (a * y) + 24))
        (-(4 * a ^ 4 * x ^ 3 + 12 * a ^ 3 * x ^ 2 + 24 * a ^ 2 * x + 24 * a)) x := by
      have e2 : HasDerivAt (fun y : ℝ => (a * y) ^ 4) (4 * (a * x) ^ 3 * a) x := by
        simpa using e1.pow 4
      have e3 : HasDerivAt (fun y : ℝ => 4 * (a * y) ^ 3) (4 * (3 * (a * x) ^ 2 * a)) x := by
        have := (e1.pow 3).const_mul 4
        simpa using this
      have e4 : HasDerivAt (fun y : ℝ => 12 * (a * y) ^ 2) (12 * (2 * (a * x) * a)) x := by
        have := (e1.pow 2).const_mul 12
        simpa using this
      have e5 : HasDerivAt (fun y : ℝ => 24 * (a * y)) (24 * a) x := by
        have := e1.const_mul 24
        simpa using this
      have e6 : HasDerivAt
          (fun y : ℝ => (a * y) ^ 4 + 4 * (a * y) ^ 3 + 12 * (a * y) ^ 2 + 24 * (a * y) + 24)
          (4 * (a * x) ^ 3 * a + 4 * (3 * (a * x) ^ 2 * a) +
            12 * (2 * (a * x) * a) + 24 * a) x := by
        have := (((e2.add e3).add e4).add e5).add_const (24 : ℝ)
        simpa using this
      exact e6.neg.congr_deriv (by ring)
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(a * y))) (-a * Real.exp (-(a * x))) x := by
      have hd : HasDerivAt (fun y : ℝ => -(a * y)) (-a) x := by
        have := e1.neg
        simpa using this
      have hc := (Real.hasDerivAt_exp (-(a * x))).comp x hd
      exact hc.congr_deriv (by ring)
    have hprod := (h1.mul h2).div_const (a ^ 5)
    refine hprod.congr_deriv ?_
    field_simp
    ring
  have hnn : ∀ x ∈ Set.Ioi R, 0 ≤ x ^ 4 * Real.exp (-(a * x)) := fun x _ =>
    mul_nonneg (by positivity) (Real.exp_pos _).le
  have htendsto : Tendsto F atTop (𝓝 0) := by
    have key4 : Tendsto (fun x : ℝ => x ^ 4 * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
        show -a * x = -(a * x) from by ring]
    have key3 : Tendsto (fun x : ℝ => x ^ 3 * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
        show -a * x = -(a * x) from by ring]
    have key2 : Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
        show -a * x = -(a * x) from by ring]
    have key1 : Tendsto (fun x : ℝ => x * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
      refine h.congr' ?_
      filter_upwards with x
      rw [Real.rpow_one, show -a * x = -(a * x) from by ring]
    have key0 : Tendsto (fun x : ℝ => Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx' : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
      rw [Real.rpow_zero, one_mul, show -a * x = -(a * x) from by ring]
    have heq : F = fun x => (-a ^ 4 / a ^ 5) * (x ^ 4 * Real.exp (-(a * x))) +
        (-4 * a ^ 3 / a ^ 5) * (x ^ 3 * Real.exp (-(a * x))) +
        (-12 * a ^ 2 / a ^ 5) * (x ^ 2 * Real.exp (-(a * x))) +
        (-24 * a / a ^ 5) * (x * Real.exp (-(a * x))) +
        (-24 / a ^ 5) * Real.exp (-(a * x)) := by
      ext x
      simp only [F]
      field_simp
      ring
    rw [heq]
    have := ((((key4.const_mul (-a ^ 4 / a ^ 5)).add
      (key3.const_mul (-4 * a ^ 3 / a ^ 5))).add
      (key2.const_mul (-12 * a ^ 2 / a ^ 5))).add
      (key1.const_mul (-24 * a / a ^ 5))).add (key0.const_mul (-24 / a ^ 5))
    simpa using this
  have hint := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnn htendsto
  rw [hint]
  change 0 - F R = _
  simp only [F]
  ring

/-- The tail integral of `x ^ 5 * exp (-(a * x))` on `(R, +∞)`, for `0 < a` and `0 ≤ R`. -/
theorem integral_pow_five_mul_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) {R : ℝ} (hR : 0 ≤ R) :
    ∫ x : ℝ in Set.Ioi R, x ^ 5 * Real.exp (-(a * x)) =
      ((a * R) ^ 5 + 5 * (a * R) ^ 4 + 20 * (a * R) ^ 3 + 60 * (a * R) ^ 2 +
        120 * (a * R) + 120) * Real.exp (-(a * R)) / a ^ 6 := by
  set F : ℝ → ℝ := fun x =>
    -((a * x) ^ 5 + 5 * (a * x) ^ 4 + 20 * (a * x) ^ 3 + 60 * (a * x) ^ 2 +
      120 * (a * x) + 120) * Real.exp (-(a * x)) / a ^ 6 with hF
  have ha' : a ≠ 0 := ne_of_gt ha
  have hderiv : ∀ x ∈ Set.Ici R, HasDerivAt F (x ^ 5 * Real.exp (-(a * x))) x := by
    intro x _
    have e1 : HasDerivAt (fun y : ℝ => a * y) a x := by
      have := (hasDerivAt_id x).const_mul a
      simpa using this
    have h1 : HasDerivAt
        (fun y : ℝ => -((a * y) ^ 5 + 5 * (a * y) ^ 4 + 20 * (a * y) ^ 3 + 60 * (a * y) ^ 2 +
          120 * (a * y) + 120))
        (-(5 * a ^ 5 * x ^ 4 + 20 * a ^ 4 * x ^ 3 + 60 * a ^ 3 * x ^ 2 +
          120 * a ^ 2 * x + 120 * a)) x := by
      have e2 : HasDerivAt (fun y : ℝ => (a * y) ^ 5) (5 * (a * x) ^ 4 * a) x := by
        simpa using e1.pow 5
      have e3 : HasDerivAt (fun y : ℝ => 5 * (a * y) ^ 4) (5 * (4 * (a * x) ^ 3 * a)) x := by
        have := (e1.pow 4).const_mul 5
        simpa using this
      have e4 : HasDerivAt (fun y : ℝ => 20 * (a * y) ^ 3) (20 * (3 * (a * x) ^ 2 * a)) x := by
        have := (e1.pow 3).const_mul 20
        simpa using this
      have e5 : HasDerivAt (fun y : ℝ => 60 * (a * y) ^ 2) (60 * (2 * (a * x) * a)) x := by
        have := (e1.pow 2).const_mul 60
        simpa using this
      have e6 : HasDerivAt (fun y : ℝ => 120 * (a * y)) (120 * a) x := by
        have := e1.const_mul 120
        simpa using this
      have e7 : HasDerivAt
          (fun y : ℝ => (a * y) ^ 5 + 5 * (a * y) ^ 4 + 20 * (a * y) ^ 3 + 60 * (a * y) ^ 2 +
            120 * (a * y) + 120)
          (5 * (a * x) ^ 4 * a + 5 * (4 * (a * x) ^ 3 * a) + 20 * (3 * (a * x) ^ 2 * a) +
            60 * (2 * (a * x) * a) + 120 * a) x := by
        have := ((((e2.add e3).add e4).add e5).add e6).add_const (120 : ℝ)
        simpa using this
      exact e7.neg.congr_deriv (by ring)
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(a * y))) (-a * Real.exp (-(a * x))) x := by
      have hd : HasDerivAt (fun y : ℝ => -(a * y)) (-a) x := by
        have := e1.neg
        simpa using this
      have hc := (Real.hasDerivAt_exp (-(a * x))).comp x hd
      exact hc.congr_deriv (by ring)
    have hprod := (h1.mul h2).div_const (a ^ 6)
    refine hprod.congr_deriv ?_
    field_simp
    ring
  have hnn : ∀ x ∈ Set.Ioi R, 0 ≤ x ^ 5 * Real.exp (-(a * x)) := fun x hx => by
    have hxR : 0 ≤ x := le_of_lt (lt_of_le_of_lt hR hx)
    exact mul_nonneg (by positivity) (Real.exp_pos _).le
  have htendsto : Tendsto F atTop (𝓝 0) := by
    have key5 : Tendsto (fun x : ℝ => x ^ 5 * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 5 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
        show -a * x = -(a * x) from by ring]
    have key4 : Tendsto (fun x : ℝ => x ^ 4 * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 4 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
        show -a * x = -(a * x) from by ring]
    have key3 : Tendsto (fun x : ℝ => x ^ 3 * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
        show -a * x = -(a * x) from by ring]
    have key2 : Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
        show -a * x = -(a * x) from by ring]
    have key1 : Tendsto (fun x : ℝ => x * Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 a ha
      refine h.congr' ?_
      filter_upwards with x
      rw [Real.rpow_one, show -a * x = -(a * x) from by ring]
    have key0 : Tendsto (fun x : ℝ => Real.exp (-(a * x))) atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 a ha
      refine h.congr' ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
      have hx' : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
      rw [Real.rpow_zero, one_mul, show -a * x = -(a * x) from by ring]
    have heq : F = fun x => (-a ^ 5 / a ^ 6) * (x ^ 5 * Real.exp (-(a * x))) +
        (-5 * a ^ 4 / a ^ 6) * (x ^ 4 * Real.exp (-(a * x))) +
        (-20 * a ^ 3 / a ^ 6) * (x ^ 3 * Real.exp (-(a * x))) +
        (-60 * a ^ 2 / a ^ 6) * (x ^ 2 * Real.exp (-(a * x))) +
        (-120 * a / a ^ 6) * (x * Real.exp (-(a * x))) +
        (-120 / a ^ 6) * Real.exp (-(a * x)) := by
      ext x
      simp only [F]
      field_simp
      ring
    rw [heq]
    have := (((((key5.const_mul (-a ^ 5 / a ^ 6)).add
      (key4.const_mul (-5 * a ^ 4 / a ^ 6))).add
      (key3.const_mul (-20 * a ^ 3 / a ^ 6))).add
      (key2.const_mul (-60 * a ^ 2 / a ^ 6))).add
      (key1.const_mul (-120 * a / a ^ 6))).add (key0.const_mul (-120 / a ^ 6))
    simpa using this
  have hint := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hnn htendsto
  rw [hint]
  change 0 - F R = _
  simp only [F]
  ring

/-- If `-m < c`, then `(fun t : ℝ ↦ (t + m) ^ a)` is integrable on `(c, ∞)` for all `a < -1`. -/
theorem integrableOn_add_rpow_Ioi_of_lt {a c m : ℝ} (ha : a < -1) (hc : -m < c) :
    IntegrableOn (fun (x : ℝ) ↦ (x + m) ^ a) (Ioi c) := by
  have hd : ∀ x ∈ Ici c, HasDerivAt (fun t ↦ (t + m) ^ (a + 1) / (a + 1)) ((x + m) ^ a) x := by
    intro x hx
    convert (((hasDerivAt_id _).add_const _).rpow_const _).div_const _ using 1
    · simp [show a + 1 ≠ 0 by linarith]
    left; linarith [mem_Ici.mp hx, id_eq x]
  have ht : Tendsto (fun t ↦ ((t + m) ^ (a + 1)) / (a + 1)) atTop (nhds (0 / (a + 1))) := by
    rw [← neg_neg (a + 1)]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp
      (tendsto_atTop_add_const_right _ m tendsto_id) |>.div_const _
  exact integrableOn_Ioi_deriv_of_nonneg' hd
    (fun t ht ↦ rpow_nonneg (by linarith [mem_Ioi.mp ht]) a) ht

/-- If `0 < c`, then `(fun t : ℝ ↦ t ^ a)` is integrable on `(c, ∞)` for all `a < -1`. -/
theorem integrableOn_Ioi_rpow_of_lt {a c : ℝ} (ha : a < -1) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ ↦ t ^ a) (Ioi c) := by
  simpa using integrableOn_add_rpow_Ioi_of_lt ha (by simpa : -0 < c)

theorem integrableOn_Ioi_rpow_iff {s t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x ↦ x ^ s) (Ioi t) ↔ s < -1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrableOn_Ioi_rpow_of_lt h ht⟩
  contrapose! h
  intro H
  have H' : IntegrableOn (fun x ↦ x ^ s) (Ioi (max 1 t)) :=
    H.mono (Set.Ioi_subset_Ioi (le_max_right _ _)) le_rfl
  have : IntegrableOn (fun x ↦ x⁻¹) (Ioi (max 1 t)) := by
    apply H'.mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have x_one : 1 ≤ x := ((le_max_left _ _).trans_lt (mem_Ioi.1 hx)).le
    simp only [norm_inv, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans x_one)]
    rw [← Real.rpow_neg_one x]
    exact Real.rpow_le_rpow_of_exponent_le x_one h
  exact not_integrableOn_Ioi_inv this

theorem integrableAtFilter_rpow_atTop_iff {s : ℝ} :
    IntegrableAtFilter (fun x : ℝ ↦ x ^ s) atTop ↔ s < -1 := by
  refine ⟨fun ⟨t, ht, hint⟩ ↦ ?_, fun h ↦
    ⟨Set.Ioi 1, Ioi_mem_atTop 1, (integrableOn_Ioi_rpow_iff zero_lt_one).mpr h⟩⟩
  obtain ⟨a, ha⟩ := mem_atTop_sets.mp ht
  refine (integrableOn_Ioi_rpow_iff (zero_lt_one.trans_le (le_max_right a 1))).mp ?_
  exact hint.mono_set <| fun x hx ↦ ha _ <| (le_max_left a 1).trans hx.le

/-- The real power function with any exponent is not integrable on `(0, +∞)`. -/
theorem not_integrableOn_Ioi_rpow (s : ℝ) : ¬ IntegrableOn (fun x ↦ x ^ s) (Ioi (0 : ℝ)) := by
  intro h
  rcases le_or_gt s (-1) with hs | hs
  · have : IntegrableOn (fun x ↦ x ^ s) (Ioo (0 : ℝ) 1) := h.mono Ioo_subset_Ioi_self le_rfl
    rw [integrableOn_Ioo_rpow_iff zero_lt_one] at this
    exact hs.not_gt this
  · have : IntegrableOn (fun x ↦ x ^ s) (Ioi (1 : ℝ)) := h.mono (Ioi_subset_Ioi zero_le_one) le_rfl
    rw [integrableOn_Ioi_rpow_iff zero_lt_one] at this
    exact hs.not_gt this

theorem setIntegral_Ioi_zero_rpow (s : ℝ) : ∫ x in Ioi (0 : ℝ), x ^ s = 0 :=
  MeasureTheory.integral_undef (not_integrableOn_Ioi_rpow s)

theorem integral_Ioi_rpow_of_lt {a : ℝ} (ha : a < -1) {c : ℝ} (hc : 0 < c) :
    ∫ t : ℝ in Ioi c, t ^ a = -c ^ (a + 1) / (a + 1) := by
  have hd : ∀ x ∈ Ici c, HasDerivAt (fun t => t ^ (a + 1) / (a + 1)) (x ^ a) x := by
    intro x hx
    convert (hasDerivAt_rpow_const (p := a + 1) (Or.inl (hc.trans_le hx).ne')).div_const _ using 1
    simp [show a + 1 ≠ 0 from ne_of_lt (by linarith), mul_comm]
  have ht : Tendsto (fun t => t ^ (a + 1) / (a + 1)) atTop (𝓝 (0 / (a + 1))) := by
    apply Tendsto.div_const
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (by linarith : 0 < -(a + 1))
  convert integral_Ioi_of_hasDerivAt_of_tendsto' hd (integrableOn_Ioi_rpow_of_lt ha hc) ht using 1
  simp only [neg_div, zero_div, zero_sub]

theorem integrableOn_Ioi_norm_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ ↦ ‖(t : ℂ) ^ a‖) (Ioi c) := by
  refine (integrableOn_Ioi_rpow_of_lt ha hc).congr_fun (fun x hx => ?_) measurableSet_Ioi
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (hc.trans hx)]

theorem integrableOn_Ioi_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ a) (Ioi c) := by
  refine (integrable_norm_iff ?_).mp <| integrableOn_Ioi_norm_cpow_of_lt ha hc
  refine ContinuousOn.aestronglyMeasurable (fun t ht ↦ ?_) measurableSet_Ioi
  exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (hc.trans ht).ne')).continuousWithinAt

theorem integrableOn_Ioi_norm_cpow_iff {s : ℂ} {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ ↦ ‖(x : ℂ) ^ s‖) (Ioi t) ↔ s.re < -1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ integrableOn_Ioi_norm_cpow_of_lt h ht⟩
  refine (integrableOn_Ioi_rpow_iff ht).mp <| h.congr_fun (fun a ha ↦ ?_) measurableSet_Ioi
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (ht.trans ha)]

theorem integrableOn_Ioi_cpow_iff {s : ℂ} {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioi t) ↔ s.re < -1 :=
  ⟨fun h ↦ (integrableOn_Ioi_norm_cpow_iff ht).mp h.norm, fun h ↦ integrableOn_Ioi_cpow_of_lt h ht⟩

theorem integrableOn_Ioi_deriv_ofReal_cpow {s : ℂ} {t : ℝ} (ht : 0 < t) (hs : s.re < 0) :
    IntegrableOn (deriv fun x : ℝ ↦ (x : ℂ) ^ s) (Set.Ioi t) := by
  have h : IntegrableOn (fun x : ℝ ↦ s * x ^ (s - 1)) (Set.Ioi t) := by
    refine (integrableOn_Ioi_cpow_of_lt ?_ ht).const_mul _
    rwa [Complex.sub_re, Complex.one_re, sub_lt_iff_lt_add, neg_add_cancel]
  refine h.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  rw [Complex.deriv_ofReal_cpow_const (ht.trans hx).ne' (fun h ↦ (Complex.zero_re ▸ h ▸ hs).false)]

theorem integrableOn_Ioi_deriv_norm_ofReal_cpow {s : ℂ} {t : ℝ} (ht : 0 < t) (hs : s.re ≤ 0) :
    IntegrableOn (deriv fun x : ℝ ↦ ‖(x : ℂ) ^ s‖) (Set.Ioi t) := by
  rw [integrableOn_congr_fun (fun x hx ↦ by
    rw [deriv_norm_ofReal_cpow _ (ht.trans hx)]) measurableSet_Ioi]
  obtain hs | hs := eq_or_lt_of_le hs
  · simp_rw [hs, zero_mul]
    exact integrableOn_zero
  · replace hs : s.re - 1 < -1 := by rwa [sub_lt_iff_lt_add, neg_add_cancel]
    exact (integrableOn_Ioi_rpow_of_lt hs ht).const_mul s.re

/-- The complex power function with any exponent is not integrable on `(0, +∞)`. -/
theorem not_integrableOn_Ioi_cpow (s : ℂ) :
    ¬ IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioi (0 : ℝ)) := by
  intro h
  rcases le_or_gt s.re (-1) with hs | hs
  · have : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioo (0 : ℝ) 1) :=
      h.mono Ioo_subset_Ioi_self le_rfl
    rw [integrableOn_Ioo_cpow_iff zero_lt_one] at this
    exact hs.not_gt this
  · have : IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ s) (Ioi 1) :=
      h.mono (Ioi_subset_Ioi zero_le_one) le_rfl
    rw [integrableOn_Ioi_cpow_iff zero_lt_one] at this
    exact hs.not_gt this

theorem setIntegral_Ioi_zero_cpow (s : ℂ) : ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ s = 0 :=
  MeasureTheory.integral_undef (not_integrableOn_Ioi_cpow s)

theorem integral_Ioi_cpow_of_lt {a : ℂ} (ha : a.re < -1) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi c, (t : ℂ) ^ a) = -(c : ℂ) ^ (a + 1) / (a + 1) := by
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Ioi c (integrableOn_Ioi_cpow_of_lt ha hc) tendsto_id) ?_
  suffices
    Tendsto (fun x : ℝ => ((x : ℂ) ^ (a + 1) - (c : ℂ) ^ (a + 1)) / (a + 1)) atTop
      (𝓝 <| -c ^ (a + 1) / (a + 1)) by
    refine this.congr' ((eventually_gt_atTop 0).mp (Eventually.of_forall fun x hx => ?_))
    dsimp only
    rw [integral_cpow, id]
    refine Or.inr ⟨?_, notMem_uIcc_of_lt hc hx⟩
    apply_fun Complex.re
    rw [Complex.neg_re, Complex.one_re]
    exact ha.ne
  simp_rw [← zero_sub, sub_div]
  refine (Tendsto.div_const ?_ _).sub_const _
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine
    (tendsto_rpow_neg_atTop (by linarith : 0 < -(a.re + 1))).congr'
      ((eventually_gt_atTop 0).mp (Eventually.of_forall fun x hx => ?_))
  simp_rw [neg_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.add_re, Complex.one_re]

theorem integrable_inv_one_add_sq : Integrable fun (x : ℝ) ↦ (1 + x ^ 2)⁻¹ := by
  suffices Integrable fun (x : ℝ) ↦ (1 + ‖x‖ ^ 2) ^ ((-2 : ℝ) / 2) by simpa [rpow_neg_one]
  exact integrable_rpow_neg_one_add_norm_sq (by simp)

@[simp]
theorem integral_Iic_inv_one_add_sq {i : ℝ} :
    ∫ (x : ℝ) in Set.Iic i, (1 + x ^ 2)⁻¹ = arctan i + (π / 2) :=
  integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan' x)
    integrable_inv_one_add_sq.integrableOn (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot)
    |>.trans (sub_neg_eq_add _ _)

@[simp]
theorem integral_Ioi_inv_one_add_sq {i : ℝ} :
    ∫ (x : ℝ) in Set.Ioi i, (1 + x ^ 2)⁻¹ = (π / 2) - arctan i :=
  integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_arctan' x)
    integrable_inv_one_add_sq.integrableOn (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop)

@[simp]
theorem integral_univ_inv_one_add_sq : ∫ (x : ℝ), (1 + x ^ 2)⁻¹ = π :=
  (by ring : π = (π / 2) - (-(π / 2))) ▸ integral_of_hasDerivAt_of_tendsto hasDerivAt_arctan'
    integrable_inv_one_add_sq (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atBot)
    (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop)
