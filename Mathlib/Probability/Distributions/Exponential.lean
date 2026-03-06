/-
Copyright (c) 2023 Claus Clausen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claus Clausen, Patrick Massot
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # Exponential distributions over ℝ

Define the Exponential measure over the reals.

## Main definitions
* `exponentialPDFReal`: the function `r x ↦ r * exp (-(r * x)` for `0 ≤ x`
  or `0` else, which is the probability density function of an exponential distribution with
  rate `r` (when `hr : 0 < r`).
* `exponentialPDF`: `ℝ≥0∞`-valued pdf,
  `exponentialPDF r = ENNReal.ofReal (exponentialPDFReal r)`.
* `expMeasure`: an exponential measure on `ℝ`, parametrized by its rate `r`.

## Main results
* `cdf_expMeasure_eq`: Proof that the CDF of the exponential measure equals the
  known function given as `r x ↦ 1 - exp (- (r * x))` for `0 ≤ x` or `0` else.
* `integral_id_expMeasure`: the mean of the exponential distribution is `r⁻¹`.
* `variance_id_expMeasure`: the variance of the exponential distribution is `r⁻¹ ^ 2`.
* `mgf_id_expMeasure`: the moment-generating function is `r / (r - t)` for `t < r`.
* `integrable_exp_mul_expMeasure`: integrability of `exp (t * ·)` under `expMeasure r`.
* `memLp_id_expMeasure`: the identity function is in `ℒp` for all `p` under `expMeasure r`.
* `memoryless_expMeasure`: the memoryless property
  `P(X > s + t) / P(X > s) = P(X > t)`.
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section ExponentialPDF

/-- The pdf of the exponential distribution depending on its rate -/
noncomputable
def exponentialPDFReal (r x : ℝ) : ℝ :=
  gammaPDFReal 1 r x

/-- The pdf of the exponential distribution, as a function valued in `ℝ≥0∞` -/
noncomputable
def exponentialPDF (r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (exponentialPDFReal r x)

lemma exponentialPDF_eq (r x : ℝ) :
    exponentialPDF r x = ENNReal.ofReal (if 0 ≤ x then r * exp (-(r * x)) else 0) := by
  rw [exponentialPDF, exponentialPDFReal, gammaPDFReal]
  simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one]

lemma exponentialPDF_of_neg {r x : ℝ} (hx : x < 0) : exponentialPDF r x = 0 := gammaPDF_of_neg hx

lemma exponentialPDF_of_nonneg {r x : ℝ} (hx : 0 ≤ x) :
    exponentialPDF r x = ENNReal.ofReal (r * rexp (-(r * x))) := by
  simp only [exponentialPDF_eq, if_pos hx]

/-- The Lebesgue integral of the exponential pdf over nonpositive reals equals 0 -/
lemma lintegral_exponentialPDF_of_nonpos {x r : ℝ} (hx : x ≤ 0) :
    ∫⁻ y in Iio x, exponentialPDF r y = 0 := lintegral_gammaPDF_of_nonpos hx

/-- The exponential pdf is measurable. -/
@[fun_prop]
lemma measurable_exponentialPDFReal (r : ℝ) : Measurable (exponentialPDFReal r) :=
  measurable_gammaPDFReal 1 r

-- The exponential pdf is strongly measurable -/
@[fun_prop]
lemma stronglyMeasurable_exponentialPDFReal (r : ℝ) :
    StronglyMeasurable (exponentialPDFReal r) := stronglyMeasurable_gammaPDFReal 1 r

/-- The exponential pdf is positive for all positive reals -/
lemma exponentialPDFReal_pos {x r : ℝ} (hr : 0 < r) (hx : 0 < x) :
    0 < exponentialPDFReal r x := gammaPDFReal_pos zero_lt_one hr hx

/-- The exponential pdf is nonnegative -/
lemma exponentialPDFReal_nonneg {r : ℝ} (hr : 0 < r) (x : ℝ) :
    0 ≤ exponentialPDFReal r x := gammaPDFReal_nonneg zero_lt_one hr x

open Measure

/-- The pdf of the exponential distribution integrates to 1 -/
@[simp]
lemma lintegral_exponentialPDF_eq_one {r : ℝ} (hr : 0 < r) : ∫⁻ x, exponentialPDF r x = 1 :=
  lintegral_gammaPDF_eq_one zero_lt_one hr

end ExponentialPDF

open MeasureTheory

/-- Measure defined by the exponential distribution -/
noncomputable
def expMeasure (r : ℝ) : Measure ℝ := gammaMeasure 1 r

lemma isProbabilityMeasure_expMeasure {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_gammaMeasure zero_lt_one hr

@[deprecated (since := "2025-08-29")] alias isProbabilityMeasureExponential :=
  isProbabilityMeasure_expMeasure

section ExponentialCDF

/-- CDF of the exponential distribution -/
@[deprecated "Use `cdf (expMeasure r)` instead." (since := "2025-08-28")]
noncomputable
def exponentialCDFReal (r : ℝ) : StieltjesFunction ℝ :=
  cdf (expMeasure r)

lemma cdf_expMeasure_eq_integral {r : ℝ} (hr : 0 < r) (x : ℝ) :
    cdf (expMeasure r) x = ∫ x in Iic x, exponentialPDFReal r x :=
  cdf_gammaMeasure_eq_integral zero_lt_one hr x

@[deprecated (since := "2025-08-28")] alias exponentialCDFReal_eq_integral :=
  cdf_expMeasure_eq_integral

lemma cdf_expMeasure_eq_lintegral {r : ℝ} (hr : 0 < r) (x : ℝ) :
    cdf (expMeasure r) x = ENNReal.toReal (∫⁻ x in Iic x, exponentialPDF r x) :=
  cdf_gammaMeasure_eq_lintegral zero_lt_one hr x

@[deprecated (since := "2025-08-28")] alias exponentialCDFReal_eq_lintegral :=
  cdf_expMeasure_eq_lintegral

open Topology

lemma hasDerivAt_neg_exp_mul_exp {r x : ℝ} :
    HasDerivAt (fun a ↦ -exp (-(r * a))) (r * exp (-(r * x))) x := by
  convert (((hasDerivAt_id x).const_mul (-r)).exp.const_mul (-1)) using 1
  · simp only [one_mul, id_eq, neg_mul]
  simp only [id_eq, neg_mul, mul_one, mul_neg, one_mul, neg_neg, mul_comm]

/-- A negative exponential function is integrable on intervals in `R≥0` -/
lemma exp_neg_integrableOn_Ioc {b x : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x ↦ rexp (-(b * x))) (Ioc 0 x) := by
  simp only [neg_mul_eq_neg_mul]
  exact (exp_neg_integrableOn_Ioi _ hb).mono_set Ioc_subset_Ioi_self

lemma lintegral_exponentialPDF_eq_antiDeriv {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ∫⁻ y in Iic x, exponentialPDF r y
    = ENNReal.ofReal (if 0 ≤ x then 1 - exp (-(r * x)) else 0) := by
  split_ifs with h
  case neg =>
    simp only [exponentialPDF_eq]
    rw [setLIntegral_congr_fun measurableSet_Iic, lintegral_zero, ENNReal.ofReal_zero]
    exact fun a (_ : a ≤ _) ↦ by rw [if_neg (by linarith), ENNReal.ofReal_eq_zero]
  case pos =>
    rw [lintegral_Iic_eq_lintegral_Iio_add_Icc _ h, lintegral_exponentialPDF_of_nonpos (le_refl 0),
      zero_add]
    simp only [exponentialPDF_eq]
    rw [setLIntegral_congr_fun measurableSet_Icc (g := fun x ↦ ENNReal.ofReal (r * rexp (-(r * x))))
      (by intro a ha; simp [ha.1])]
    rw [← ENNReal.toReal_eq_toReal_iff' _ ENNReal.ofReal_ne_top,
        ← integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ ↦ le_of_lt
        (mul_pos hr (exp_pos _)))]
    · have : ∫ a in uIoc 0 x, r * rexp (-(r * a)) = ∫ a in 0..x, r * rexp (-(r * a)) := by
        rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul, if_pos h, one_mul]
      rw [integral_Icc_eq_integral_Ioc, ← uIoc_of_le h, this]
      rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le h
        (f := fun a ↦ -1 * rexp (-(r * a))) _ _]
      · rw [ENNReal.toReal_ofReal_eq_iff.2
          (sub_nonneg.2 (Real.exp_le_one_iff.2 <| by nlinarith))]
        norm_num; ring
      · simp only [intervalIntegrable_iff, uIoc_of_le h]
        exact Integrable.const_mul (exp_neg_integrableOn_Ioc hr) _
      · have : Continuous (fun a ↦ rexp (-(r * a))) := by
          simp only [← neg_mul]; exact (continuous_const_mul (-r)).rexp
        exact Continuous.continuousOn (Continuous.comp' (continuous_const_mul (-1)) this)
      · simp only [neg_mul, one_mul]
        exact fun _ _ ↦ HasDerivAt.hasDerivWithinAt hasDerivAt_neg_exp_mul_exp
    · refine Integrable.aestronglyMeasurable (Integrable.const_mul ?_ _)
      rw [← IntegrableOn, integrableOn_Icc_iff_integrableOn_Ioc]
      exact exp_neg_integrableOn_Ioc hr
    · refine ne_of_lt (IntegrableOn.setLIntegral_lt_top ?_)
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact Integrable.const_mul (exp_neg_integrableOn_Ioc hr) _

/-- The CDF of the exponential distribution equals ``1 - exp (-(r * x))`` -/
lemma cdf_expMeasure_eq {r : ℝ} (hr : 0 < r) (x : ℝ) :
    cdf (expMeasure r) x = if 0 ≤ x then 1 - exp (-(r * x)) else 0 := by
  rw [cdf_expMeasure_eq_lintegral hr, lintegral_exponentialPDF_eq_antiDeriv hr x,
    ENNReal.toReal_ofReal_eq_iff]
  split_ifs with h
  · simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]
    exact mul_nonneg hr.le h
  · exact le_rfl

@[deprecated (since := "2025-08-28")] alias exponentialCDFReal_eq := cdf_expMeasure_eq

end ExponentialCDF

section ExponentialMGF

variable {r t : ℝ}

/-- Rewrite integrals against `expMeasure r` as Lebesgue integrals weighted by
`exponentialPDF r`. -/
private lemma integral_expMeasure_eq_integral_density (r : ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(expMeasure r) = ∫ x, (exponentialPDF r x).toReal * f x := by
  have h_meas : Measurable (exponentialPDF r) := by
    simpa [exponentialPDF] using (measurable_exponentialPDFReal r).ennreal_ofReal
  simpa [expMeasure, gammaMeasure, exponentialPDF, exponentialPDFReal, smul_eq_mul] using
    integral_withDensity_eq_integral_toReal_smul (μ := volume) (f := exponentialPDF r) (g := f)
      h_meas (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)

/-- The integral of `exp (t * x)` against `expMeasure r` equals `r / (r - t)` when `t < r`. -/
lemma integral_exp_mul_expMeasure (hr : 0 < r) (ht : t < r) :
    ∫ x, exp (t * x) ∂(expMeasure r) = r / (r - t) := by
  rw [integral_expMeasure_eq_integral_density]
  have hIci0 :
      ∫ x, (exponentialPDF r x).toReal * exp (t * x) =
        ∫ x in Ici 0, (exponentialPDF r x).toReal * exp (t * x) := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    simp [exponentialPDF_of_neg (by simpa [mem_Ici] using hx)]
  have hIci :
      ∫ x in Ici 0, (exponentialPDF r x).toReal * exp (t * x) =
        ∫ x in Ici 0, r * exp ((t - r) * x) := by
    refine setIntegral_congr_fun measurableSet_Ici fun x hx => ?_
    rw [exponentialPDF_of_nonneg hx, ENNReal.toReal_ofReal (by positivity),
      mul_assoc, mul_comm _ (exp (t * x)), ← Real.exp_add]
    congr 2; ring
  rw [hIci0, hIci, integral_Ici_eq_integral_Ioi, integral_const_mul]
  have htr : t - r < 0 := by linarith
  rw [integral_exp_mul_Ioi htr 0]
  simp only [mul_zero, exp_zero, neg_div, ← div_neg, neg_sub, mul_one_div]

/-- The function `x ↦ exp (t * x)` is integrable against `expMeasure r` when `t < r`. -/
lemma integrable_exp_mul_expMeasure (hr : 0 < r) (ht : t < r) :
    Integrable (fun x => exp (t * x)) (expMeasure r) := by
  by_contra h
  have h0 := integral_undef h
  linarith [integral_exp_mul_expMeasure hr ht, div_pos hr (sub_pos.mpr ht)]

/-- The moment-generating function of `id` under the exponential distribution with rate `r > 0`
is `r / (r - t)` for `t < r`. -/
lemma mgf_id_expMeasure (hr : 0 < r) (ht : t < r) :
    mgf id (expMeasure r) t = r / (r - t) := by
  simpa [mgf, id_eq] using integral_exp_mul_expMeasure hr ht

/-- The integrable exponential set of `id` under `expMeasure r` contains `Iio r`. -/
lemma Iio_subset_integrableExpSet_id_expMeasure (hr : 0 < r) :
    Iio r ⊆ integrableExpSet id (expMeasure r) := by
  intro t ht
  simp only [integrableExpSet, mem_setOf_eq, id]
  exact integrable_exp_mul_expMeasure hr ht

/-- `0` belongs to the interior of the integrable exponential set of `id` under
`expMeasure r`. -/
lemma zero_mem_interior_integrableExpSet_id_expMeasure (hr : 0 < r) :
    0 ∈ interior (integrableExpSet id (expMeasure r)) :=
  mem_interior.mpr
    ⟨Iio r, Iio_subset_integrableExpSet_id_expMeasure hr, isOpen_Iio, hr⟩

/-- The identity function belongs to `ℒp` for all `p` under `expMeasure r`. -/
lemma memLp_id_expMeasure (hr : 0 < r) (p : ℝ≥0) :
    MemLp id p (expMeasure r) :=
  memLp_of_mem_interior_integrableExpSet
    (zero_mem_interior_integrableExpSet_id_expMeasure hr) p

end ExponentialMGF

section ExponentialMoments

variable {r : ℝ}

/-- The mean of the exponential distribution with rate `r > 0` is `r⁻¹`. -/
@[simp]
lemma integral_id_expMeasure (hr : 0 < r) : ∫ x, x ∂(expMeasure r) = r⁻¹ := by
  rw [integral_expMeasure_eq_integral_density]
  have hIci0 :
      ∫ x, (exponentialPDF r x).toReal * x =
        ∫ x in Ici 0, (exponentialPDF r x).toReal * x := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    simp [exponentialPDF_of_neg (by simpa [mem_Ici] using hx)]
  have hIci :
      ∫ x in Ici 0, (exponentialPDF r x).toReal * x =
        ∫ x in Ici 0, r * (x * exp (-(r * x))) := by
    refine setIntegral_congr_fun measurableSet_Ici fun x hx => ?_
    rw [exponentialPDF_of_nonneg hx, ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [hIci0, hIci, integral_Ici_eq_integral_Ioi, integral_const_mul]
  have hpow :
      ∫ x in Ioi 0, x * exp (-(r * x)) =
        ∫ x in Ioi 0, x ^ (2 - 1 : ℝ) * exp (-(r * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [show (2 - 1 : ℝ) = 1 by norm_num, Real.rpow_one]
  rw [hpow, Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hr]
  norm_num [Real.Gamma_nat_eq_factorial]
  field_simp [hr.ne']

/-- The second raw moment of the exponential distribution with rate `r > 0` is `2 * r⁻¹ ^ 2`. -/
private lemma integral_sq_expMeasure (hr : 0 < r) :
    ∫ x, x ^ 2 ∂(expMeasure r) = 2 * r⁻¹ ^ 2 := by
  rw [integral_expMeasure_eq_integral_density]
  have hIci0 :
      ∫ x, (exponentialPDF r x).toReal * x ^ 2 =
        ∫ x in Ici 0, (exponentialPDF r x).toReal * x ^ 2 := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    simp [exponentialPDF_of_neg (by simpa [mem_Ici] using hx)]
  have hIci :
      ∫ x in Ici 0, (exponentialPDF r x).toReal * x ^ 2 =
        ∫ x in Ici 0, r * (x ^ 2 * exp (-(r * x))) := by
    refine setIntegral_congr_fun measurableSet_Ici fun x hx => ?_
    rw [exponentialPDF_of_nonneg hx, ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [hIci0, hIci, integral_Ici_eq_integral_Ioi, integral_const_mul]
  have hpow :
      ∫ x in Ioi 0, x ^ 2 * exp (-(r * x)) =
        ∫ x in Ioi 0, x ^ (3 - 1 : ℝ) * exp (-(r * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    norm_num
  rw [hpow, Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hr]
  norm_num [Real.Gamma_nat_eq_factorial]
  field_simp [hr.ne']

/-- The variance of `id` under the exponential distribution with rate `r > 0` is `r⁻¹ ^ 2`. -/
@[simp]
lemma variance_id_expMeasure (hr : 0 < r) : Var[id; expMeasure r] = r⁻¹ ^ 2 := by
  let μ : Measure ℝ := expMeasure r
  haveI : IsProbabilityMeasure μ := by simpa [μ] using isProbabilityMeasure_expMeasure hr
  rw [variance_eq_sub (memLp_id_expMeasure hr 2)]
  have hsq : ∫ x, (id ^ 2) x ∂μ = 2 * r⁻¹ ^ 2 := by
    simpa [id, μ] using integral_sq_expMeasure hr
  have hid : ∫ x, id x ∂μ = r⁻¹ := by
    simpa [id, μ] using integral_id_expMeasure hr
  rw [hsq, hid]; ring_nf

/-- The centered second moment `∫ (x - r⁻¹)² d(expMeasure r)` equals `r⁻¹ ^ 2`. -/
lemma variance_integral_expMeasure (hr : 0 < r) :
    ∫ x, (x - r⁻¹) ^ 2 ∂(expMeasure r) = r⁻¹ ^ 2 := by
  calc ∫ x, (x - r⁻¹) ^ 2 ∂(expMeasure r)
      = ∫ x, (x - ∫ y, y ∂(expMeasure r)) ^ 2 ∂(expMeasure r) := by
        simp [integral_id_expMeasure hr]
    _ = Var[id; expMeasure r] := (variance_eq_integral measurable_id'.aemeasurable).symm
    _ = r⁻¹ ^ 2 := variance_id_expMeasure hr

end ExponentialMoments

section ExponentialTail

variable {r : ℝ}

/-- The tail probability `P(X > x)` for the exponential distribution equals `exp (-(r * x))`
when `x ≥ 0`. -/
lemma measure_Ioi_expMeasure (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    (expMeasure r) (Ioi x) = ENNReal.ofReal (exp (-(r * x))) := by
  haveI : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  calc (expMeasure r) (Ioi x)
      = (cdf (expMeasure r)).measure (Ioi x) := by simp [measure_cdf]
    _ = ENNReal.ofReal (1 - cdf (expMeasure r) x) := by
        simpa using StieltjesFunction.measure_Ioi
          (f := cdf (expMeasure r))
          (ProbabilityTheory.tendsto_cdf_atTop (μ := expMeasure r)) x
    _ = ENNReal.ofReal (exp (-(r * x))) := by
        rw [cdf_expMeasure_eq hr x, if_pos hx]; ring_nf

/-- The memoryless property of the exponential distribution: `P(X > s + t | X > s) = P(X > t)`. -/
lemma memoryless_expMeasure (hr : 0 < r) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (expMeasure r) {x | x > s + t} * ((expMeasure r) {x | x > s})⁻¹ =
      (expMeasure r) {x | x > t} := by
  change (expMeasure r) (Ioi (s + t)) * ((expMeasure r) (Ioi s))⁻¹ = (expMeasure r) (Ioi t)
  rw [measure_Ioi_expMeasure hr (add_nonneg hs ht),
    measure_Ioi_expMeasure hr hs,
    measure_Ioi_expMeasure hr ht,
    ← ENNReal.ofReal_inv_of_pos (exp_pos _),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hsne : exp (-(r * s)) ≠ 0 := exp_ne_zero _
  apply mul_right_cancel₀ hsne
  calc (exp (-(r * (s + t))) * (exp (-(r * s)))⁻¹) * exp (-(r * s))
      = exp (-(r * (s + t))) := by field_simp [hsne]
    _ = exp (-(r * t)) * exp (-(r * s)) := by
        rw [← Real.exp_add]; congr 1; ring_nf

end ExponentialTail

end ProbabilityTheory
