/-
Copyright (c) 2023 Claus Clausen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claus Clausen
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Probability.Notation
import Mathlib.Probability.Cdf

/-! # Exponential distributions over ℝ

Define the Exponential Measure over the Reals

## Main definitions
* `exponentialPdfReal`: the function `r x ↦ r * (Real.exp (-(r * ↑x))` for `0 ≤ x`
  or `0` else, which is the probability density function of a exponential distribution with
  rate `r` (when `hr : 0 < r`).
* `exponentialPdf`: `ℝ≥0∞`-valued pdf,
  `exponentialPdf r = ENNReal.ofReal (exponentialPdfReal r)`.
* `expMeasure`: an exponential measure on `ℝ`, parametrized by its rate `r`.
* `exponentialCdfReal` : the Cdf given by the Definition of CDF in `ProbabilityTheory.Cdf` on

## Main results
* `ExpCdf_eq`: Proof that the `exponentialCdfReal` given by the Definition equals the known
  function given as `r x ↦ 1 - (Real.exp (-(r * ↑x))` for `0 ≤ x` or `0` else.
-/

open scoped ENNReal NNReal Real

open MeasureTheory Real Set Filter Topology

@[simp]
lemma comp_of_ge : {x : ℝ | x ≥ 0}ᶜ =  {x | x < 0} := by
  ext x;
  constructor <;>
  simp only [ge_iff_le, mem_compl_iff, mem_setOf_eq, not_le, imp_self]

  /-- A Lebesgue Integral from -∞ to y can be expressed
    as the sum of one from -∞ to 0 and 0 to x-/
lemma lintegral_split_bounded {y z : ℝ}(f: ℝ → ENNReal) (ygez: z ≤ y) : ∫⁻ (x : ℝ) in Iic y, f x =
    (∫⁻ (x : ℝ) in Iio z, f x) +  ∫⁻ (x : ℝ) in Icc z y, f x := by
  have union : Iic y = Iio z ∪ Icc z y := by
    exact (Iio_union_Icc_eq_Iic ygez).symm
  rw[union]
  apply lintegral_union measurableSet_Icc
  rw [Set.disjoint_iff]
  rintro x ⟨h1, h2⟩
  simp only [mem_Iio, mem_Icc] at h1 h2
  linarith

lemma lintegral_split (f: ℝ → ENNReal) (c : ℝ) :  ∫⁻ (x : ℝ), f x  =
    (∫⁻ (x : ℝ) in {x | x ≥ c}, f x) +  ∫⁻ (x : ℝ) in {x | x < c}, f x := by
  have union : univ = {x: ℝ | x ≥ c} ∪ {x : ℝ | x < c} := by
    ext x
    simp [le_or_lt]
  have : IsOpen {x : ℝ | x < c} := by exact isOpen_gt' c
  calc
  ∫⁻ (x : ℝ), f x = ∫⁻ (x : ℝ) in univ, f x ∂ volume := (set_lintegral_univ f).symm
  _ = ∫⁻ (x : ℝ) in {x | x ≥ c} ∪ {x | x < c} , f x ∂ volume := by rw [← union]
  _ = _ := by
    apply lintegral_union this.measurableSet
    rw [Set.disjoint_iff]; rintro x ⟨hxge : x ≥ _, hxlt : x < _⟩; linarith

namespace ProbabilityTheory

section ExponentialPdf

/-- Define the PDF of the exponential distribution depending on its rate-/
noncomputable
def exponentialPdfReal (r : ℝ) (x : ℝ) : ℝ :=
if 0 ≤ x then r*exp (-(r*x)) else 0

local notation "E" => exponentialPdfReal

/-- The PDF of the exponential Distribution on the extended real Numbers-/
noncomputable
def exponentialPdf (r : ℝ) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (E r x)

lemma antiDeriv_expDeriv_pos' {r x: ℝ} (hr : 0 < r)  :
    HasDerivAt (fun a ↦ -1/r * (exp (-(r * a)))) (exp (-(r * x))) x := by
  convert (((hasDerivAt_id x).const_mul (-r)).exp.const_mul (-1/r)) using 1 <;> field_simp

/-- the Lebesgue-Integral of the exponential PDF over nonpositive Reals equals 0-/
lemma lintegral_nonpos {x r : ℝ} (hx : x ≤ 0) :
    ∫⁻ (y : ℝ) in Iio x, (exponentialPdf r y) = ENNReal.ofReal 0 := by
  unfold exponentialPdf exponentialPdfReal;
  rw [set_lintegral_congr_fun (g:=(fun _ ↦ 0)) measurableSet_Iio];
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · refine ae_of_all _ ?_; intro a (ha : a < x)
    simp only [ge_iff_le, ENNReal.ofReal_eq_zero]
    rw [if_neg]; linarith


/-- The exponential pdf is measurable. -/
lemma measurable_exponentialPdfReal (r : ℝ) :
    Measurable (E r) := by
  unfold exponentialPdfReal;
  refine Measurable.ite ?hp ((measurable_id'.const_mul r).neg.exp.const_mul r) ?hg;
  · refine MeasurableSet.of_compl ?hp.h;
    apply  IsOpen.measurableSet; rw [comp_of_ge]; exact isOpen_gt' 0
  · exact measurable_const


/-- The exponential Pdf is strongly measurable. Needed to transfer lintegral to integral -/
lemma stronglyMeasurable_exponentialPdfReal (r : ℝ) :
    StronglyMeasurable (E r) :=
  (measurable_exponentialPdfReal r).stronglyMeasurable

/-- the exponential Pdf is positive for all positive reals-/
lemma exponentialPdfReal_pos {x r : ℝ} {hr : 0 < r} (hx : 0 < x) :
    0 < E r x := by
  simp only [exponentialPdfReal, if_pos hx.le]
  positivity

/-- The exponential Pdf is nonnegative-/
lemma exponentialPdfReal_nonneg {r : ℝ} (hr : 0 < r) :
    ∀ x : ℝ, 0 ≤ E r x := by
  unfold exponentialPdfReal
  intro x
  split_ifs <;> positivity

/-- A negative exponential function is integrable on Intervals in R≥0 -/
lemma exp_neg_integrableOn_Ioc {b x : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x ↦ rexp (-(b * x))) (Ioc 0 x) := by
  simp only [neg_mul_eq_neg_mul]
  exact (exp_neg_integrableOn_Ioi _ hb).mono_set Ioc_subset_Ioi_self

lemma if_eval_pos {r : ℝ} : ∀ᵐ  x : ℝ ∂ volume , x < 0 →
    ENNReal.ofReal (if x ≥ 0 then r * rexp (-(r * x)) else 0) = 0 := by
  apply ae_of_all
  intro x hx
  replace hx : ¬ 0 ≤ x := by exact not_le.mpr hx
  simp [hx]

lemma if_eval_neg {r : ℝ} :  ∀ᵐ  x : ℝ ∂ volume , (x ∈ {x|x ≥ 0} →
    ENNReal.ofReal (ite ((x : ℝ) ≥  0) (r * rexp (-(r * x))) 0 ) =
    ENNReal.ofReal (r * rexp (-(r * x)))):= by
  apply ae_of_all
  intro x hx; split_ifs with h; simp only [ge_iff_le] at h
  · rfl
  · contrapose h; simp only [ge_iff_le, not_le, not_lt]; exact hx

lemma antiDerivTendsZero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x ↦ -1/r * (exp (-(r * x)))) atTop (𝓝 0) := by
  rw [← mul_zero (-1/r)]
  apply Tendsto.mul
  exact tendsto_const_nhds
  apply tendsto_exp_neg_atTop_nhds_0.comp
  exact (tendsto_const_mul_atTop_of_pos hr).2 tendsto_id

open Measure

lemma lintegral_exponentialPdfReal_eq_one (r : ℝ) (hr : 0 < r) :
    ∫⁻ (x : ℝ), exponentialPdf r x = 1 := by
  rw [lintegral_split (exponentialPdf r) 0, ←ENNReal.toReal_eq_one_iff];
  have leftSide: ∫⁻ (x : ℝ) in {x | x < 0}, exponentialPdf r x = 0 := by
    unfold exponentialPdf exponentialPdfReal
    rw [set_lintegral_congr_fun (isOpen_gt' 0).measurableSet if_eval_pos, lintegral_zero]
  have rightSide: ∫⁻ (x : ℝ) in {x | x ≥ 0}, exponentialPdf r x
      = ∫⁻ (x : ℝ) in {x | x ≥ 0}, ENNReal.ofReal (r * rexp (-(r * x))) := by
    unfold exponentialPdf exponentialPdfReal
    exact set_lintegral_congr_fun isClosed_Ici.measurableSet if_eval_neg
  rw [leftSide]; simp only [ge_iff_le, add_zero];
  rw [rightSide, ENNReal.toReal_eq_one_iff, ←ENNReal.toReal_eq_one_iff]
  have hf : 0 ≤ᵐ[(restrictₗ {x:ℝ | x ≥ 0}) ℙ] (fun x ↦ r * (rexp (-(r * x)))) := by
    apply ae_of_all
    intro a
    positivity
  rw [← restrictₗ_apply, ← integral_eq_lintegral_of_nonneg_ae hf]
  · simp only [ge_iff_le, restrictₗ_apply];
    have IntegrOn : IntegrableOn (fun x ↦ rexp (-(r * x))) (Ioi 0) := by
      simp only [← neg_mul, exp_neg_integrableOn_Ioi 0 hr]
    rw [integral_mul_left, Ici_def, integral_Ici_eq_integral_Ioi,
        integral_Ioi_of_hasDerivAt_of_tendsto' (fun _ _ ↦ antiDeriv_expDeriv_pos' hr) IntegrOn
        (antiDerivTendsZero hr)]
    field_simp
  · exact ((measurable_id'.const_mul r).neg.exp.const_mul r).stronglyMeasurable.aestronglyMeasurable

/-- The Pdf of the exponential Distribution integrates to 1-/
@[simp]
lemma lintegral_exponentialPdf_eq_one (r : ℝ) (hr : 0 < r) :
    ∫⁻ x, exponentialPdf r x = 1 :=
  lintegral_exponentialPdfReal_eq_one r hr

end ExponentialPdf

local notation "E" => exponentialPdfReal

open MeasureTheory

/-- Measure defined by the exponential Distribution -/
noncomputable
def expMeasure (r : ℝ) : Measure ℝ :=
  volume.withDensity (exponentialPdf r)

instance instIsProbabilityMeasureExponential (r : ℝ) [Fact (0 < r)] :
    IsProbabilityMeasure (expMeasure r) where
  measure_univ := by unfold expMeasure; simp only [MeasurableSet.univ, withDensity_apply,
    Measure.restrict_univ, lintegral_exponentialPdf_eq_one r Fact.out]

/-- CDF of the exponential Distribution -/
noncomputable
def exponentialCdfReal (r : ℝ) : StieltjesFunction :=
    ProbabilityTheory.cdf (expMeasure r)

lemma ExpCdf_eq_integral (r : ℝ) [Fact (0 < r)] : exponentialCdfReal r
    = fun x ↦ ∫ x in Iic x, E r x := by
  ext x;
  --have := instIsProbabilityMeasureExponential r hr
  unfold exponentialCdfReal; rw [ProbabilityTheory.cdf_eq_toReal]
  unfold expMeasure; simp only [measurableSet_Iic, withDensity_apply]
  rw [integral_eq_lintegral_of_nonneg_ae]; exact rfl;
  · apply ae_of_all _ ?a; simp only [Pi.zero_apply]; intro a
    exact exponentialPdfReal_nonneg Fact.out a
  · refine AEStronglyMeasurable.restrict ?hfm.hfm;
    refine Measurable.aestronglyMeasurable ?hfm.hfm.hf;
    exact measurable_exponentialPdfReal r

lemma ExpCdf_eq_lintegral (r : ℝ) [Fact (0 < r)] : exponentialCdfReal r =
    fun x ↦ ENNReal.toReal (∫⁻ x in Iic x, exponentialPdf r x) := by
  ext x;
  unfold exponentialPdf exponentialCdfReal; rw [ProbabilityTheory.cdf_eq_toReal];
  unfold expMeasure; simp only [measurableSet_Iic, withDensity_apply];
  exact rfl

open Topology

lemma antiDeriv_expDeriv_pos {r x : ℝ} :
    HasDerivAt (fun a ↦ -1* (exp (-(r * a)))) (r * exp (-(r * x))) x := by
  convert (((hasDerivAt_id x).const_mul (-r)).exp.const_mul (-1)) using 1;
  · simp only [id_eq, neg_mul];
  simp only [id_eq, neg_mul, mul_one, mul_neg, one_mul, neg_neg, mul_comm]

lemma lint_eq_antiDeriv (r : ℝ) (hr: 0 < r) : ∀ x : ℝ,
    (∫⁻ y in (Iic x),  (exponentialPdf r y) =
    ENNReal.ofReal ( ite (0 ≤ x) (1 - exp (-(r * x))) 0)) := by
  intro x'; split_ifs with h
  case neg =>
    unfold exponentialPdf exponentialPdfReal;
    rw [set_lintegral_congr_fun measurableSet_Iic, lintegral_zero, ENNReal.ofReal_zero];
    refine ae_of_all _ ?_; intro a (ha : a ≤ x')
    rw [if_neg, ENNReal.ofReal_eq_zero]; linarith
  rw [lintegral_split_bounded _ h, lintegral_nonpos (le_refl 0), ENNReal.ofReal_zero, zero_add];
  unfold exponentialPdf exponentialPdfReal;
  rw[set_lintegral_congr_fun measurableSet_Icc (ae_of_all _ ?pos')]
  case pos'; intro a ⟨(hle : _ ≤ a),  _⟩; rw [if_pos hle]
  rw [←ENNReal.toReal_eq_toReal _ ENNReal.ofReal_ne_top, ←integral_eq_lintegral_of_nonneg_ae
      (eventually_of_forall fun _ ↦ le_of_lt (mul_pos hr (exp_pos _)))];
  have : (∫ a in uIoc 0 x', r * rexp (-(r * a))) = (∫ a in (0)..x', r * rexp (-(r * a))) := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul, if_pos h, one_mul]
  rw [integral_Icc_eq_integral_Ioc, ←(uIoc_of_le h), this]
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le h
    (f:= fun a ↦ -1* (rexp (-(r * a)))) _ _]
  rw [ENNReal.toReal_ofReal_eq_iff.2 (by norm_num; positivity)];
  . norm_num; ring
  · simp only [intervalIntegrable_iff, uIoc_of_le h];
    apply Integrable.const_mul (exp_neg_integrableOn_Ioc hr);
  · have : Continuous (fun a ↦ rexp (-(r * a))) := by
      simp only [←neg_mul]; exact (Continuous.exp (continuous_mul_left (-r)))
    exact Continuous.continuousOn (Continuous.comp' (continuous_mul_left (-1)) this)
  · exact (fun _ _ ↦ HasDerivAt.hasDerivWithinAt antiDeriv_expDeriv_pos)
  · apply Integrable.aestronglyMeasurable (Integrable.const_mul _ _);
    rw [←integrableOn_def, integrableOn_Icc_iff_integrableOn_Ioc]; exact exp_neg_integrableOn_Ioc hr
  · refine ne_of_lt (IntegrableOn.set_lintegral_lt_top ?_);
    rw [integrableOn_Icc_iff_integrableOn_Ioc];
    apply Integrable.const_mul (exp_neg_integrableOn_Ioc hr)

/-- The Definition of the CDF equals the known Formular ``1 - exp (-(r * x))``-/
lemma ExpCdf_eq {r : ℝ} [Fact (0 < r)] : exponentialCdfReal r =
    fun x ↦ if 0 ≤ x then 1 - exp (-(r * x)) else 0 := by
  rw[ExpCdf_eq_lintegral]; ext x; rw [lint_eq_antiDeriv _ Fact.out];
  rw[ENNReal.toReal_ofReal_eq_iff]
  split_ifs with h <;> simp [mul_nonneg (le_of_lt (Fact.out)) _]
  exact (mul_nonneg (le_of_lt (Fact.out)) h);
