/-
Copyright (c) 2026 Moe Tabei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moe Tabei
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Probability.Moments.Basic

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Independence.Integration

/-!
# Probability generating function

For an `ℕ`-valued random variable `X`, the probability generating function is
`pgf X μ t = μ[t ^ X]`. It is related to the moment-generating function by
`pgf X μ (exp s) = mgf (fun ω ↦ (X ω : ℝ)) μ s` (`ProbabilityTheory.pgf_exp_eq_mgf`).

## Main definitions

* `ProbabilityTheory.pgf X μ t`: probability generating function of `X` with respect to
  measure `μ`, `μ[t ^ X]`.

## Main results

* `ProbabilityTheory.integrable_pow_pgf`: for `|t| ≤ 1` and a finite measure the defining
  integrand is integrable, so the generating function is well-defined on `[-1, 1]`.
* `ProbabilityTheory.pgf_eq_tsum`: the usual power-series form
  `pgf X μ t = ∑' n, μ.real (X ⁻¹' {n}) * t ^ n`.
* `ProbabilityTheory.hasFPowerSeriesOnBall_pgf`: on the open unit ball, `pgf X μ` is given by
  the power series whose coefficients are the point masses of `X`.
* `ProbabilityTheory.map_eq_of_pgf_frequently_eq`: the generating function determines the law —
  if two generating functions agree at points accumulating at `0`, the distributions coincide.
* `ProbabilityTheory.IndepFun.pgf_add`: if `X` and `Y` are independent then
  `pgf (X + Y) μ t = pgf X μ t * pgf Y μ t`; `ProbabilityTheory.iIndepFun.pgf_sum` is the
  version for finitely many independent variables.
* `ProbabilityTheory.pgf_exp_eq_mgf`: `pgf X μ (exp s) = mgf (fun ω ↦ (X ω : ℝ)) μ s`.
-/

@[expose] public section

open MeasureTheory Filter Finset Real

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℕ} {μ : Measure Ω} {t s : ℝ}

/-- Probability generating function of an `ℕ`-valued random variable `X`:
`fun t ↦ μ[t ^ X]`. -/
def pgf (X : Ω → ℕ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  μ[fun ω ↦ t ^ X ω]

lemma pgf_def (X : Ω → ℕ) (μ : Measure Ω) (t : ℝ) : pgf X μ t = μ[fun ω ↦ t ^ X ω] := rfl

@[simp]
lemma pgf_zero_measure : pgf X (0 : Measure Ω) t = 0 := by simp [pgf_def]

@[simp]
lemma pgf_one [IsProbabilityMeasure μ] : pgf X μ 1 = 1 := by simp [pgf_def]

lemma pgf_const [IsProbabilityMeasure μ] (c : ℕ) : pgf (fun _ ↦ c) μ t = t ^ c := by
  simp [pgf_def]

@[simp]
lemma pgf_zero_fun [IsProbabilityMeasure μ] : pgf (0 : Ω → ℕ) μ t = 1 := by simp [pgf_def]

lemma pgf_nonneg (ht : 0 ≤ t) : 0 ≤ pgf X μ t :=
  integral_nonneg fun _ ↦ pow_nonneg ht _

lemma pgf_congr {Y : Ω → ℕ} (h : X =ᵐ[μ] Y) : pgf X μ t = pgf Y μ t :=
  integral_congr_ae (h.fun_comp (t ^ ·))

lemma pgf_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {Y : Ω' → Ω}
    (hY : AEMeasurable Y μ) (hX : AEMeasurable X (μ.map Y)) :
    pgf X (μ.map Y) = pgf (X ∘ Y) μ :=
  funext fun t ↦ integral_map hY (by fun_prop)

lemma pgf_id_map (hX : AEMeasurable X μ) : pgf id (μ.map X) = pgf X μ :=
  pgf_map hX Measurable.of_discrete.aemeasurable

/-- Identically distributed random variables have the same generating function. -/
lemma pgf_congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' → ℕ} (h : IdentDistrib X Y μ μ') :
    pgf X μ = pgf Y μ' := by
  rw [← pgf_id_map h.aemeasurable_fst, ← pgf_id_map h.aemeasurable_snd, h.map_eq]

/-- The value at `0` of the generating function is the mass of `{X = 0}`. -/
lemma pgf_zero (hX : AEMeasurable X μ) : pgf X μ 0 = μ.real (X ⁻¹' {0}) := by
  have h_eq : (fun n : ℕ ↦ (0 : ℝ) ^ n) = ({0} : Set ℕ).indicator fun _ ↦ (1 : ℝ) := by
    ext n
    by_cases h : n = 0 <;> simp [h]
  rw [← pgf_id_map hX, pgf_def]
  simp only [id_eq]
  rw [h_eq, integral_indicator_const _ (measurableSet_singleton 0),
    smul_eq_mul, mul_one, Measure.real, Measure.real,
    Measure.map_apply_of_aemeasurable hX (measurableSet_singleton 0)]

/-- The generating function evaluated at `exp s` is the moment-generating function of `X`
viewed as a real random variable. -/
lemma pgf_exp_eq_mgf (s : ℝ) : pgf X μ (exp s) = mgf (fun ω ↦ (X ω : ℝ)) μ s := by
  simp [pgf_def, mgf, ← Real.exp_natCast_mul, mul_comm s]

/-- For `|t| ≤ 1` the integrand defining `pgf` is integrable with respect to any finite
measure: the generating function of an `ℕ`-valued variable is well-defined on `[-1, 1]`. -/
lemma integrable_pow_pgf [IsFiniteMeasure μ] (hX : AEMeasurable X μ) (ht : |t| ≤ 1) :
    Integrable (fun ω ↦ t ^ X ω) μ := by
  apply Integrable.mono' (integrable_const 1) (by fun_prop)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_one₀ (abs_nonneg t) ht

lemma pgf_mono_of_integrable (ht : 0 ≤ t) (hts : t ≤ s)
    (hs : Integrable (fun ω ↦ s ^ X ω) μ) : pgf X μ t ≤ pgf X μ s := by
  refine integral_mono_of_nonneg ?_ hs ?_
  · filter_upwards with ω using pow_nonneg ht _
  · filter_upwards with ω using pow_le_pow_left₀ ht hts _

/-- The generating function is monotone on `[0, 1]`. -/
lemma pgf_mono [IsFiniteMeasure μ] (hX : AEMeasurable X μ)
    (ht : 0 ≤ t) (hts : t ≤ s) (hs : s ≤ 1) : pgf X μ t ≤ pgf X μ s := by
  apply pgf_mono_of_integrable ht hts
  apply integrable_pow_pgf hX
  rwa [abs_of_nonneg (ht.trans hts)]

lemma abs_pgf_le_one [IsProbabilityMeasure μ] (ht : |t| ≤ 1) :
    |pgf X μ t| ≤ 1 := by
  rw [pgf_def, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := 1) ?_).trans_eq (by simp)
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_one₀ (abs_nonneg t) ht

lemma pgf_le_one [IsProbabilityMeasure μ] (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    pgf X μ t ≤ 1 :=
  (le_abs_self _).trans (abs_pgf_le_one (by rwa [abs_of_nonneg ht₀]))

/-- Power-series form of the generating function: the point masses of `X` are the
coefficients of the series summing to `pgf X μ t`. -/
lemma hasSum_pgf [IsFiniteMeasure μ] (hX : AEMeasurable X μ) (ht : |t| ≤ 1) :
    HasSum (fun n ↦ μ.real (X ⁻¹' {n}) * t ^ n) (pgf X μ t) := by
  have h_int : Integrable (fun n : ℕ ↦ t ^ n) (μ.map X) :=
    integrable_pow_pgf aemeasurable_id ht
  rw [pgf_def, ← integral_map hX Measurable.of_discrete.aestronglyMeasurable]
  rw [← Measure.sum_smul_dirac (μ.map X)] at h_int ⊢
  refine (hasSum_integral_measure h_int).congr_fun fun n ↦ ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul,
    Measure.real, Measure.map_apply_of_aemeasurable hX (measurableSet_singleton n)]

/-- Power-series form of the generating function:
`pgf X μ t = ∑' n, μ.real (X ⁻¹' {n}) * t ^ n`. Both sides are `0` when the series does not
converge. -/
lemma pgf_eq_tsum [IsFiniteMeasure μ] (hX : AEMeasurable X μ) :
    pgf X μ t = ∑' n, μ.real (X ⁻¹' {n}) * t ^ n := by
  rw [pgf_def, ← integral_map hX Measurable.of_discrete.aestronglyMeasurable]
  rw [← Measure.sum_smul_dirac (μ.map X), integral_sum_dirac (fun _ ↦ measure_ne_top _ _)]
  simp [Measure.real, Measure.map_apply_of_aemeasurable hX]

lemma summable_pgf [IsFiniteMeasure μ] (hX : AEMeasurable X μ) (ht : |t| ≤ 1) :
    Summable fun n ↦ μ.real (X ⁻¹' {n}) * t ^ n :=
  (hasSum_pgf hX ht).summable

section Uniqueness

open FormalMultilinearSeries

/-- On the open unit ball, the generating function is the sum of the power series whose
coefficients are the point masses of `X`. -/
lemma hasFPowerSeriesOnBall_pgf [IsFiniteMeasure μ] (hX : AEMeasurable X μ) :
    HasFPowerSeriesOnBall (pgf X μ) (ofScalars ℝ fun n ↦ μ.real (X ⁻¹' {n})) 0 1 where
  r_le := by
    apply (ofScalars ℝ fun n ↦ μ.real (X ⁻¹' {n})).le_radius_of_summable
    simpa [ofScalars_norm] using (summable_pgf hX (t := 1) (by simp)).norm
  r_pos := zero_lt_one
  hasSum {y} hy := by
    have hy : |y| < 1 := by
      rwa [Metric.mem_eball, edist_zero_right, Real.eNorm_eq_ofReal_abs,
        ENNReal.ofReal_lt_one] at hy
    simp only [ofScalars_apply_eq, smul_eq_mul, zero_add]
    exact hasSum_pgf hX hy.le

/-- **The probability generating function determines the law.** If the generating functions
of two `ℕ`-valued random variables with respect to finite measures agree at points accumulating
at `0`, then the two distributions agree. -/
theorem map_eq_of_pgf_frequently_eq {Ω' : Type*} {m' : MeasurableSpace Ω'} {ν : Measure Ω'}
    {Y : Ω' → ℕ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    (h : ∃ᶠ t in 𝓝[≠] (0 : ℝ), pgf X μ t = pgf Y ν t) :
    μ.map X = ν.map Y := by
  have hpa := (hasFPowerSeriesOnBall_pgf hX).hasFPowerSeriesAt
  have hpb := (hasFPowerSeriesOnBall_pgf hY).hasFPowerSeriesAt
  have h_eq : pgf X μ =ᶠ[𝓝 0] pgf Y ν :=
    (AnalyticAt.frequently_eq_iff_eventually_eq hpa.analyticAt hpb.analyticAt).mp h
  have h_coeff := ofScalars_series_injective ℝ ℝ
    (hpa.eq_formalMultilinearSeries_of_eventually hpb h_eq)
  refine Measure.ext_of_singleton fun n ↦ ?_
  rw [Measure.map_apply_of_aemeasurable hX (measurableSet_singleton n),
    Measure.map_apply_of_aemeasurable hY (measurableSet_singleton n)]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp
    (congrFun h_coeff n)

/-- **The probability generating function determines the law.** If the generating functions
of two `ℕ`-valued random variables with respect to finite measures agree on `(0, c)` for some
`c > 0`, then the two distributions agree. -/
theorem map_eq_of_pgf_eq {Ω' : Type*} {m' : MeasurableSpace Ω'} {ν : Measure Ω'}
    {Y : Ω' → ℕ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν) {c : ℝ} (hc : 0 < c)
    (h : ∀ t : ℝ, 0 < t → t < c → pgf X μ t = pgf Y ν t) :
    μ.map X = ν.map Y := by
  apply map_eq_of_pgf_frequently_eq hX hY
  refine (Eventually.frequently ?_).filter_mono (nhdsGT_le_nhdsNE 0)
  filter_upwards [Ioo_mem_nhdsGT hc] with t ⟨ht₀, htc⟩ using h t ht₀ htc

end Uniqueness

section IndepFun

/-- This is a trivial application of `IndepFun.comp` but it will come up frequently: if `X`
and `Y` are independent, so are `t ^ X` and `s ^ Y`. -/
theorem IndepFun.pow_nat {Y : Ω → ℕ} (h_indep : X ⟂ᵢ[μ] Y) (t s : ℝ) :
    (fun ω ↦ t ^ X ω) ⟂ᵢ[μ] fun ω ↦ s ^ Y ω :=
  h_indep.comp Measurable.of_discrete Measurable.of_discrete

/-- The generating function of a sum of independent variables is the product of the
generating functions. -/
theorem IndepFun.pgf_add {Y : Ω → ℕ} (h_indep : X ⟂ᵢ[μ] Y)
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    pgf (X + Y) μ t = pgf X μ t * pgf Y μ t := by
  simp_rw [pgf_def, Pi.add_apply, pow_add]
  exact h_indep.integral_fun_comp_mul_comp hX hY (by fun_prop) (by fun_prop)

/-- The generating function of a sum of finitely many independent variables is the product of
the generating functions. -/
theorem iIndepFun.pgf_sum {ι : Type*} {X : ι → Ω → ℕ}
    (h_indep : iIndepFun X μ) {s : Finset ι} (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ) :
    pgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, pgf (X i) μ t := by
  simp_rw [pgf_def, Finset.sum_apply, ← prod_pow_eq_pow_sum, ← prod_coe_sort s]
  exact (h_indep.restrict s).integral_fun_prod_comp (fun i ↦ h_meas i i.prop) (by fun_prop)

end IndepFun

end ProbabilityTheory
