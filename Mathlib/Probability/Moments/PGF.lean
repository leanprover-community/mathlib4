/-
Copyright (c) 2026 Moe Tabei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moe Tabei
-/
module

public import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Probability.Independence.Integration

/-!
# Probability generating function

For an `ℕ`-valued random variable `X`, the probability generating function is
`pgf X μ t = μ[t ^ X]`, the analogue for discrete variables of the moment-generating
function `mgf`.

## Main definitions

* `ProbabilityTheory.pgf X μ t`: probability generating function of `X` with respect to
  measure `μ`, `μ[t ^ X]`.

## Main results

* `ProbabilityTheory.integrable_pow_pgf`: for `|t| ≤ 1` and a finite measure the defining
  integrand is integrable, so the generating function is defined on `[-1, 1]`.
* `ProbabilityTheory.hasSum_pgf` and `ProbabilityTheory.pgf_eq_tsum`: the usual power-series
  form `pgf X μ t = ∑' n, μ.real (X ⁻¹' {n}) * t ^ n`.
* `ProbabilityTheory.map_eq_map_of_pgf_eq`: the generating function determines the law —
  if two generating functions agree on `[-1, 1]`, the distributions coincide.
* `ProbabilityTheory.IndepFun.pgf_add`: if `X` and `Y` are independent then
  `pgf (X + Y) μ t = pgf X μ t * pgf Y μ t`; `ProbabilityTheory.iIndepFun.pgf_sum` is the
  version for finitely many independent variables.
* `ProbabilityTheory.pgf_exp_eq_mgf`: `pgf X μ (exp s) = mgf (fun ω => (X ω : ℝ)) μ s`.
-/

@[expose] public section

open MeasureTheory Filter Finset Real

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℕ} {μ : Measure Ω} {t s : ℝ}

/-- Probability generating function of an `ℕ`-valued random variable `X`:
`fun t => μ[t ^ X]`. -/
def pgf (X : Ω → ℕ) (μ : Measure Ω) (t : ℝ) : ℝ :=
  μ[fun ω => t ^ X ω]

lemma pgf_def (X : Ω → ℕ) (μ : Measure Ω) (t : ℝ) : pgf X μ t = μ[fun ω => t ^ X ω] := rfl

@[simp]
lemma pgf_zero_measure : pgf X (0 : Measure Ω) t = 0 := by simp [pgf]

/-- The value at `0` of the generating function is the mass of `{X = 0}`. -/
lemma pgf_zero (hX : Measurable X) : pgf X μ 0 = μ.real (X ⁻¹' {0}) := by
  have h_eq : (fun ω => (0 : ℝ) ^ X ω) = (X ⁻¹' {0}).indicator fun _ => (1 : ℝ) := by
    ext ω
    by_cases h : X ω = 0 <;> simp [h]
  rw [pgf, h_eq, integral_indicator_const _ (hX (measurableSet_singleton 0)), smul_eq_mul, mul_one]

@[simp]
lemma pgf_one [IsProbabilityMeasure μ] : pgf X μ 1 = 1 := by simp [pgf]

lemma pgf_const [IsProbabilityMeasure μ] (c : ℕ) : pgf (fun _ => c) μ t = t ^ c := by
  simp [pgf]

@[simp]
lemma pgf_zero_fun [IsProbabilityMeasure μ] : pgf (0 : Ω → ℕ) μ t = 1 := by simp [pgf]

lemma pgf_nonneg (ht : 0 ≤ t) : 0 ≤ pgf X μ t :=
  integral_nonneg fun _ => pow_nonneg ht _

lemma pgf_congr {Y : Ω → ℕ} (h : X =ᵐ[μ] Y) : pgf X μ t = pgf Y μ t :=
  integral_congr_ae <| by filter_upwards [h] with ω hω using by rw [hω]

lemma pgf_id_map (hX : AEMeasurable X μ) : pgf id (μ.map X) = pgf X μ := by
  ext t
  rw [pgf, pgf, integral_map hX Measurable.of_discrete.aestronglyMeasurable]
  rfl

/-- Identically distributed random variables have the same generating function. -/
lemma pgf_congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' → ℕ} (h : IdentDistrib X Y μ μ') :
    pgf X μ = pgf Y μ' := by
  rw [← pgf_id_map h.aemeasurable_fst, ← pgf_id_map h.aemeasurable_snd, h.map_eq]

/-- The generating function evaluated at `exp s` is the moment-generating function of `X`
viewed as a real random variable. -/
lemma pgf_exp_eq_mgf (s : ℝ) : pgf X μ (exp s) = mgf (fun ω => (X ω : ℝ)) μ s := by
  simp only [pgf, mgf, ← Real.exp_nat_mul, mul_comm s]

/-- For `|t| ≤ 1` the integrand defining `pgf` is integrable with respect to any finite
measure: the generating function of an `ℕ`-valued variable is always defined on `[-1, 1]`. -/
lemma integrable_pow_pgf [IsFiniteMeasure μ] (hX : Measurable X) (ht : |t| ≤ 1) :
    Integrable (fun ω => t ^ X ω) μ := by
  refine Integrable.mono' (integrable_const 1)
    (((Measurable.of_discrete (f := fun n : ℕ => t ^ n)).comp hX).aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_one₀ (abs_nonneg t) ht

/-- The generating function is monotone on `[0, 1]`. -/
lemma pgf_mono [IsFiniteMeasure μ] (hX : Measurable X) (ht : 0 ≤ t) (hts : t ≤ s) (hs : s ≤ 1) :
    pgf X μ t ≤ pgf X μ s :=
  integral_mono (integrable_pow_pgf hX (abs_le.2 ⟨by linarith, by linarith⟩))
    (integrable_pow_pgf hX (abs_le.2 ⟨by linarith, hs⟩))
    fun ω => pow_le_pow_left₀ ht hts _

lemma pgf_le_one [IsProbabilityMeasure μ] (hX : Measurable X) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    pgf X μ t ≤ 1 :=
  calc pgf X μ t ≤ pgf X μ 1 := pgf_mono hX ht₀ ht₁ le_rfl
    _ = 1 := pgf_one

/-- Power-series form of the generating function: the point masses of `X` are the
coefficients of the series summing to `pgf X μ t`. -/
lemma hasSum_pgf [IsFiniteMeasure μ] (hX : Measurable X) (ht : |t| ≤ 1) :
    HasSum (fun n => μ.real (X ⁻¹' {n}) * t ^ n) (pgf X μ t) := by
  have h_int : Integrable (fun n : ℕ => t ^ n) (μ.map X) := by
    refine Integrable.mono' (integrable_const 1) Measurable.of_discrete.aestronglyMeasurable ?_
    filter_upwards with n
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg t) ht
  rw [pgf, ← integral_map hX.aemeasurable Measurable.of_discrete.aestronglyMeasurable]
  rw [← Measure.sum_smul_dirac (μ.map X)] at h_int ⊢
  refine (hasSum_integral_measure h_int).congr_fun fun n => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul,
    Measure.real, Measure.map_apply hX (measurableSet_singleton n)]

/-- Power-series form of the generating function:
`pgf X μ t = ∑' n, μ.real (X ⁻¹' {n}) * t ^ n`. -/
lemma pgf_eq_tsum [IsFiniteMeasure μ] (hX : Measurable X) (ht : |t| ≤ 1) :
    pgf X μ t = ∑' n, μ.real (X ⁻¹' {n}) * t ^ n :=
  (hasSum_pgf hX ht).tsum_eq.symm

lemma summable_pgf [IsFiniteMeasure μ] (hX : Measurable X) (ht : |t| ≤ 1) :
    Summable fun n => μ.real (X ⁻¹' {n}) * t ^ n :=
  (hasSum_pgf hX ht).summable

section Uniqueness

open FormalMultilinearSeries

/-- Auxiliary: a real power series with bounded coefficients has radius of convergence at
least `1`, hence represents its sum at `0`. -/
private lemma hasFPowerSeriesAt_ofScalarsSum {c : ℕ → ℝ} {C : ℝ} (hc : ∀ n, |c n| ≤ C) :
    HasFPowerSeriesAt (ofScalarsSum c) (ofScalars ℝ c) 0 := by
  have h_rad : (1 : ℝ≥0∞) ≤ (ofScalars ℝ c).radius := by
    simpa using (ofScalars ℝ c).le_radius_of_bound C (r := 1) fun n => by
      rw [ofScalars_norm]
      simpa [Real.norm_eq_abs] using hc n
  exact ((ofScalars ℝ c).hasFPowerSeriesOnBall
    (lt_of_lt_of_le zero_lt_one h_rad)).hasFPowerSeriesAt

/-- **The probability generating function determines the law.** If the generating functions
of two `ℕ`-valued random variables with respect to finite measures agree on `[-1, 1]`, then
the two distributions agree. -/
theorem map_eq_map_of_pgf_eq {Ω' : Type*} {m' : MeasurableSpace Ω'} {ν : Measure Ω'}
    {Y : Ω' → ℕ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ t : ℝ, |t| ≤ 1 → pgf X μ t = pgf Y ν t) :
    μ.map X = ν.map Y := by
  have hpa : HasFPowerSeriesAt (ofScalarsSum fun n => μ.real (X ⁻¹' {n}))
      (ofScalars ℝ fun n => μ.real (X ⁻¹' {n})) 0 :=
    hasFPowerSeriesAt_ofScalarsSum (C := μ.real Set.univ) fun n => by
      rw [abs_of_nonneg measureReal_nonneg]
      exact measureReal_mono (Set.subset_univ _)
  have hpb : HasFPowerSeriesAt (ofScalarsSum fun n => ν.real (Y ⁻¹' {n}))
      (ofScalars ℝ fun n => ν.real (Y ⁻¹' {n})) 0 :=
    hasFPowerSeriesAt_ofScalarsSum (C := ν.real Set.univ) fun n => by
      rw [abs_of_nonneg measureReal_nonneg]
      exact measureReal_mono (Set.subset_univ _)
  have h_eq : (ofScalarsSum fun n => μ.real (X ⁻¹' {n}))
      =ᶠ[nhds (0 : ℝ)] ofScalarsSum fun n => ν.real (Y ⁻¹' {n}) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) zero_lt_one] with t ht
    rw [mem_ball_zero_iff, Real.norm_eq_abs] at ht
    rw [ofScalars_sum_eq, ofScalars_sum_eq]
    simp_rw [smul_eq_mul]
    rw [← pgf_eq_tsum hX ht.le, ← pgf_eq_tsum hY ht.le]
    exact h t ht.le
  have h_coeff := ofScalars_series_injective ℝ ℝ
    (hpa.eq_formalMultilinearSeries_of_eventually hpb h_eq)
  refine Measure.ext_of_singleton fun n => ?_
  rw [Measure.map_apply hX (measurableSet_singleton n),
    Measure.map_apply hY (measurableSet_singleton n)]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _)).mp
    (congrFun h_coeff n)

end Uniqueness

section IndepFun

/-- This is a trivial application of `IndepFun.comp` but it will come up frequently: if `X`
and `Y` are independent, so are `t ^ X` and `s ^ Y`. -/
theorem IndepFun.pow_nat {Y : Ω → ℕ} (h_indep : X ⟂ᵢ[μ] Y) (t s : ℝ) :
    (fun ω => t ^ X ω) ⟂ᵢ[μ] fun ω => s ^ Y ω :=
  h_indep.comp (Measurable.of_discrete (f := fun n : ℕ => t ^ n))
    (Measurable.of_discrete (f := fun n : ℕ => s ^ n))

/-- The generating function of a sum of independent variables is the product of the
generating functions. -/
theorem IndepFun.pgf_add {Y : Ω → ℕ} (h_indep : X ⟂ᵢ[μ] Y)
    (hX : Measurable X) (hY : Measurable Y) :
    pgf (X + Y) μ t = pgf X μ t * pgf Y μ t := by
  simp_rw [pgf, Pi.add_apply, pow_add]
  exact (h_indep.pow_nat t t).integral_mul_eq_mul_integral
    (((Measurable.of_discrete (f := fun n : ℕ => t ^ n)).comp hX).aestronglyMeasurable)
    (((Measurable.of_discrete (f := fun n : ℕ => t ^ n)).comp hY).aestronglyMeasurable)

/-- The generating function of a sum of finitely many independent variables is the product of
the generating functions. -/
theorem iIndepFun.pgf_sum {ι : Type*} {X : ι → Ω → ℕ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (s : Finset ι) : pgf (∑ i ∈ s, X i) μ t = ∏ i ∈ s, pgf (X i) μ t := by
  have : IsProbabilityMeasure μ := h_indep.isProbabilityMeasure
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi_notin_s h_rec =>
    rw [sum_insert hi_notin_s,
      IndepFun.pgf_add (h_indep.indepFun_finsetSum_of_notMem h_meas hi_notin_s).symm
        (h_meas i) (by fun_prop),
      h_rec, prod_insert hi_notin_s]

end IndepFun

end ProbabilityTheory
