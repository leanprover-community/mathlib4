/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Moments
import Mathlib.Probability.Distributions.Gaussian

/-!
# Linearly tilted measures

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open MeasureTheory Real Set Finset

open scoped NNReal ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {X : Ω → ℝ} {t u : ℝ}

/-- Exponentially tilted measure. When `x ↦ exp (t * x)` is integrable, `μ.linTilted t` is the
probability measure with density with respect to `μ` proportional to `exp (t * x)`.
Otherwise it is 0.
-/
noncomputable
def _root_.MeasureTheory.Measure.linTilted (X : Ω → ℝ) (μ : Measure Ω) (t : ℝ) : Measure Ω :=
  μ.tilted (fun ω ↦ t * X ω)

/- API needed:
- zero measure
- zero E
- add measure?
- add E
- smul measure
- smul E, if exists
- order measure
- order E, if exists

- monotone function
- link to mgf / cgf

-/

instance : IsZeroOrProbabilityMeasure (μ.linTilted X t) := by
  rw [Measure.linTilted]; infer_instance

@[simp]
lemma linTilted_zero_measure : (0 : Measure Ω).linTilted X t = 0 := by simp [Measure.linTilted]

set_option linter.docPrime false in
@[simp]
lemma linTilted_zero' : μ.linTilted X (0 : ℝ) = (μ univ)⁻¹ • μ := by simp [Measure.linTilted]

@[simp]
lemma linTilted_zero [IsZeroOrProbabilityMeasure μ] : μ.linTilted X (0 : ℝ) = μ := by
  rw [linTilted_zero']
  cases eq_zero_or_isProbabilityMeasure μ with
  | inl h => simp [h]
  | inr h => simp [h]

set_option linter.docPrime false in
lemma linTilted_apply' {s : Set Ω} (hs : MeasurableSet s) :
    μ.linTilted X t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ := by
  rw [Measure.linTilted, tilted_apply' _ _ hs]
  rfl

lemma linTilted_apply [SFinite μ] (s : Set Ω) :
    μ.linTilted X t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a) / mgf X μ t) ∂μ := by
  rw [Measure.linTilted, tilted_apply _ _]
  rfl

lemma linTilted_apply_cgf [IsProbabilityMeasure μ] (s : Set Ω)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.linTilted X t s = ∫⁻ a in s, ENNReal.ofReal (exp (t * X a - cgf X μ t)) ∂μ := by
  simp_rw [linTilted_apply s, exp_sub]
  rw [exp_cgf]
  exact ht

set_option linter.docPrime false in
lemma linTilted_apply_eq_ofReal_integral' {s : Set Ω} (hs : MeasurableSet s) :
    μ.linTilted X t s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) := by
  rw [Measure.linTilted, tilted_apply_eq_ofReal_integral' _ hs]
  rfl

lemma linTilted_apply_eq_ofReal_integral [SFinite μ] (s : Set Ω) :
    μ.linTilted X t s = ENNReal.ofReal (∫ a in s, exp (t * X a) / mgf X μ t ∂μ) := by
  rw [Measure.linTilted, tilted_apply_eq_ofReal_integral _ s]
  rfl

lemma linTilted_apply_eq_ofReal_integral_cgf [IsProbabilityMeasure μ] (s : Set Ω)
    (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    μ.linTilted X t s = ENNReal.ofReal (∫ a in s, exp (t * X a - cgf X μ t) ∂μ) := by
  simp_rw [linTilted_apply_eq_ofReal_integral s, exp_sub]
  rw [exp_cgf]
  exact ht

lemma isProbabilityMeasure_linTilted [NeZero μ] (hf : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    IsProbabilityMeasure (μ.linTilted X t) :=
  isProbabilityMeasure_tilted hf

instance isZeroOrProbabilityMeasure_linTilted : IsZeroOrProbabilityMeasure (μ.linTilted X t) :=
  isZeroOrProbabilityMeasure_tilted

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a version that does not assume that the set is measurable, but works only for s-finite
measures, see `setIntegral_linTilted`. -/
lemma setIntegral_linTilted' (g : Ω → E) {s : Set Ω} (hs : MeasurableSet s) :
    ∫ x in s, g x ∂(μ.linTilted X t) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂μ := by
  rw [Measure.linTilted, setIntegral_tilted' _ _ hs, mgf]

lemma setIntegral_linTilted [SFinite μ] (g : Ω → E) (s : Set Ω) :
    ∫ x in s, g x ∂(μ.linTilted X t) = ∫ x in s, (exp (t * X x) / mgf X μ t) • (g x) ∂μ := by
  rw [Measure.linTilted, setIntegral_tilted, mgf]

lemma integral_linTilted (g : Ω → E) :
    ∫ ω, g ω ∂(μ.linTilted X t) = ∫ ω, (exp (t * X ω) / mgf X μ t) • (g ω) ∂μ := by
  rw [Measure.linTilted, integral_tilted, mgf]

lemma integral_linTilted_self [IsFiniteMeasure μ]
    (ht : t ∈ interior {x | Integrable (fun ω ↦ rexp (x * X ω)) μ}) :
    (μ.linTilted X t)[X] = deriv (cgf X μ) t := by
  rw [integral_linTilted, deriv_cgf ht, ← integral_div, mgf]
  congr with ω
  rw [smul_eq_mul]
  ring

lemma linTilted_absolutelyContinuous (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : μ.linTilted X t ≪ μ :=
  withDensity_absolutelyContinuous _ _

lemma integrable_linTilted_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Ω → E) :
    Integrable g (μ.linTilted X t) ↔ Integrable (fun ω ↦ exp (t * X ω) • g ω) μ := by
  rw [Measure.linTilted, integrable_tilted_iff]

lemma memℒp_linTilted_nat (n : ℕ) [IsFiniteMeasure μ]
    (ht : t ∈ interior {x | Integrable (fun ω ↦ rexp (x * X ω)) μ}) :
    Memℒp X n (Measure.linTilted X μ t) := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrable_exp ht
  by_cases hn : n = 0
  · simp only [hn, CharP.cast_eq_zero, memℒp_zero_iff_aestronglyMeasurable]
    exact hX.aestronglyMeasurable.mono_ac (linTilted_absolutelyContinuous _ _ _)
  refine ⟨hX.aestronglyMeasurable.mono_ac (linTilted_absolutelyContinuous _ _ _), ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top]
  rotate_left
  · simp [hn]
  · simp
  simp only [ENNReal.toReal_nat, ENNReal.rpow_natCast]
  simp_rw [← ofReal_norm_eq_coe_nnnorm, ← ENNReal.ofReal_pow (norm_nonneg (X _))]
  refine Integrable.lintegral_lt_top ?_
  simp_rw [norm_eq_abs]
  simp_rw [integrable_linTilted_iff, smul_eq_mul, mul_comm]
  exact integrable_pow_abs_mul_exp_of_mem_interior ht n

lemma memℒp_linTilted (p : ℝ≥0) [IsFiniteMeasure μ]
    (ht : t ∈ interior {x | Integrable (fun ω ↦ rexp (x * X ω)) μ}) :
    Memℒp X p (Measure.linTilted X μ t) := by
  have hX : AEMeasurable X μ := aemeasurable_of_mem_interior_integrable_exp ht
  by_cases hp : p = 0
  · simp only [hp, ENNReal.coe_zero, memℒp_zero_iff_aestronglyMeasurable]
    exact hX.aestronglyMeasurable.mono_ac (linTilted_absolutelyContinuous _ _ _)
  refine ⟨hX.aestronglyMeasurable.mono_ac (linTilted_absolutelyContinuous _ _ _), ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top]
  rotate_left
  · simp [hp]
  · simp
  simp only [ENNReal.coe_toReal]
  simp_rw [← ofReal_norm_eq_coe_nnnorm]
  have : ∫⁻ ω, (ENNReal.ofReal ‖X ω‖) ^ (p : ℝ) ∂(μ.linTilted X t)
      = ∫⁻ ω, ENNReal.ofReal (‖X ω‖ ^ (p : ℝ)) ∂(μ.linTilted X t) := by
    refine lintegral_congr fun ω ↦ ?_
    exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (X _)) p.2
  rw [this]
  refine Integrable.lintegral_lt_top ?_
  simp_rw [norm_eq_abs]
  sorry

lemma variance_linTilted [NeZero μ] [IsFiniteMeasure μ]
    (ht : t ∈ interior {x | Integrable (fun ω ↦ rexp (x * X ω)) μ}) :
    variance X (μ.linTilted X t) = iteratedDeriv 2 (cgf X μ) t := by
  have ht_int : Integrable (fun ω ↦ rexp (t * X ω)) μ := by
    suffices t ∈ {x | Integrable (fun ω ↦ rexp (x * X ω)) μ} from this
    exact interior_subset ht
  have := isProbabilityMeasure_linTilted ht_int
  rw [Memℒp.variance_eq]
  swap; · exact memℒp_linTilted_nat 2 ht
  rw [integral_linTilted_self ht, iteratedDeriv_two_cgf ht, integral_linTilted, ← integral_div]
  simp only [Pi.pow_apply, Pi.sub_apply, smul_eq_mul]
  congr with ω
  ring

lemma centralMoment_three_linTilted [NeZero μ] [IsFiniteMeasure μ]
    (ht : t ∈ interior {x | Integrable (fun ω ↦ rexp (x * X ω)) μ}) :
    centralMoment X 3 (μ.linTilted X t) = iteratedDeriv 3 (cgf X μ) t := by
  have ht_int : Integrable (fun ω ↦ rexp (t * X ω)) μ := by
    suffices t ∈ {x | Integrable (fun ω ↦ rexp (x * X ω)) μ} from this
    exact interior_subset ht
  have := isProbabilityMeasure_linTilted ht_int
  rw [centralMoment, iteratedDeriv_three_cgf ht, ← integral_div, integral_linTilted]
  congr with ω
  rw [smul_eq_mul, Pi.pow_apply, Pi.sub_apply, integral_linTilted_self ht]
  ring

end Integral

lemma measure_eq_integral_exp_linTilted [IsFiniteMeasure μ] (ε : ℝ) (t : ℝ)
    (h_int : Integrable (fun ω ↦ exp (t * X ω)) μ)
    {s : Set Ω} (hs : MeasurableSet s) :
    (μ s).toReal
      = exp (-t * ε) * mgf X μ t
      * ∫ ω, s.indicator 1 ω * exp (- t * (X ω - ε)) ∂(μ.linTilted X t) := by
  by_cases hμ : μ = 0
  · simp [hμ]
  calc (μ s).toReal = ∫ ω, s.indicator 1 ω ∂μ := by rw [integral_indicator_one hs]
  _ = ∫ ω, s.indicator 1 ω * exp (- t * ε - t * (X ω - ε) + t * X ω)
          * mgf X μ t / mgf X μ t ∂μ := by
    congr with ω
    have : -t * ε - t * (X ω - ε) + t * X ω = 0 := by ring
    rw [mul_div_assoc, div_self (mgf_pos' hμ h_int).ne', mul_one, this, exp_zero, mul_one]
  _ = exp (-t * ε) * mgf X μ t * ∫ ω, s.indicator 1 ω * exp (- t * (X ω - ε))
        * exp (t * X ω) / mgf X μ t ∂μ := by
      rw [← integral_mul_left]
      congr with ω
      rw [exp_add, sub_eq_add_neg, exp_add, ← neg_mul]
      ring
  _ = exp (-t * ε) * mgf X μ t
      * ∫ ω, s.indicator 1 ω * exp (- t * (X ω - ε)) ∂(μ.linTilted X t) := by
    rw [integral_linTilted]
    congr with ω
    rw [smul_eq_mul]
    ring

lemma measure_ge_eq_integral_exp_linTilted [IsFiniteMeasure μ] (ε : ℝ) (t : ℝ) (hX : Measurable X)
    (h_int : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    (μ {ω | ε ≤ X ω}).toReal
      = exp (-t * ε) * mgf X μ t
      * ∫ ω, {ω | ε ≤ X ω}.indicator 1 ω * exp (- t * (X ω - ε)) ∂(μ.linTilted X t) :=
  measure_eq_integral_exp_linTilted _ _ h_int (hX measurableSet_Ici)

lemma integral_eq_integral_measure_ge [SFinite μ] {f : Ω → ℝ}
    (hf_meas : Measurable f) (hf : 0 ≤ f) (hf_int : Integrable f μ) :
    ∫ ω, f ω ∂μ = ∫ u in Ici 0, (μ {x | u ≤ f x}).toReal := by
  calc ∫ ω, f ω ∂μ
  _ = ∫ ω, (∫ u, (Icc 0 (f ω)).indicator 1 u) ∂μ := by
    congr with ω
    rw [integral_indicator_one]
    swap; · exact measurableSet_Icc
    simp only [volume_Icc, sub_zero]
    rw [ENNReal.toReal_ofReal (hf ω)]
  _ = ∫ ω, (∫ u in Ici 0, if u ≤ f ω then 1 else 0) ∂μ := by
    congr with ω
    have h_eq u : (if u ≤ f ω then (1 : ℝ) else 0) = {u | u ≤ f ω}.indicator 1 u := by
      split_ifs with h <;> simp [h]
    simp_rw [h_eq]
    rw [setIntegral_indicator]
    swap; · exact measurableSet_Iic
    rw [integral_indicator measurableSet_Icc]
    congr
  _ = ∫ u in Ici 0, ∫ ω, if u ≤ f ω then 1 else 0 ∂μ := by
    rw [integral_integral_swap]
    refine (integrable_prod_iff ?_).mpr ?_
    · sorry
    · simp only [Function.uncurry_apply_pair, norm_eq_abs]
      refine ⟨ae_of_all _ fun ω ↦ ?_, ?_⟩
      · sorry
      · have h_eq x : ∫ y in Set.Ici 0, |if y ≤ f x then 1 else 0| = f x := by
          have h_if_eq y : |if y ≤ f x then (1 : ℝ) else 0| = {z | z ≤ f x}.indicator 1 y := by
            split_ifs with h <;> simp [h]
          simp_rw [h_if_eq]
          rw [setIntegral_indicator]
          · simp only [Pi.one_apply, integral_const, MeasurableSet.univ, Measure.restrict_apply,
              Set.univ_inter, smul_eq_mul, mul_one]
            have : Ici (0 : ℝ) ∩ {z | z ≤ f x} = Set.Icc 0 (f x) := by ext; simp
            simp only [this, volume_Icc, sub_zero, ENNReal.toReal_ofReal_eq_iff, ge_iff_le]
            exact hf x
          · exact measurableSet_Iic
        simp_rw [h_eq]
        exact hf_int
  _ = ∫ u in Ici 0, (μ {x | u ≤ f x}).toReal := by
    congr with u
    have h_eq ω : (if u ≤ f ω then (1 : ℝ) else 0) = {ω | u ≤ f ω}.indicator 1 ω := by
      split_ifs with h <;> simp [h]
    simp_rw [h_eq]
    rw [integral_indicator_one]
    exact hf_meas measurableSet_Ici

lemma measure_ge_eq_integral_todo [IsFiniteMeasure μ] (ε : ℝ) (t : ℝ) (hX : Measurable X)
    (h_int : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    (μ {ω | ε ≤ X ω}).toReal
      = exp (-t * ε) * mgf X μ t
      * ∫ u in Ici 0, ((μ.linTilted X t) {ω | X ω - ε ∈ Icc 0 (log u⁻¹ / t)}).toReal := by
  rw [measure_ge_eq_integral_exp_linTilted ε t hX h_int]
  congr
  rw [integral_eq_integral_measure_ge _ (fun ω ↦ ?_)]
  rotate_left
  · sorry
  · sorry
  · simp only [Pi.zero_apply, neg_mul]
    refine mul_nonneg ?_ (exp_nonneg _)
    exact indicator_nonneg (fun _ _ ↦ zero_le_one) _
  refine setIntegral_congr_fun measurableSet_Ici fun u hu ↦ ?_
  congr with x
  simp only [neg_mul, mem_setOf_eq, sub_nonneg, log_inv]
  simp only [Set.mem_Ici] at hu
  sorry

lemma measure_ge_eq_integral_todo' [IsFiniteMeasure μ] (ε : ℝ) (t : ℝ) (hX : Measurable X)
    (h_int : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    (μ {ω | ε ≤ X ω}).toReal
      = exp (-t * ε) * mgf X μ t
      * ∫ u in Ici 0, exp (-u) * ((μ.linTilted X t) {ω | X ω - ε ∈ Icc 0 (u / t)}).toReal := by
  sorry

lemma berry_esseen_1 :
    |(μ {ω | (X ω - μ[X]) / variance X μ ≤ t}).toReal - (gaussianReal 0 1 (Iic t)).toReal|
      ≤ 2⁻¹ * (μ[fun ω ↦ |X ω - μ[X]| ^ 3]) / variance X μ ^ ((3 : ℝ) / 2) := by
  sorry

lemma berry_esseen_centered [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun (fun _ ↦ inferInstance) X μ) (h_meas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (h_mean : μ[X 0] = 0)
    (h_var : variance (X 0) μ = 1) (n : ℕ) :
    |(μ {ω | (∑ i in range n, X i ω) / n ≤ t}).toReal - (gaussianReal 0 1 (Iic t)).toReal|
      ≤ 2⁻¹ * μ[fun ω ↦ |X 0 ω| ^ 3] / sqrt n := by
  sorry

lemma berry_esseen [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun (fun _ ↦ inferInstance) X μ) (h_meas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    |(μ {ω | ((∑ i in range n, X i ω)/n - μ[X 0]) / sqrt (variance (X 0) μ) ≤ t}).toReal
        - (gaussianReal 0 1 (Iic t)).toReal|
      ≤ 2⁻¹ * μ[fun ω ↦ |X 0 ω - μ[X 0]| ^ 3] / (variance (X 0) μ ^ ((3 : ℝ) / 2) * sqrt n) := by
  sorry

lemma berry_esseen_Icc_centered [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun (fun _ ↦ inferInstance) X μ) (h_meas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (h_mean : μ[X 0] = 0)
    (h_var : variance (X 0) μ = 1) (n : ℕ) :
    |(μ {ω | (∑ i in range n, X i ω) / n ∈ Icc u t}).toReal - (gaussianReal 0 1 (Icc u t)).toReal|
      ≤ μ[fun ω ↦ |X 0 ω| ^ 3] / sqrt n := by
  sorry

lemma berry_esseen_Icc [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (h_indep : iIndepFun (fun _ ↦ inferInstance) X μ) (h_meas : ∀ i, Measurable (X i))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) (n : ℕ) :
    |(μ {ω | ((∑ i in range n, X i ω)/n - μ[X 0]) / sqrt (variance (X 0) μ) ∈ Icc u t}).toReal
        - (gaussianReal 0 1 (Icc u t)).toReal|
      ≤ μ[fun ω ↦ |X 0 ω - μ[X 0]| ^ 3] / (variance (X 0) μ ^ ((3 : ℝ) / 2) * sqrt n) := by
  sorry

end ProbabilityTheory
