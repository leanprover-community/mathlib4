/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Kexing Ying
-/
import Mathlib.Probability.Moments.Covariance

/-!
# Variance of random variables

We define the variance of a real-valued random variable as `Var[X] = 𝔼[(X - 𝔼[X])^2]` (in the
`ProbabilityTheory` locale).

## Main definitions

* `ProbabilityTheory.evariance`: the variance of a real-valued random variable as an extended
  non-negative real.
* `ProbabilityTheory.variance`: the variance of a real-valued random variable as a real number.

## Main results

* `ProbabilityTheory.variance_le_expectation_sq`: the inequality `Var[X] ≤ 𝔼[X^2]`.
* `ProbabilityTheory.meas_ge_le_variance_div_sq`: Chebyshev's inequality, i.e.,
      `ℙ {ω | c ≤ |X ω - 𝔼[X]|} ≤ ENNReal.ofReal (Var[X] / c ^ 2)`.
* `ProbabilityTheory.meas_ge_le_evariance_div_sq`: Chebyshev's inequality formulated with
  `evariance` without requiring the random variables to be L².
* `ProbabilityTheory.IndepFun.variance_add`: the variance of the sum of two independent
  random variables is the sum of the variances.
* `ProbabilityTheory.IndepFun.variance_sum`: the variance of a finite sum of pairwise
  independent random variables is the sum of the variances.
* `ProbabilityTheory.variance_le_sub_mul_sub`: the variance of a random variable `X` satisfying
  `a ≤ X ≤ b` almost everywhere is at most `(b - 𝔼 X) * (𝔼 X - a)`.
* `ProbabilityTheory.variance_le_sq_of_bounded`: the variance of a random variable `X` satisfying
  `a ≤ X ≤ b` almost everywhere is at most`((b - a) / 2) ^ 2`.
-/

open MeasureTheory Filter Finset

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure Ω}

variable (X μ) in
-- Porting note: Consider if `evariance` or `eVariance` is better. Also,
-- consider `eVariationOn` in `Mathlib.Analysis.BoundedVariation`.
/-- The `ℝ≥0∞`-valued variance of a real-valued random variable defined as the Lebesgue integral of
`‖X - 𝔼[X]‖^2`. -/
def evariance : ℝ≥0∞ := ∫⁻ ω, ‖X ω - μ[X]‖ₑ ^ 2 ∂μ

variable (X μ) in
/-- The `ℝ`-valued variance of a real-valued random variable defined by applying `ENNReal.toReal`
to `evariance`. -/
def variance : ℝ := (evariance X μ).toReal

/-- The `ℝ≥0∞`-valued variance of the real-valued random variable `X` according to the measure `μ`.

This is defined as the Lebesgue integral of `(X - 𝔼[X])^2`. -/
scoped notation "eVar[" X "; " μ "]" => ProbabilityTheory.evariance X μ

/-- The `ℝ≥0∞`-valued variance of the real-valued random variable `X` according to the volume
measure.

This is defined as the Lebesgue integral of `(X - 𝔼[X])^2`. -/
scoped notation "eVar[" X "]" => eVar[X; MeasureTheory.MeasureSpace.volume]

/-- The `ℝ`-valued variance of the real-valued random variable `X` according to the measure `μ`.

It is set to `0` if `X` has infinite variance. -/
scoped notation "Var[" X "; " μ "]" => ProbabilityTheory.variance X μ

/-- The `ℝ`-valued variance of the real-valued random variable `X` according to the volume measure.

It is set to `0` if `X` has infinite variance. -/
scoped notation "Var[" X "]" => Var[X; MeasureTheory.MeasureSpace.volume]

theorem evariance_congr (h : X =ᵐ[μ] Y) : eVar[X; μ] = eVar[Y; μ] := by
  simp_rw [evariance, integral_congr_ae h]
  apply lintegral_congr_ae
  filter_upwards [h] with ω hω using by simp [hω]

theorem variance_congr (h : X =ᵐ[μ] Y) : Var[X; μ] = Var[Y; μ] := by
  simp_rw [variance, evariance_congr h]

theorem evariance_lt_top [IsFiniteMeasure μ] (hX : MemLp X 2 μ) : evariance X μ < ∞ := by
  have := ENNReal.pow_lt_top (hX.sub <| memLp_const <| μ[X]).2 (n := 2)
  rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, ← ENNReal.rpow_two] at this
  simp only [ENNReal.toReal_ofNat, Pi.sub_apply, one_div] at this
  rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), ENNReal.rpow_one] at this
  simp_rw [ENNReal.rpow_two] at this
  exact this

lemma evariance_ne_top [IsFiniteMeasure μ] (hX : MemLp X 2 μ) : evariance X μ ≠ ∞ :=
  (evariance_lt_top hX).ne

theorem evariance_eq_top [IsFiniteMeasure μ] (hXm : AEStronglyMeasurable X μ) (hX : ¬MemLp X 2 μ) :
    evariance X μ = ∞ := by
  by_contra h
  rw [← Ne, ← lt_top_iff_ne_top] at h
  have : MemLp (fun ω => X ω - μ[X]) 2 μ := by
    refine ⟨by fun_prop, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    exact ENNReal.rpow_lt_top_of_nonneg (by linarith) h.ne
  refine hX ?_
  convert this.add (memLp_const μ[X])
  ext ω
  rw [Pi.add_apply, sub_add_cancel]

theorem evariance_lt_top_iff_memLp [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ) :
    evariance X μ < ∞ ↔ MemLp X 2 μ where
  mp := by contrapose!; rw [top_le_iff]; exact evariance_eq_top hX
  mpr := evariance_lt_top

@[deprecated (since := "2025-02-21")]
alias evariance_lt_top_iff_memℒp := evariance_lt_top_iff_memLp

lemma evariance_eq_top_iff [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ) :
    evariance X μ = ∞ ↔ ¬ MemLp X 2 μ := by simp [← evariance_lt_top_iff_memLp hX]

lemma variance_of_not_memLp [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ)
    (hX_not : ¬ MemLp X 2 μ) :
    variance X μ = 0 := by simp [variance, (evariance_eq_top_iff hX).mpr hX_not]

theorem ofReal_variance [IsFiniteMeasure μ] (hX : MemLp X 2 μ) :
    .ofReal (variance X μ) = evariance X μ := by
  rw [variance, ENNReal.ofReal_toReal]
  exact evariance_ne_top hX

protected alias _root_.MeasureTheory.MemLp.evariance_lt_top := evariance_lt_top
protected alias _root_.MeasureTheory.MemLp.evariance_ne_top := evariance_ne_top
protected alias _root_.MeasureTheory.MemLp.ofReal_variance_eq := ofReal_variance

@[deprecated (since := "2025-02-21")]
protected alias _root_.MeasureTheory.Memℒp.evariance_lt_top := evariance_lt_top
@[deprecated (since := "2025-02-21")]
protected alias _root_.MeasureTheory.Memℒp.evariance_ne_top := evariance_ne_top
@[deprecated (since := "2025-02-21")]
protected alias _root_.MeasureTheory.Memℒp.ofReal_variance_eq := ofReal_variance

variable (X μ) in
theorem evariance_eq_lintegral_ofReal :
    evariance X μ = ∫⁻ ω, ENNReal.ofReal ((X ω - μ[X]) ^ 2) ∂μ := by
  simp [evariance, ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]

lemma variance_eq_integral (hX : AEMeasurable X μ) : Var[X; μ] = ∫ ω, (X ω - μ[X]) ^ 2 ∂μ := by
  simp [variance, evariance, toReal_enorm, ← integral_toReal ((hX.sub_const _).enorm.pow_const _) <|
    .of_forall fun _ ↦ ENNReal.pow_lt_top enorm_lt_top]

lemma variance_of_integral_eq_zero (hX : AEMeasurable X μ) (hXint : μ[X] = 0) :
    variance X μ = ∫ ω, X ω ^ 2 ∂μ := by
  simp [variance_eq_integral hX, hXint]

@[deprecated (since := "2025-01-23")]
alias _root_.MeasureTheory.Memℒp.variance_eq := variance_eq_integral

@[deprecated (since := "2025-01-23")]
alias _root_.MeasureTheory.Memℒp.variance_eq_of_integral_eq_zero := variance_of_integral_eq_zero

@[simp]
theorem evariance_zero : evariance 0 μ = 0 := by simp [evariance]

theorem evariance_eq_zero_iff (hX : AEMeasurable X μ) :
    evariance X μ = 0 ↔ X =ᵐ[μ] fun _ => μ[X] := by
  simp [evariance, lintegral_eq_zero_iff' ((hX.sub_const _).enorm.pow_const _), EventuallyEq,
    sub_eq_zero]

theorem evariance_mul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    evariance (fun ω => c * X ω) μ = ENNReal.ofReal (c ^ 2) * evariance X μ := by
  rw [evariance, evariance, ← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
  congr with ω
  rw [integral_const_mul, ← mul_sub, enorm_mul, mul_pow, ← enorm_pow,
    Real.enorm_of_nonneg (sq_nonneg _)]

@[simp]
theorem variance_zero (μ : Measure Ω) : variance 0 μ = 0 := by
  simp only [variance, evariance_zero, ENNReal.toReal_zero]

lemma covariance_self {X : Ω → ℝ} (hX : AEMeasurable X μ) :
    cov[X, X; μ] = Var[X; μ] := by
  rw [covariance, variance_eq_integral hX]
  congr with x
  ring

@[deprecated (since := "2025-06-25")] alias covariance_same := covariance_self

theorem variance_nonneg (X : Ω → ℝ) (μ : Measure Ω) : 0 ≤ variance X μ :=
  ENNReal.toReal_nonneg

theorem variance_mul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    variance (fun ω => c * X ω) μ = c ^ 2 * variance X μ := by
  rw [variance, evariance_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl

theorem variance_smul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    variance (c • X) μ = c ^ 2 * variance X μ :=
  variance_mul c X μ

theorem variance_smul' {A : Type*} [CommSemiring A] [Algebra A ℝ] (c : A) (X : Ω → ℝ)
    (μ : Measure Ω) : variance (c • X) μ = c ^ 2 • variance X μ := by
  convert variance_smul (algebraMap A ℝ c) X μ using 1
  · congr; simp only [algebraMap_smul]
  · simp only [Algebra.smul_def, map_pow]

theorem variance_def' [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    variance X μ = μ[X ^ 2] - μ[X] ^ 2 := by
  simp only [variance_eq_integral hX.aestronglyMeasurable.aemeasurable, sub_sq']
  rw [integral_sub, integral_add]; rotate_left
  · exact hX.integrable_sq
  · apply integrable_const
  · apply hX.integrable_sq.add
    apply integrable_const
  · exact ((hX.integrable one_le_two).const_mul 2).mul_const' _
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul, integral_mul_const,
    integral_const_mul, Pi.pow_apply]
  ring

lemma variance_add_const [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : ℝ) :
    Var[fun ω ↦ X ω + c; μ] = Var[X; μ] := by
  by_cases hX_Lp : MemLp X 2 μ
  · have hX_int : Integrable X μ := hX_Lp.integrable one_le_two
    rw [variance_eq_integral (hX.add_const _).aemeasurable,
      integral_add hX_int (by fun_prop), integral_const, variance_eq_integral hX.aemeasurable]
    simp
  · rw [variance_of_not_memLp (hX.add_const _), variance_of_not_memLp hX hX_Lp]
    refine fun h_memLp ↦ hX_Lp ?_
    have : X = fun ω ↦ X ω + c - c := by ext; ring
    rw [this]
    exact h_memLp.sub (memLp_const c)

lemma variance_const_add [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : ℝ) :
    Var[fun ω ↦ c + X ω; μ] = Var[X; μ] := by
  simp_rw [add_comm c, variance_add_const hX c]

lemma variance_fun_neg : Var[fun ω ↦ -X ω; μ] = Var[X; μ] := by
  convert variance_mul (-1) X μ
  · ext; ring
  · simp

lemma variance_neg : Var[-X; μ] = Var[X; μ] := variance_fun_neg

lemma variance_sub_const [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : ℝ) :
    Var[fun ω ↦ X ω - c; μ] = Var[X; μ] := by
  simp_rw [sub_eq_add_neg, variance_add_const hX (-c)]

lemma variance_const_sub [IsProbabilityMeasure μ] (hX : AEStronglyMeasurable X μ) (c : ℝ) :
    Var[fun ω ↦ c - X ω; μ] = Var[X; μ] := by
  simp_rw [sub_eq_add_neg]
  rw [variance_const_add (by fun_prop) c, variance_fun_neg]

lemma variance_add [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Var[X + Y; μ] = Var[X; μ] + 2 * cov[X, Y; μ] + Var[Y; μ] := by
  rw [← covariance_self, covariance_add_left hX hY (hX.add hY), covariance_add_right hX hX hY,
    covariance_add_right hY hX hY, covariance_self, covariance_self, covariance_comm]
  · ring
  · exact hY.aemeasurable
  · exact hX.aemeasurable
  · exact hX.aemeasurable.add hY.aemeasurable

lemma variance_fun_add [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Var[fun ω ↦ X ω + Y ω; μ] = Var[X; μ] + 2 * cov[X, Y; μ] + Var[Y; μ] :=
  variance_add hX hY

lemma variance_sub [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
     Var[X - Y; μ] = Var[X; μ] - 2 * cov[X, Y; μ] + Var[Y; μ] := by
   rw [sub_eq_add_neg, variance_add hX hY.neg, variance_neg, covariance_neg_right]
   ring

lemma variance_fun_sub [IsFiniteMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    Var[fun ω ↦ X ω - Y ω; μ] = Var[X; μ] - 2 * cov[X, Y; μ] + Var[Y; μ] :=
  variance_sub hX hY

variable {ι : Type*} {s : Finset ι} {X : (i : ι) → Ω → ℝ}

lemma variance_sum' [IsFiniteMeasure μ] (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    Var[∑ i ∈ s, X i; μ] = ∑ i ∈ s, ∑ j ∈ s, cov[X i, X j; μ] := by
  rw [← covariance_self, covariance_sum_left' (by simpa)]
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [covariance_sum_right' (by simpa) (hX i hi)]
  · exact memLp_finset_sum' _ (by simpa)
  · exact (memLp_finset_sum' _ (by simpa)).aemeasurable

lemma variance_sum [IsFiniteMeasure μ] [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) :
    Var[∑ i, X i; μ] = ∑ i, ∑ j, cov[X i, X j; μ] :=
  variance_sum' (fun _ _ ↦ hX _)

lemma variance_fun_sum' [IsFiniteMeasure μ] (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    Var[fun ω ↦ ∑ i ∈ s, X i ω; μ] = ∑ i ∈ s, ∑ j ∈ s, cov[X i, X j; μ] := by
  convert variance_sum' hX
  simp

lemma variance_fun_sum [IsFiniteMeasure μ] [Fintype ι] (hX : ∀ i, MemLp (X i) 2 μ) :
    Var[fun ω ↦ ∑ i, X i ω; μ] = ∑ i, ∑ j, cov[X i, X j; μ] := by
  convert variance_sum hX
  simp

variable {X : Ω → ℝ}

@[simp]
lemma variance_dirac [MeasurableSingletonClass Ω] (x : Ω) : Var[X; Measure.dirac x] = 0 := by
  rw [variance_eq_integral]
  · simp
  · exact aemeasurable_dirac

lemma variance_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {Y : Ω' → Ω} (hX : AEMeasurable X (μ.map Y)) (hY : AEMeasurable Y μ) :
    Var[X; μ.map Y] = Var[X ∘ Y; μ] := by
  rw [variance_eq_integral hX, integral_map hY, variance_eq_integral (hX.comp_aemeasurable hY),
    integral_map hY]
  · congr
  · exact hX.aestronglyMeasurable
  · refine AEStronglyMeasurable.pow ?_ _
    exact AEMeasurable.aestronglyMeasurable (by fun_prop)

lemma variance_map_equiv {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    (X : Ω → ℝ) (Y : Ω' ≃ᵐ Ω) :
    Var[X; μ.map Y] = Var[X ∘ Y; μ] := by
  simp_rw [variance, evariance, lintegral_map_equiv, integral_map_equiv]
  rfl

lemma variance_id_map (hX : AEMeasurable X μ) : Var[id; μ.map X] = Var[X; μ] := by
  simp [variance_map measurable_id.aemeasurable hX]

theorem variance_le_expectation_sq [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hm : AEStronglyMeasurable X μ) : variance X μ ≤ μ[X ^ 2] := by
  by_cases hX : MemLp X 2 μ
  · rw [variance_def' hX]
    simp only [sq_nonneg, sub_le_self_iff]
  rw [variance, evariance_eq_lintegral_ofReal, ← integral_eq_lintegral_of_nonneg_ae]
  · by_cases hint : Integrable X μ; swap
    · simp only [integral_undef hint, Pi.pow_apply, sub_zero]
      exact le_rfl
    · rw [integral_undef]
      · exact integral_nonneg fun a => sq_nonneg _
      intro h
      have A : MemLp (X - fun ω : Ω => μ[X]) 2 μ :=
        (memLp_two_iff_integrable_sq (by fun_prop)).2 h
      have B : MemLp (fun _ : Ω => μ[X]) 2 μ := memLp_const _
      apply hX
      convert A.add B
      simp
  · exact Eventually.of_forall fun x => sq_nonneg _
  · exact (AEMeasurable.pow_const (hm.aemeasurable.sub_const _) _).aestronglyMeasurable

theorem evariance_def' [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) :
    evariance X μ = (∫⁻ ω, ‖X ω‖ₑ ^ 2 ∂μ) - ENNReal.ofReal (μ[X] ^ 2) := by
  by_cases hℒ : MemLp X 2 μ
  · rw [← ofReal_variance hℒ, variance_def' hℒ, ENNReal.ofReal_sub _ (sq_nonneg _)]
    congr
    simp_rw [← enorm_pow, enorm]
    rw [lintegral_coe_eq_integral]
    · simp
    · simpa using hℒ.abs.integrable_sq
  · symm
    rw [evariance_eq_top hX hℒ, ENNReal.sub_eq_top_iff]
    refine ⟨?_, ENNReal.ofReal_ne_top⟩
    rw [MemLp, not_and] at hℒ
    specialize hℒ hX
    simp only [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top, not_lt, top_le_iff,
      ENNReal.toReal_ofNat, one_div, ENNReal.rpow_eq_top_iff, inv_lt_zero, inv_pos, and_true,
      or_iff_not_imp_left, not_and_or, zero_lt_two] at hℒ
    exact mod_cast hℒ fun _ => zero_le_two

set_option linter.deprecated false in
/-- **Chebyshev's inequality** for `ℝ≥0∞`-valued variance. -/
theorem meas_ge_le_evariance_div_sq {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) {c : ℝ≥0}
    (hc : c ≠ 0) : μ {ω | ↑c ≤ |X ω - μ[X]|} ≤ evariance X μ / c ^ 2 := by
  have A : (c : ℝ≥0∞) ≠ 0 := by rwa [Ne, ENNReal.coe_eq_zero]
  have B : AEStronglyMeasurable (fun _ : Ω => μ[X]) μ := aestronglyMeasurable_const
  convert meas_ge_le_mul_pow_eLpNorm μ two_ne_zero ENNReal.ofNat_ne_top (hX.sub B) A using 1
  · congr
    simp only [Pi.sub_apply, ENNReal.coe_le_coe, ← Real.norm_eq_abs, ← coe_nnnorm,
      NNReal.coe_le_coe]
  · rw [eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, one_div, Pi.sub_apply]
    rw [div_eq_mul_inv, ENNReal.inv_pow, mul_comm, ENNReal.rpow_two]
    congr
    simp_rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), ENNReal.rpow_two,
      ENNReal.rpow_one, evariance]


/-- **Chebyshev's inequality**: one can control the deviation probability of a real random variable
from its expectation in terms of the variance. -/
theorem meas_ge_le_variance_div_sq [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) {c : ℝ}
    (hc : 0 < c) : μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (variance X μ / c ^ 2) := by
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_ne_zero hc.ne.symm), hX.ofReal_variance_eq]
  convert @meas_ge_le_evariance_div_sq _ _ _ _ hX.1 c.toNNReal (by simp [hc]) using 1
  · simp only [Real.coe_toNNReal', max_le_iff, abs_nonneg, and_true]
  · rw [ENNReal.ofReal_pow hc.le]
    rfl

-- Porting note: supplied `MeasurableSpace Ω` argument of `h` by unification
/-- The variance of the sum of two independent random variables is the sum of the variances. -/
nonrec theorem IndepFun.variance_add {X Y : Ω → ℝ} (hX : MemLp X 2 μ)
    (hY : MemLp Y 2 μ) (h : IndepFun X Y μ) : Var[X + Y; μ] = Var[X; μ] + Var[Y; μ] := by
  by_cases h' : X =ᵐ[μ] 0
  · rw [variance_congr h', variance_congr h'.add_right]
    simp
  have := hX.isProbabilityMeasure_of_indepFun X Y (by simp) (by simp) h' h
  rw [variance_add hX hY, h.covariance_eq_zero hX hY]
  simp

-- Porting note: supplied `MeasurableSpace Ω` argument of `hs`, `h` by unification
/-- The variance of a finite sum of pairwise independent random variables is the sum of the
variances. -/
nonrec theorem IndepFun.variance_sum {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι}
    (hs : ∀ i ∈ s, MemLp (X i) 2 μ)
    (h : Set.Pairwise ↑s fun i j => IndepFun (X i) (X j) μ) :
    variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, variance (X i) μ := by
  by_cases h'' : ∀ i ∈ s, X i =ᵐ[μ] 0
  · rw [variance_congr (Y := 0), variance_zero]
    · symm
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      simp [variance_congr (h'' i hi)]
    · have := fun (i : s) ↦ h'' i.1 i.2
      filter_upwards [ae_all_iff.2 this] with ω hω
      simp only [sum_apply, Pi.zero_apply]
      exact Finset.sum_eq_zero fun i hi ↦ hω ⟨i, hi⟩
  obtain ⟨j, hj1, hj2⟩ := not_forall₂.1 h''
  obtain rfl | h' := s.eq_singleton_or_nontrivial hj1
  · simp
  obtain ⟨k, hk1, hk2⟩ := h'.exists_ne j
  have := (hs j hj1).isProbabilityMeasure_of_indepFun (X j) (X k) (by simp) (by simp) hj2
    (h hj1 hk1 hk2.symm)
  rw [variance_sum' hs]
  refine Finset.sum_congr rfl (fun i hi ↦ ?_)
  rw [← covariance_self (hs i hi).aemeasurable]
  refine Finset.sum_eq_single_of_mem i hi fun j hj1 hj2 ↦ ?_
  exact (h hi hj1 hj2.symm).covariance_eq_zero (hs i hi) (hs j hj1)

/-- **The Bhatia-Davis inequality on variance**

The variance of a random variable `X` satisfying `a ≤ X ≤ b` almost everywhere is at most
`(b - 𝔼 X) * (𝔼 X - a)`. -/
lemma variance_le_sub_mul_sub [IsProbabilityMeasure μ] {a b : ℝ} {X : Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hX : AEMeasurable X μ) :
    variance X μ ≤ (b - μ[X]) * (μ[X] - a) := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h => h.1
  have hb : ∀ᵐ ω ∂μ, X ω ≤ b := h.mono fun ω h => h.2
  have hX_int₂ : Integrable (fun ω ↦ -X ω ^ 2) μ :=
    (memLp_of_bounded h hX.aestronglyMeasurable 2).integrable_sq.neg
  have hX_int₁ : Integrable (fun ω ↦ (a + b) * X ω) μ :=
    ((integrable_const (max |a| |b|)).mono' hX.aestronglyMeasurable
      (by filter_upwards [ha, hb] with ω using abs_le_max_abs_abs)).const_mul (a + b)
  have h0 : 0 ≤ -μ[X ^ 2] + (a + b) * μ[X] - a * b :=
    calc
      _ ≤ ∫ ω, (b - X ω) * (X ω - a) ∂μ := by
        apply integral_nonneg_of_ae
        filter_upwards [ha, hb] with ω ha' hb'
        exact mul_nonneg (by linarith : 0 ≤ b - X ω) (by linarith : 0 ≤ X ω - a)
      _ = ∫ ω, -X ω ^ 2 + (a + b) * X ω - a * b ∂μ :=
        integral_congr_ae <| ae_of_all μ fun ω ↦ by ring
      _ = ∫ ω, - X ω ^ 2 + (a + b) * X ω ∂μ - ∫ _, a * b ∂μ :=
        integral_sub (by fun_prop) (integrable_const (a * b))
      _ = ∫ ω, - X ω ^ 2 + (a + b) * X ω ∂μ - a * b := by simp
      _ = - μ[X ^ 2] + (a + b) * μ[X] - a * b := by
        simp [← integral_neg, ← integral_const_mul, integral_add hX_int₂ hX_int₁]
  calc
    _ ≤ (a + b) * μ[X] - a * b - μ[X] ^ 2 := by
      rw [variance_def' (memLp_of_bounded h hX.aestronglyMeasurable 2)]
      linarith
    _ = (b - μ[X]) * (μ[X] - a) := by ring

/-- **Popoviciu's inequality on variance**

The variance of a random variable `X` satisfying `a ≤ X ≤ b` almost everywhere is at most
`((b - a) / 2) ^ 2`. -/
lemma variance_le_sq_of_bounded [IsProbabilityMeasure μ] {a b : ℝ} {X : Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hX : AEMeasurable X μ) :
    variance X μ ≤ ((b - a) / 2) ^ 2 :=
  calc
    _ ≤ (b - μ[X]) * (μ[X] - a) := variance_le_sub_mul_sub h hX
    _ = ((b - a) / 2) ^ 2 - (μ[X] - (b + a) / 2) ^ 2 := by ring
    _ ≤ ((b - a) / 2) ^ 2 := sub_le_self _ (sq_nonneg _)

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)}

variable {𝒳 : ι → Type*} [∀ i, MeasurableSpace (𝒳 i)] {X : Π i, Ω i → 𝒳 i}

variable [∀ i, IsProbabilityMeasure (μ i)]

lemma iIndepFun_pi (mX : ∀ i, Measurable (X i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ) := by
  refine @iIndepFun_iff_map_fun_eq_pi_map (Π i, Ω i) ι _ (Measure.pi μ) _ 𝒳 _
    (fun i x ↦ X i (x i)) _ ?_ |>.2 ?_
  · exact fun i ↦ Measurable.aemeasurable (by fun_prop)
  · symm
    refine Measure.pi_eq fun s hs ↦ ?_
    rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
    have : (fun (ω : Π i, Ω i) i ↦ X i (ω i)) ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun i ↦ (X i) ⁻¹' (s i)) := by ext x; simp
    rw [this, Measure.pi_pi]
    congr with i
    rw [Measure.map_apply (by fun_prop) (hs i)]
    change _ = (Measure.pi μ) (((X i) ∘ (fun x ↦ x i)) ⁻¹' s i)
    rw [Set.preimage_comp, ← Measure.map_apply (measurable_pi_apply i) (mX i (hs i)),
      (measurePreserving_eval i).map_eq]

lemma iIndepFun_pi₀ (mX : ∀ i, AEMeasurable (X i) (μ i)) :
    iIndepFun (fun i ω ↦ X i (ω i)) (Measure.pi μ) := by
  have : iIndepFun (fun i ω ↦ (mX i).mk (X i) (ω i)) (Measure.pi μ) :=
    iIndepFun_pi fun i ↦ (mX i).measurable_mk
  refine this.congr fun i ↦ ?_
  change ((mX i).mk (X i)) ∘ Function.eval i =ᶠ[_] (X i) ∘ Function.eval i
  apply ae_eq_comp
  · exact (measurable_pi_apply i).aemeasurable
  · rw [(measurePreserving_eval i).map_eq]
    exact (AEMeasurable.ae_eq_mk (mX i)).symm

lemma variance_pi {X : Π i, Ω i → ℝ} (h : ∀ i, MemLp (X i) 2 (μ i)) :
    Var[∑ i, fun ω ↦ X i (ω i); Measure.pi μ] = ∑ i, Var[X i; μ i] := by
  rw [IndepFun.variance_sum]
  · congr with i
    change Var[(X i) ∘ (fun ω ↦ ω i); Measure.pi μ] = _
    rw [← variance_map, (measurePreserving_eval i).map_eq]
    · rw [(measurePreserving_eval i).map_eq]
      exact (h i).aemeasurable
    · exact Measurable.aemeasurable (by fun_prop)
  · exact fun i _ ↦ (h i).comp_measurePreserving (measurePreserving_eval i)
  · exact fun i _ j _ hij ↦
      (iIndepFun_pi₀ fun i ↦ (h i).aemeasurable).indepFun hij

end ProbabilityTheory
