/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Kexing Ying
-/
import Mathlib.Probability.Notation
import Mathlib.Probability.Integration
import Mathlib.MeasureTheory.Function.L2Space

#align_import probability.variance from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

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
-/


open MeasureTheory Filter Finset

noncomputable section

open scoped MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory

-- Porting note: this lemma replaces `ENNReal.toReal_bit0`, which does not exist in Lean 4
private lemma coe_two : ENNReal.toReal 2 = (2 : ℝ) := rfl

-- Porting note: Consider if `evariance` or `eVariance` is better. Also,
-- consider `eVariationOn` in `Mathlib.Analysis.BoundedVariation`.
/-- The `ℝ≥0∞`-valued variance of a real-valued random variable defined as the Lebesgue integral of
`(X - 𝔼[X])^2`. -/
def evariance {Ω : Type*} {_ : MeasurableSpace Ω} (X : Ω → ℝ) (μ : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ ω, (‖X ω - μ[X]‖₊ : ℝ≥0∞) ^ 2 ∂μ
#align probability_theory.evariance ProbabilityTheory.evariance

/-- The `ℝ`-valued variance of a real-valued random variable defined by applying `ENNReal.toReal`
to `evariance`. -/
def variance {Ω : Type*} {_ : MeasurableSpace Ω} (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  (evariance X μ).toReal
#align probability_theory.variance ProbabilityTheory.variance

variable {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω}

theorem _root_.MeasureTheory.Memℒp.evariance_lt_top [IsFiniteMeasure μ] (hX : Memℒp X 2 μ) :
    evariance X μ < ∞ := by
  have := ENNReal.pow_lt_top (hX.sub <| memℒp_const <| μ[X]).2 2
  rw [snorm_eq_lintegral_rpow_nnnorm two_ne_zero ENNReal.two_ne_top, ← ENNReal.rpow_two] at this
  simp only [coe_two, Pi.sub_apply, ENNReal.one_toReal, one_div] at this
  rw [← ENNReal.rpow_mul, inv_mul_cancel (two_ne_zero : (2 : ℝ) ≠ 0), ENNReal.rpow_one] at this
  simp_rw [ENNReal.rpow_two] at this
  exact this
#align measure_theory.mem_ℒp.evariance_lt_top MeasureTheory.Memℒp.evariance_lt_top

theorem evariance_eq_top [IsFiniteMeasure μ] (hXm : AEStronglyMeasurable X μ) (hX : ¬Memℒp X 2 μ) :
    evariance X μ = ∞ := by
  by_contra h
  rw [← Ne, ← lt_top_iff_ne_top] at h
  have : Memℒp (fun ω => X ω - μ[X]) 2 μ := by
    refine ⟨hXm.sub aestronglyMeasurable_const, ?_⟩
    rw [snorm_eq_lintegral_rpow_nnnorm two_ne_zero ENNReal.two_ne_top]
    simp only [coe_two, ENNReal.one_toReal, ENNReal.rpow_two, Ne]
    exact ENNReal.rpow_lt_top_of_nonneg (by linarith) h.ne
  refine hX ?_
  -- Porting note: `μ[X]` without whitespace is ambiguous as it could be GetElem,
  -- and `convert` cannot disambiguate based on typeclass inference failure.
  convert this.add (memℒp_const <| μ [X])
  ext ω
  rw [Pi.add_apply, sub_add_cancel]
#align probability_theory.evariance_eq_top ProbabilityTheory.evariance_eq_top

theorem evariance_lt_top_iff_memℒp [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ) :
    evariance X μ < ∞ ↔ Memℒp X 2 μ := by
  refine ⟨?_, MeasureTheory.Memℒp.evariance_lt_top⟩
  contrapose
  rw [not_lt, top_le_iff]
  exact evariance_eq_top hX
#align probability_theory.evariance_lt_top_iff_mem_ℒp ProbabilityTheory.evariance_lt_top_iff_memℒp

theorem _root_.MeasureTheory.Memℒp.ofReal_variance_eq [IsFiniteMeasure μ] (hX : Memℒp X 2 μ) :
    ENNReal.ofReal (variance X μ) = evariance X μ := by
  rw [variance, ENNReal.ofReal_toReal]
  exact hX.evariance_lt_top.ne
#align measure_theory.mem_ℒp.of_real_variance_eq MeasureTheory.Memℒp.ofReal_variance_eq

theorem evariance_eq_lintegral_ofReal (X : Ω → ℝ) (μ : Measure Ω) :
    evariance X μ = ∫⁻ ω, ENNReal.ofReal ((X ω - μ[X]) ^ 2) ∂μ := by
  rw [evariance]
  congr
  ext1 ω
  rw [pow_two, ← ENNReal.coe_mul, ← nnnorm_mul, ← pow_two]
  congr
  exact (Real.toNNReal_eq_nnnorm_of_nonneg <| sq_nonneg _).symm
#align probability_theory.evariance_eq_lintegral_of_real ProbabilityTheory.evariance_eq_lintegral_ofReal

theorem _root_.MeasureTheory.Memℒp.variance_eq_of_integral_eq_zero (hX : Memℒp X 2 μ)
    (hXint : μ[X] = 0) : variance X μ = μ[X ^ (2 : Nat)] := by
  rw [variance, evariance_eq_lintegral_ofReal, ← ofReal_integral_eq_lintegral_ofReal,
      ENNReal.toReal_ofReal (by positivity)] <;>
    simp_rw [hXint, sub_zero]
  · rfl
  · convert hX.integrable_norm_rpow two_ne_zero ENNReal.two_ne_top with ω
    simp only [Pi.sub_apply, Real.norm_eq_abs, coe_two, ENNReal.one_toReal,
      Real.rpow_two, sq_abs, abs_pow]
  · exact ae_of_all _ fun ω => pow_two_nonneg _
#align measure_theory.mem_ℒp.variance_eq_of_integral_eq_zero MeasureTheory.Memℒp.variance_eq_of_integral_eq_zero

theorem _root_.MeasureTheory.Memℒp.variance_eq [IsFiniteMeasure μ] (hX : Memℒp X 2 μ) :
    variance X μ = μ[(X - fun _ => μ[X] :) ^ (2 : Nat)] := by
  rw [variance, evariance_eq_lintegral_ofReal, ← ofReal_integral_eq_lintegral_ofReal,
    ENNReal.toReal_ofReal (by positivity)]
  · rfl
  · -- Porting note: `μ[X]` without whitespace is ambiguous as it could be GetElem,
    -- and `convert` cannot disambiguate based on typeclass inference failure.
    convert (hX.sub <| memℒp_const (μ [X])).integrable_norm_rpow two_ne_zero ENNReal.two_ne_top
      with ω
    simp only [Pi.sub_apply, Real.norm_eq_abs, coe_two, ENNReal.one_toReal,
      Real.rpow_two, sq_abs, abs_pow]
  · exact ae_of_all _ fun ω => pow_two_nonneg _
#align measure_theory.mem_ℒp.variance_eq MeasureTheory.Memℒp.variance_eq

@[simp]
theorem evariance_zero : evariance 0 μ = 0 := by simp [evariance]
#align probability_theory.evariance_zero ProbabilityTheory.evariance_zero

theorem evariance_eq_zero_iff (hX : AEMeasurable X μ) :
    evariance X μ = 0 ↔ X =ᵐ[μ] fun _ => μ[X] := by
  rw [evariance, lintegral_eq_zero_iff']
  constructor <;> intro hX <;> filter_upwards [hX] with ω hω
  · simpa only [Pi.zero_apply, sq_eq_zero_iff, ENNReal.coe_eq_zero, nnnorm_eq_zero, sub_eq_zero]
      using hω
  · rw [hω]
    simp
  · exact (hX.sub_const _).ennnorm.pow_const _ -- TODO `measurability` and `fun_prop` fail
#align probability_theory.evariance_eq_zero_iff ProbabilityTheory.evariance_eq_zero_iff

theorem evariance_mul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    evariance (fun ω => c * X ω) μ = ENNReal.ofReal (c ^ 2) * evariance X μ := by
  rw [evariance, evariance, ← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
  congr
  ext1 ω
  rw [ENNReal.ofReal, ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_mul]
  congr
  rw [← sq_abs, ← Real.rpow_two, Real.toNNReal_rpow_of_nonneg (abs_nonneg _), NNReal.rpow_two,
    ← mul_pow, Real.toNNReal_mul_nnnorm _ (abs_nonneg _)]
  conv_rhs => rw [← nnnorm_norm, norm_mul, norm_abs_eq_norm, ← norm_mul, nnnorm_norm, mul_sub]
  congr
  rw [mul_comm]
  simp_rw [← smul_eq_mul, ← integral_smul_const, smul_eq_mul, mul_comm]
#align probability_theory.evariance_mul ProbabilityTheory.evariance_mul

scoped notation "eVar[" X "]" => ProbabilityTheory.evariance X MeasureTheory.MeasureSpace.volume

@[simp]
theorem variance_zero (μ : Measure Ω) : variance 0 μ = 0 := by
  simp only [variance, evariance_zero, ENNReal.zero_toReal]
#align probability_theory.variance_zero ProbabilityTheory.variance_zero

theorem variance_nonneg (X : Ω → ℝ) (μ : Measure Ω) : 0 ≤ variance X μ :=
  ENNReal.toReal_nonneg
#align probability_theory.variance_nonneg ProbabilityTheory.variance_nonneg

theorem variance_mul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    variance (fun ω => c * X ω) μ = c ^ 2 * variance X μ := by
  rw [variance, evariance_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl
#align probability_theory.variance_mul ProbabilityTheory.variance_mul

theorem variance_smul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    variance (c • X) μ = c ^ 2 * variance X μ :=
  variance_mul c X μ
#align probability_theory.variance_smul ProbabilityTheory.variance_smul

theorem variance_smul' {A : Type*} [CommSemiring A] [Algebra A ℝ] (c : A) (X : Ω → ℝ)
    (μ : Measure Ω) : variance (c • X) μ = c ^ 2 • variance X μ := by
  convert variance_smul (algebraMap A ℝ c) X μ using 1
  · congr; simp only [algebraMap_smul]
  · simp only [Algebra.smul_def, map_pow]
#align probability_theory.variance_smul' ProbabilityTheory.variance_smul'

scoped notation "Var[" X "]" => ProbabilityTheory.variance X MeasureTheory.MeasureSpace.volume

variable [MeasureSpace Ω]

theorem variance_def' [@IsProbabilityMeasure Ω _ ℙ] {X : Ω → ℝ} (hX : Memℒp X 2) :
    Var[X] = 𝔼[X ^ 2] - 𝔼[X] ^ 2 := by
  rw [hX.variance_eq, sub_sq', integral_sub', integral_add']; rotate_left
  · exact hX.integrable_sq
  · convert @integrable_const Ω ℝ (_) ℙ _ _ (𝔼[X] ^ 2)
  · apply hX.integrable_sq.add
    convert @integrable_const Ω ℝ (_) ℙ _ _ (𝔼[X] ^ 2)
  · exact ((hX.integrable one_le_two).const_mul 2).mul_const' _
  simp only [Pi.pow_apply, integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul,
    Pi.mul_apply, Pi.ofNat_apply, Nat.cast_ofNat, integral_mul_right, integral_mul_left]
  ring
#align probability_theory.variance_def' ProbabilityTheory.variance_def'

theorem variance_le_expectation_sq [@IsProbabilityMeasure Ω _ ℙ] {X : Ω → ℝ}
    (hm : AEStronglyMeasurable X ℙ) : Var[X] ≤ 𝔼[X ^ 2] := by
  by_cases hX : Memℒp X 2
  · rw [variance_def' hX]
    simp only [sq_nonneg, sub_le_self_iff]
  rw [variance, evariance_eq_lintegral_ofReal, ← integral_eq_lintegral_of_nonneg_ae]
  · by_cases hint : Integrable X; swap
    · simp only [integral_undef hint, Pi.pow_apply, Pi.sub_apply, sub_zero]
      exact le_rfl
    · rw [integral_undef]
      · exact integral_nonneg fun a => sq_nonneg _
      intro h
      have A : Memℒp (X - fun ω : Ω => 𝔼[X]) 2 ℙ :=
        (memℒp_two_iff_integrable_sq (hint.aestronglyMeasurable.sub aestronglyMeasurable_const)).2 h
      have B : Memℒp (fun _ : Ω => 𝔼[X]) 2 ℙ := memℒp_const _
      apply hX
      convert A.add B
      simp
  · exact eventually_of_forall fun x => sq_nonneg _
  · exact (AEMeasurable.pow_const (hm.aemeasurable.sub_const _) _).aestronglyMeasurable
#align probability_theory.variance_le_expectation_sq ProbabilityTheory.variance_le_expectation_sq

theorem evariance_def' [@IsProbabilityMeasure Ω _ ℙ] {X : Ω → ℝ} (hX : AEStronglyMeasurable X ℙ) :
    eVar[X] = (∫⁻ ω, (‖X ω‖₊ ^ 2 :)) - ENNReal.ofReal (𝔼[X] ^ 2) := by
  by_cases hℒ : Memℒp X 2
  · rw [← hℒ.ofReal_variance_eq, variance_def' hℒ, ENNReal.ofReal_sub _ (sq_nonneg _)]
    congr
    rw [lintegral_coe_eq_integral]
    · congr 2 with ω
      simp only [Pi.pow_apply, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, Even.pow_abs even_two]
    · exact hℒ.abs.integrable_sq
  · symm
    rw [evariance_eq_top hX hℒ, ENNReal.sub_eq_top_iff]
    refine ⟨?_, ENNReal.ofReal_ne_top⟩
    rw [Memℒp, not_and] at hℒ
    specialize hℒ hX
    simp only [snorm_eq_lintegral_rpow_nnnorm two_ne_zero ENNReal.two_ne_top, not_lt, top_le_iff,
      coe_two, one_div, ENNReal.rpow_eq_top_iff, inv_lt_zero, inv_pos, and_true_iff,
      or_iff_not_imp_left, not_and_or, zero_lt_two] at hℒ
    exact mod_cast hℒ fun _ => zero_le_two
#align probability_theory.evariance_def' ProbabilityTheory.evariance_def'

/-- **Chebyshev's inequality** for `ℝ≥0∞`-valued variance. -/
theorem meas_ge_le_evariance_div_sq {X : Ω → ℝ} (hX : AEStronglyMeasurable X ℙ) {c : ℝ≥0}
    (hc : c ≠ 0) : ℙ {ω | ↑c ≤ |X ω - 𝔼[X]|} ≤ eVar[X] / c ^ 2 := by
  have A : (c : ℝ≥0∞) ≠ 0 := by rwa [Ne, ENNReal.coe_eq_zero]
  have B : AEStronglyMeasurable (fun _ : Ω => 𝔼[X]) ℙ := aestronglyMeasurable_const
  convert meas_ge_le_mul_pow_snorm ℙ two_ne_zero ENNReal.two_ne_top (hX.sub B) A using 1
  · congr
    simp only [Pi.sub_apply, ENNReal.coe_le_coe, ← Real.norm_eq_abs, ← coe_nnnorm,
      NNReal.coe_le_coe, ENNReal.ofReal_coe_nnreal]
  · rw [snorm_eq_lintegral_rpow_nnnorm two_ne_zero ENNReal.two_ne_top]
    simp only [show ENNReal.ofNNReal (c ^ 2) = (ENNReal.ofNNReal c) ^ 2 by norm_cast, coe_two,
      one_div, Pi.sub_apply]
    rw [div_eq_mul_inv, ENNReal.inv_pow, mul_comm, ENNReal.rpow_two]
    congr
    simp_rw [← ENNReal.rpow_mul, inv_mul_cancel (two_ne_zero : (2 : ℝ) ≠ 0), ENNReal.rpow_two,
      ENNReal.rpow_one, evariance]
#align probability_theory.meas_ge_le_evariance_div_sq ProbabilityTheory.meas_ge_le_evariance_div_sq

/-- **Chebyshev's inequality**: one can control the deviation probability of a real random variable
from its expectation in terms of the variance. -/
theorem meas_ge_le_variance_div_sq [@IsFiniteMeasure Ω _ ℙ] {X : Ω → ℝ} (hX : Memℒp X 2) {c : ℝ}
    (hc : 0 < c) : ℙ {ω | c ≤ |X ω - 𝔼[X]|} ≤ ENNReal.ofReal (Var[X] / c ^ 2) := by
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_ne_zero hc.ne.symm), hX.ofReal_variance_eq]
  convert @meas_ge_le_evariance_div_sq _ _ _ hX.1 c.toNNReal (by simp [hc]) using 1
  · simp only [Real.coe_toNNReal', max_le_iff, abs_nonneg, and_true_iff]
  · rw [ENNReal.ofReal_pow hc.le]
    rfl
#align probability_theory.meas_ge_le_variance_div_sq ProbabilityTheory.meas_ge_le_variance_div_sq

-- Porting note: supplied `MeasurableSpace Ω` argument of `h` by unification
/-- The variance of the sum of two independent random variables is the sum of the variances. -/
theorem IndepFun.variance_add [@IsProbabilityMeasure Ω _ ℙ] {X Y : Ω → ℝ} (hX : Memℒp X 2)
    (hY : Memℒp Y 2) (h : @IndepFun _ _ _ (_) _ _ X Y ℙ) : Var[X + Y] = Var[X] + Var[Y] :=
  calc
    Var[X + Y] = 𝔼[fun a => X a ^ 2 + Y a ^ 2 + 2 * X a * Y a] - 𝔼[X + Y] ^ 2 := by
      simp [variance_def' (hX.add hY), add_sq']
    _ = 𝔼[X ^ 2] + 𝔼[Y ^ 2] + (2 : ℝ) * 𝔼[X * Y] - (𝔼[X] + 𝔼[Y]) ^ 2 := by
      simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply, mul_assoc]
      rw [integral_add, integral_add, integral_add, integral_mul_left]
      · exact hX.integrable one_le_two
      · exact hY.integrable one_le_two
      · exact hX.integrable_sq
      · exact hY.integrable_sq
      · exact hX.integrable_sq.add hY.integrable_sq
      · apply Integrable.const_mul
        exact h.integrable_mul (hX.integrable one_le_two) (hY.integrable one_le_two)
    _ = 𝔼[X ^ 2] + 𝔼[Y ^ 2] + 2 * (𝔼[X] * 𝔼[Y]) - (𝔼[X] + 𝔼[Y]) ^ 2 := by
      congr
      exact h.integral_mul_of_integrable (hX.integrable one_le_two) (hY.integrable one_le_two)
    _ = Var[X] + Var[Y] := by simp only [variance_def', hX, hY, Pi.pow_apply]; ring
#align probability_theory.indep_fun.variance_add ProbabilityTheory.IndepFun.variance_add

-- Porting note: supplied `MeasurableSpace Ω` argument of `hs`, `h` by unification
/-- The variance of a finite sum of pairwise independent random variables is the sum of the
variances. -/
theorem IndepFun.variance_sum [@IsProbabilityMeasure Ω _ ℙ] {ι : Type*} {X : ι → Ω → ℝ}
    {s : Finset ι} (hs : ∀ i ∈ s, @Memℒp _ _ _ (_) (X i) 2 ℙ)
    (h : Set.Pairwise ↑s fun i j => @IndepFun _ _ _ (_) _ _ (X i) (X j) ℙ) :
    Var[∑ i ∈ s, X i] = ∑ i ∈ s, Var[X i] := by
  classical
  induction' s using Finset.induction_on with k s ks IH
  · simp only [Finset.sum_empty, variance_zero]
  rw [variance_def' (memℒp_finset_sum' _ hs), sum_insert ks, sum_insert ks]
  simp only [add_sq']
  calc
    𝔼[X k ^ 2 + (∑ i ∈ s, X i) ^ 2 + 2 * X k * ∑ i ∈ s, X i] - 𝔼[X k + ∑ i ∈ s, X i] ^ 2 =
        𝔼[X k ^ 2] + 𝔼[(∑ i ∈ s, X i) ^ 2] + 𝔼[2 * X k * ∑ i ∈ s, X i] -
          (𝔼[X k] + 𝔼[∑ i ∈ s, X i]) ^ 2 := by
      rw [integral_add', integral_add', integral_add']
      · exact Memℒp.integrable one_le_two (hs _ (mem_insert_self _ _))
      · apply integrable_finset_sum' _ fun i hi => ?_
        exact Memℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi))
      · exact Memℒp.integrable_sq (hs _ (mem_insert_self _ _))
      · apply Memℒp.integrable_sq
        exact memℒp_finset_sum' _ fun i hi => hs _ (mem_insert_of_mem hi)
      · apply Integrable.add
        · exact Memℒp.integrable_sq (hs _ (mem_insert_self _ _))
        · apply Memℒp.integrable_sq
          exact memℒp_finset_sum' _ fun i hi => hs _ (mem_insert_of_mem hi)
      · rw [mul_assoc]
        apply Integrable.const_mul _ (2 : ℝ)
        simp only [mul_sum, sum_apply, Pi.mul_apply]
        apply integrable_finset_sum _ fun i hi => ?_
        apply IndepFun.integrable_mul _ (Memℒp.integrable one_le_two (hs _ (mem_insert_self _ _)))
          (Memℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi)))
        apply h (mem_insert_self _ _) (mem_insert_of_mem hi)
        exact fun hki => ks (hki.symm ▸ hi)
    _ = Var[X k] + Var[∑ i ∈ s, X i] +
        (𝔼[2 * X k * ∑ i ∈ s, X i] - 2 * 𝔼[X k] * 𝔼[∑ i ∈ s, X i]) := by
      rw [variance_def' (hs _ (mem_insert_self _ _)),
        variance_def' (memℒp_finset_sum' _ fun i hi => hs _ (mem_insert_of_mem hi))]
      ring
    _ = Var[X k] + Var[∑ i ∈ s, X i] := by
      simp_rw [Pi.mul_apply, Pi.ofNat_apply, Nat.cast_ofNat, sum_apply, mul_sum, mul_assoc,
        add_right_eq_self]
      rw [integral_finset_sum s fun i hi => ?_]; swap
      · apply Integrable.const_mul _ (2 : ℝ)
        apply IndepFun.integrable_mul _ (Memℒp.integrable one_le_two (hs _ (mem_insert_self _ _)))
          (Memℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi)))
        apply h (mem_insert_self _ _) (mem_insert_of_mem hi)
        exact fun hki => ks (hki.symm ▸ hi)
      rw [integral_finset_sum s fun i hi =>
          Memℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi)),
        mul_sum, mul_sum, ← sum_sub_distrib]
      apply Finset.sum_eq_zero fun i hi => ?_
      rw [integral_mul_left, IndepFun.integral_mul', sub_self]
      · apply h (mem_insert_self _ _) (mem_insert_of_mem hi)
        exact fun hki => ks (hki.symm ▸ hi)
      · exact Memℒp.aestronglyMeasurable (hs _ (mem_insert_self _ _))
      · exact Memℒp.aestronglyMeasurable (hs _ (mem_insert_of_mem hi))
    _ = Var[X k] + ∑ i ∈ s, Var[X i] := by
      rw [IH (fun i hi => hs i (mem_insert_of_mem hi))
          (h.mono (by simp only [coe_insert, Set.subset_insert]))]
#align probability_theory.indep_fun.variance_sum ProbabilityTheory.IndepFun.variance_sum

end ProbabilityTheory
