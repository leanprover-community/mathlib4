/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Kexing Ying
-/
import Mathlib.Probability.Notation
import Mathlib.Probability.Integration
import Mathlib.MeasureTheory.Function.L2Space

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

-- Porting note: Consider if `evariance` or `eVariance` is better. Also,
-- consider `eVariationOn` in `Mathlib.Analysis.BoundedVariation`.
/-- The `ℝ≥0∞`-valued variance of a real-valued random variable defined as the Lebesgue integral of
`(X - 𝔼[X])^2`. -/
def evariance {Ω : Type*} {_ : MeasurableSpace Ω} (X : Ω → ℝ) (μ : Measure Ω) : ℝ≥0∞ :=
  ∫⁻ ω, (‖X ω - μ[X]‖₊ : ℝ≥0∞) ^ 2 ∂μ

/-- The `ℝ`-valued variance of a real-valued random variable defined by applying `ENNReal.toReal`
to `evariance`. -/
def variance {Ω : Type*} {_ : MeasurableSpace Ω} (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  (evariance X μ).toReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω}

theorem _root_.MeasureTheory.Memℒp.evariance_lt_top [IsFiniteMeasure μ] (hX : Memℒp X 2 μ) :
    evariance X μ < ∞ := by
  have := ENNReal.pow_lt_top (hX.sub <| memℒp_const <| μ[X]).2 2
  rw [eLpNorm_eq_lintegral_rpow_nnnorm two_ne_zero ENNReal.two_ne_top, ← ENNReal.rpow_two] at this
  simp only [ENNReal.toReal_ofNat, Pi.sub_apply, ENNReal.one_toReal, one_div] at this
  rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), ENNReal.rpow_one] at this
  simp_rw [ENNReal.rpow_two] at this
  exact this

theorem evariance_eq_top [IsFiniteMeasure μ] (hXm : AEStronglyMeasurable X μ) (hX : ¬Memℒp X 2 μ) :
    evariance X μ = ∞ := by
  by_contra h
  rw [← Ne, ← lt_top_iff_ne_top] at h
  have : Memℒp (fun ω => X ω - μ[X]) 2 μ := by
    refine ⟨hXm.sub aestronglyMeasurable_const, ?_⟩
    rw [eLpNorm_eq_lintegral_rpow_nnnorm two_ne_zero ENNReal.two_ne_top]
    simp only [ENNReal.toReal_ofNat, ENNReal.one_toReal, ENNReal.rpow_two, Ne]
    exact ENNReal.rpow_lt_top_of_nonneg (by linarith) h.ne
  refine hX ?_
  convert this.add (memℒp_const μ[X])
  ext ω
  rw [Pi.add_apply, sub_add_cancel]

theorem evariance_lt_top_iff_memℒp [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ) :
    evariance X μ < ∞ ↔ Memℒp X 2 μ := by
  refine ⟨?_, MeasureTheory.Memℒp.evariance_lt_top⟩
  contrapose
  rw [not_lt, top_le_iff]
  exact evariance_eq_top hX

theorem _root_.MeasureTheory.Memℒp.ofReal_variance_eq [IsFiniteMeasure μ] (hX : Memℒp X 2 μ) :
    ENNReal.ofReal (variance X μ) = evariance X μ := by
  rw [variance, ENNReal.ofReal_toReal]
  exact hX.evariance_lt_top.ne

theorem evariance_eq_lintegral_ofReal (X : Ω → ℝ) (μ : Measure Ω) :
    evariance X μ = ∫⁻ ω, ENNReal.ofReal ((X ω - μ[X]) ^ 2) ∂μ := by
  rw [evariance]
  congr
  ext1 ω
  rw [pow_two, ← ENNReal.coe_mul, ← nnnorm_mul, ← pow_two]
  congr
  exact (Real.toNNReal_eq_nnnorm_of_nonneg <| sq_nonneg _).symm

theorem _root_.MeasureTheory.Memℒp.variance_eq_of_integral_eq_zero (hX : Memℒp X 2 μ)
    (hXint : μ[X] = 0) : variance X μ = μ[X ^ (2 : Nat)] := by
  rw [variance, evariance_eq_lintegral_ofReal, ← ofReal_integral_eq_lintegral_ofReal,
      ENNReal.toReal_ofReal (by positivity)] <;>
    simp_rw [hXint, sub_zero]
  · rfl
  · convert hX.integrable_norm_rpow two_ne_zero ENNReal.two_ne_top with ω
    simp only [Pi.sub_apply, Real.norm_eq_abs, ENNReal.toReal_ofNat, ENNReal.one_toReal,
      Real.rpow_two, sq_abs, abs_pow]
  · exact ae_of_all _ fun ω => pow_two_nonneg _

theorem _root_.MeasureTheory.Memℒp.variance_eq [IsFiniteMeasure μ] (hX : Memℒp X 2 μ) :
    variance X μ = μ[(X - fun _ => μ[X] :) ^ (2 : Nat)] := by
  rw [variance, evariance_eq_lintegral_ofReal, ← ofReal_integral_eq_lintegral_ofReal,
    ENNReal.toReal_ofReal (by positivity)]
  · rfl
  · convert (hX.sub <| memℒp_const μ[X]).integrable_norm_rpow two_ne_zero ENNReal.two_ne_top
      with ω
    simp only [Pi.sub_apply, Real.norm_eq_abs, ENNReal.toReal_ofNat, ENNReal.one_toReal,
      Real.rpow_two, sq_abs, abs_pow]
  · exact ae_of_all _ fun ω => pow_two_nonneg _

@[simp]
theorem evariance_zero : evariance 0 μ = 0 := by simp [evariance]

theorem evariance_eq_zero_iff (hX : AEMeasurable X μ) :
    evariance X μ = 0 ↔ X =ᵐ[μ] fun _ => μ[X] := by
  rw [evariance, lintegral_eq_zero_iff']
  constructor <;> intro hX <;> filter_upwards [hX] with ω hω
  · simpa only [Pi.zero_apply, sq_eq_zero_iff, ENNReal.coe_eq_zero, nnnorm_eq_zero, sub_eq_zero]
      using hω
  · rw [hω]
    simp
  · exact (hX.sub_const _).ennnorm.pow_const _ -- TODO `measurability` and `fun_prop` fail

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

scoped notation "eVar[" X "]" => ProbabilityTheory.evariance X MeasureTheory.MeasureSpace.volume

@[simp]
theorem variance_zero (μ : Measure Ω) : variance 0 μ = 0 := by
  simp only [variance, evariance_zero, ENNReal.zero_toReal]

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

scoped notation "Var[" X "]" => ProbabilityTheory.variance X MeasureTheory.MeasureSpace.volume

theorem variance_def' [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Memℒp X 2 μ) :
    variance X μ = μ[X ^ 2] - μ[X] ^ 2 := by
  rw [hX.variance_eq, sub_sq', integral_sub', integral_add']; rotate_left
  · exact hX.integrable_sq
  · apply integrable_const
  · apply hX.integrable_sq.add
    apply integrable_const
  · exact ((hX.integrable one_le_two).const_mul 2).mul_const' _
  simp only [Pi.pow_apply, integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul,
    Pi.mul_apply, Pi.ofNat_apply, Nat.cast_ofNat, integral_mul_right, integral_mul_left]
  ring

theorem variance_le_expectation_sq [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hm : AEStronglyMeasurable X μ) : variance X μ ≤ μ[X ^ 2] := by
  by_cases hX : Memℒp X 2 μ
  · rw [variance_def' hX]
    simp only [sq_nonneg, sub_le_self_iff]
  rw [variance, evariance_eq_lintegral_ofReal, ← integral_eq_lintegral_of_nonneg_ae]
  · by_cases hint : Integrable X μ; swap
    · simp only [integral_undef hint, Pi.pow_apply, Pi.sub_apply, sub_zero]
      exact le_rfl
    · rw [integral_undef]
      · exact integral_nonneg fun a => sq_nonneg _
      intro h
      have A : Memℒp (X - fun ω : Ω => μ[X]) 2 μ :=
        (memℒp_two_iff_integrable_sq (hint.aestronglyMeasurable.sub aestronglyMeasurable_const)).2 h
      have B : Memℒp (fun _ : Ω => μ[X]) 2 μ := memℒp_const _
      apply hX
      convert A.add B
      simp
  · exact Eventually.of_forall fun x => sq_nonneg _
  · exact (AEMeasurable.pow_const (hm.aemeasurable.sub_const _) _).aestronglyMeasurable

theorem evariance_def' [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) :
    evariance X μ = (∫⁻ ω, (‖X ω‖₊ ^ 2 :) ∂μ) - ENNReal.ofReal (μ[X] ^ 2) := by
  by_cases hℒ : Memℒp X 2 μ
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
    simp only [eLpNorm_eq_lintegral_rpow_nnnorm two_ne_zero ENNReal.two_ne_top, not_lt, top_le_iff,
      ENNReal.toReal_ofNat, one_div, ENNReal.rpow_eq_top_iff, inv_lt_zero, inv_pos, and_true,
      or_iff_not_imp_left, not_and_or, zero_lt_two] at hℒ
    exact mod_cast hℒ fun _ => zero_le_two

/-- **Chebyshev's inequality** for `ℝ≥0∞`-valued variance. -/
theorem meas_ge_le_evariance_div_sq {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) {c : ℝ≥0}
    (hc : c ≠ 0) : μ {ω | ↑c ≤ |X ω - μ[X]|} ≤ evariance X μ / c ^ 2 := by
  have A : (c : ℝ≥0∞) ≠ 0 := by rwa [Ne, ENNReal.coe_eq_zero]
  have B : AEStronglyMeasurable (fun _ : Ω => μ[X]) μ := aestronglyMeasurable_const
  convert meas_ge_le_mul_pow_eLpNorm μ two_ne_zero ENNReal.two_ne_top (hX.sub B) A using 1
  · congr
    simp only [Pi.sub_apply, ENNReal.coe_le_coe, ← Real.norm_eq_abs, ← coe_nnnorm,
      NNReal.coe_le_coe, ENNReal.ofReal_coe_nnreal]
  · rw [eLpNorm_eq_lintegral_rpow_nnnorm two_ne_zero ENNReal.two_ne_top]
    simp only [show ENNReal.ofNNReal (c ^ 2) = (ENNReal.ofNNReal c) ^ 2 by norm_cast,
      ENNReal.toReal_ofNat, one_div, Pi.sub_apply]
    rw [div_eq_mul_inv, ENNReal.inv_pow, mul_comm, ENNReal.rpow_two]
    congr
    simp_rw [← ENNReal.rpow_mul, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), ENNReal.rpow_two,
      ENNReal.rpow_one, evariance]

/-- **Chebyshev's inequality**: one can control the deviation probability of a real random variable
from its expectation in terms of the variance. -/
theorem meas_ge_le_variance_div_sq [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Memℒp X 2 μ) {c : ℝ}
    (hc : 0 < c) : μ {ω | c ≤ |X ω - μ[X]|} ≤ ENNReal.ofReal (variance X μ / c ^ 2) := by
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_ne_zero hc.ne.symm), hX.ofReal_variance_eq]
  convert @meas_ge_le_evariance_div_sq _ _ _ _ hX.1 c.toNNReal (by simp [hc]) using 1
  · simp only [Real.coe_toNNReal', max_le_iff, abs_nonneg, and_true]
  · rw [ENNReal.ofReal_pow hc.le]
    rfl

-- Porting note: supplied `MeasurableSpace Ω` argument of `h` by unification
/-- The variance of the sum of two independent random variables is the sum of the variances. -/
theorem IndepFun.variance_add [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hX : Memℒp X 2 μ)
    (hY : Memℒp Y 2 μ) (h : IndepFun X Y μ) : variance (X + Y) μ = variance X μ + variance Y μ :=
  calc
    variance (X + Y) μ = μ[fun a => X a ^ 2 + Y a ^ 2 + 2 * X a * Y a] - μ[X + Y] ^ 2 := by
      simp [variance_def' (hX.add hY), add_sq']
    _ = μ[X ^ 2] + μ[Y ^ 2] + (2 : ℝ) * μ[X * Y] - (μ[X] + μ[Y]) ^ 2 := by
      simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply, mul_assoc]
      rw [integral_add, integral_add, integral_add, integral_mul_left]
      · exact hX.integrable one_le_two
      · exact hY.integrable one_le_two
      · exact hX.integrable_sq
      · exact hY.integrable_sq
      · exact hX.integrable_sq.add hY.integrable_sq
      · apply Integrable.const_mul
        exact h.integrable_mul (hX.integrable one_le_two) (hY.integrable one_le_two)
    _ = μ[X ^ 2] + μ[Y ^ 2] + 2 * (μ[X] * μ[Y]) - (μ[X] + μ[Y]) ^ 2 := by
      congr
      exact h.integral_mul_of_integrable (hX.integrable one_le_two) (hY.integrable one_le_two)
    _ = variance X μ + variance Y μ := by simp only [variance_def', hX, hY, Pi.pow_apply]; ring

-- Porting note: supplied `MeasurableSpace Ω` argument of `hs`, `h` by unification
/-- The variance of a finite sum of pairwise independent random variables is the sum of the
variances. -/
theorem IndepFun.variance_sum [IsProbabilityMeasure μ] {ι : Type*} {X : ι → Ω → ℝ}
    {s : Finset ι} (hs : ∀ i ∈ s, Memℒp (X i) 2 μ)
    (h : Set.Pairwise ↑s fun i j => IndepFun (X i) (X j) μ) :
    variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, variance (X i) μ := by
  classical
  induction' s using Finset.induction_on with k s ks IH
  · simp only [Finset.sum_empty, variance_zero]
  rw [variance_def' (memℒp_finset_sum' _ hs), sum_insert ks, sum_insert ks]
  simp only [add_sq']
  calc
    μ[(X k ^ 2 + (∑ i ∈ s, X i) ^ 2 + 2 * X k * ∑ i ∈ s, X i : Ω → ℝ)] - μ[X k + ∑ i ∈ s, X i] ^ 2 =
        μ[X k ^ 2] + μ[(∑ i ∈ s, X i) ^ 2] + μ[2 * X k * ∑ i ∈ s, X i] -
          (μ[X k] + μ[∑ i ∈ s, X i]) ^ 2 := by
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
        rw [mul_sum, sum_fn]
        apply integrable_finset_sum _ fun i hi => ?_
        apply IndepFun.integrable_mul _ (Memℒp.integrable one_le_two (hs _ (mem_insert_self _ _)))
          (Memℒp.integrable one_le_two (hs _ (mem_insert_of_mem hi)))
        apply h (mem_insert_self _ _) (mem_insert_of_mem hi)
        exact fun hki => ks (hki.symm ▸ hi)
    _ = variance (X k) μ + variance (∑ i ∈ s, X i) μ +
        (μ[2 * X k * ∑ i ∈ s, X i] - 2 * μ[X k] * μ[∑ i ∈ s, X i]) := by
      rw [variance_def' (hs _ (mem_insert_self _ _)),
        variance_def' (memℒp_finset_sum' _ fun i hi => hs _ (mem_insert_of_mem hi))]
      ring
    _ = variance (X k) μ + variance (∑ i ∈ s, X i) μ := by
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
    _ = variance (X k) μ + ∑ i ∈ s, variance (X i) μ := by
      rw [IH (fun i hi => hs i (mem_insert_of_mem hi))
          (h.mono (by simp only [coe_insert, Set.subset_insert]))]

/-- **The Bhatia-Davis inequality on variance**

The variance of a random variable `X` satisfying `a ≤ X ≤ b` almost everywhere is at most
`(b - 𝔼 X) * (𝔼 X - a)`. -/
lemma variance_le_sub_mul_sub [IsProbabilityMeasure μ] {a b : ℝ} {X : Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hX : AEMeasurable X μ) :
    variance X μ ≤ (b - μ[X]) * (μ[X] - a) := by
  have ha : ∀ᵐ ω ∂μ, a ≤ X ω := h.mono fun ω h => h.1
  have hb : ∀ᵐ ω ∂μ, X ω ≤ b := h.mono fun ω h => h.2
  have hX_int₂ : Integrable (fun ω ↦ -X ω ^ 2) μ :=
    (memℒp_of_bounded h hX.aestronglyMeasurable 2).integrable_sq.neg
  have hX_int₁ : Integrable (fun ω ↦ (a + b) * X ω) μ :=
    ((integrable_const (max |a| |b|)).mono' hX.aestronglyMeasurable
      (by filter_upwards [ha, hb] with ω using abs_le_max_abs_abs)).const_mul (a + b)
  have h0 : 0 ≤ - μ[X ^ 2] + (a + b) * μ[X] - a * b :=
    calc
      _ ≤ ∫ ω, (b - X ω) * (X ω - a) ∂μ := by
        apply integral_nonneg_of_ae
        filter_upwards [ha, hb] with ω ha' hb'
        exact mul_nonneg (by linarith : 0 ≤ b - X ω) (by linarith : 0 ≤ X ω - a)
      _ = ∫ ω, - X ω ^ 2 + (a + b) * X ω - a * b ∂μ :=
        integral_congr_ae <| ae_of_all μ fun ω ↦ by ring
      _ = ∫ ω, - X ω ^ 2 + (a + b) * X ω ∂μ - ∫ _, a * b ∂μ :=
        integral_sub (hX_int₂.add hX_int₁) (integrable_const (a * b))
      _ = ∫ ω, - X ω ^ 2 + (a + b) * X ω ∂μ - a * b := by simp
      _ = - μ[X ^ 2] + (a + b) * μ[X] - a * b := by
        simp [← integral_neg, ← integral_mul_left, integral_add hX_int₂ hX_int₁]
  calc
    _ ≤ (a + b) * μ[X] - a * b - μ[X] ^ 2 := by
      rw [variance_def' (memℒp_of_bounded h hX.aestronglyMeasurable 2)]
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

end ProbabilityTheory
