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

open scoped BigOperators MeasureTheory ProbabilityTheory ENNReal NNReal

namespace ProbabilityTheory

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

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
  -- ⊢ evariance X μ < ⊤
  rw [snorm_eq_lintegral_rpow_nnnorm two_ne_zero ENNReal.two_ne_top, ← ENNReal.rpow_two] at this
  -- ⊢ evariance X μ < ⊤
  simp only [coe_two, Pi.sub_apply, ENNReal.one_toReal, one_div] at this
  -- ⊢ evariance X μ < ⊤
  rw [← ENNReal.rpow_mul, inv_mul_cancel (two_ne_zero : (2 : ℝ) ≠ 0), ENNReal.rpow_one] at this
  -- ⊢ evariance X μ < ⊤
  simp_rw [ENNReal.rpow_two] at this
  -- ⊢ evariance X μ < ⊤
  exact this
  -- 🎉 no goals
#align measure_theory.mem_ℒp.evariance_lt_top MeasureTheory.Memℒp.evariance_lt_top

theorem evariance_eq_top [IsFiniteMeasure μ] (hXm : AEStronglyMeasurable X μ) (hX : ¬Memℒp X 2 μ) :
    evariance X μ = ∞ := by
  by_contra h
  -- ⊢ False
  rw [← Ne.def, ← lt_top_iff_ne_top] at h
  -- ⊢ False
  have : Memℒp (fun ω => X ω - μ[X]) 2 μ := by
    refine' ⟨hXm.sub aestronglyMeasurable_const, _⟩
    rw [snorm_eq_lintegral_rpow_nnnorm two_ne_zero ENNReal.two_ne_top]
    simp only [coe_two, ENNReal.one_toReal, ENNReal.rpow_two, Ne.def]
    exact ENNReal.rpow_lt_top_of_nonneg (by linarith) h.ne
  refine' hX _
  -- ⊢ Memℒp X 2
  -- Porting note: `μ[X]` without whitespace is ambiguous as it could be GetElem,
  -- and `convert` cannot disambiguate based on typeclass inference failure.
  convert this.add (memℒp_const <| μ [X])
  -- ⊢ X = (fun ω => X ω - ∫ (x : Ω), X x ∂μ) + fun x => ∫ (x : Ω), X x ∂μ
  ext ω
  -- ⊢ X ω = ((fun ω => X ω - ∫ (x : Ω), X x ∂μ) + fun x => ∫ (x : Ω), X x ∂μ) ω
  rw [Pi.add_apply, sub_add_cancel]
  -- 🎉 no goals
#align probability_theory.evariance_eq_top ProbabilityTheory.evariance_eq_top

theorem evariance_lt_top_iff_memℒp [IsFiniteMeasure μ] (hX : AEStronglyMeasurable X μ) :
    evariance X μ < ∞ ↔ Memℒp X 2 μ := by
  refine' ⟨_, MeasureTheory.Memℒp.evariance_lt_top⟩
  -- ⊢ evariance X μ < ⊤ → Memℒp X 2
  contrapose
  -- ⊢ ¬Memℒp X 2 → ¬evariance X μ < ⊤
  rw [not_lt, top_le_iff]
  -- ⊢ ¬Memℒp X 2 → evariance X μ = ⊤
  exact evariance_eq_top hX
  -- 🎉 no goals
#align probability_theory.evariance_lt_top_iff_mem_ℒp ProbabilityTheory.evariance_lt_top_iff_memℒp

theorem _root_.MeasureTheory.Memℒp.ofReal_variance_eq [IsFiniteMeasure μ] (hX : Memℒp X 2 μ) :
    ENNReal.ofReal (variance X μ) = evariance X μ := by
  rw [variance, ENNReal.ofReal_toReal]
  -- ⊢ evariance X μ ≠ ⊤
  exact hX.evariance_lt_top.ne
  -- 🎉 no goals
#align measure_theory.mem_ℒp.of_real_variance_eq MeasureTheory.Memℒp.ofReal_variance_eq

theorem evariance_eq_lintegral_ofReal (X : Ω → ℝ) (μ : Measure Ω) :
    evariance X μ = ∫⁻ ω, ENNReal.ofReal ((X ω - μ[X]) ^ 2) ∂μ := by
  rw [evariance]
  -- ⊢ ∫⁻ (ω : Ω), ↑‖X ω - ∫ (x : Ω), X x ∂μ‖₊ ^ 2 ∂μ = ∫⁻ (ω : Ω), ENNReal.ofReal  …
  congr
  -- ⊢ (fun ω => ↑‖X ω - ∫ (x : Ω), X x ∂μ‖₊ ^ 2) = fun ω => ENNReal.ofReal ((X ω - …
  ext1 ω
  -- ⊢ ↑‖X ω - ∫ (x : Ω), X x ∂μ‖₊ ^ 2 = ENNReal.ofReal ((X ω - ∫ (x : Ω), X x ∂μ)  …
  rw [pow_two, ← ENNReal.coe_mul, ← nnnorm_mul, ← pow_two]
  -- ⊢ ↑‖(X ω - ∫ (x : Ω), X x ∂μ) ^ 2‖₊ = ENNReal.ofReal ((X ω - ∫ (x : Ω), X x ∂μ …
  congr
  -- ⊢ ‖(X ω - ∫ (x : Ω), X x ∂μ) ^ 2‖₊ = Real.toNNReal ((X ω - ∫ (x : Ω), X x ∂μ)  …
  exact (Real.toNNReal_eq_nnnorm_of_nonneg <| sq_nonneg _).symm
  -- 🎉 no goals
#align probability_theory.evariance_eq_lintegral_of_real ProbabilityTheory.evariance_eq_lintegral_ofReal

theorem _root_.MeasureTheory.Memℒp.variance_eq_of_integral_eq_zero (hX : Memℒp X 2 μ)
    (hXint : μ[X] = 0) : variance X μ = μ[X ^ 2] := by
  rw [variance, evariance_eq_lintegral_ofReal, ← ofReal_integral_eq_lintegral_ofReal,
      ENNReal.toReal_ofReal] <;>
    simp_rw [hXint, sub_zero]
    -- ⊢ ∫ (x : Ω), X x ^ 2 ∂μ = ∫ (x : Ω), (X ^ 2) x ∂μ
    -- ⊢ 0 ≤ ∫ (x : Ω), X x ^ 2 ∂μ
    -- ⊢ Integrable fun ω => X ω ^ 2
    -- ⊢ 0 ≤ᵐ[μ] fun ω => X ω ^ 2
  · rfl
    -- 🎉 no goals
  · exact integral_nonneg fun ω => pow_two_nonneg _
    -- 🎉 no goals
  · convert hX.integrable_norm_rpow two_ne_zero ENNReal.two_ne_top with ω
    -- ⊢ X ω ^ 2 = ‖X ω‖ ^ ENNReal.toReal 2
    simp only [Pi.sub_apply, Real.norm_eq_abs, coe_two, ENNReal.one_toReal,
      Real.rpow_two, sq_abs, abs_pow]
  · exact ae_of_all _ fun ω => pow_two_nonneg _
    -- 🎉 no goals
#align measure_theory.mem_ℒp.variance_eq_of_integral_eq_zero MeasureTheory.Memℒp.variance_eq_of_integral_eq_zero

theorem _root_.MeasureTheory.Memℒp.variance_eq [IsFiniteMeasure μ] (hX : Memℒp X 2 μ) :
    variance X μ = μ[(X - fun _ => μ[X]) ^ 2] := by
  rw [variance, evariance_eq_lintegral_ofReal, ← ofReal_integral_eq_lintegral_ofReal,
    ENNReal.toReal_ofReal]
  · rfl
    -- 🎉 no goals
  · exact integral_nonneg fun ω => pow_two_nonneg _
    -- 🎉 no goals
  · -- Porting note: `μ[X]` without whitespace is ambiguous as it could be GetElem,
    -- and `convert` cannot disambiguate based on typeclass inference failure.
    convert (hX.sub <| memℒp_const (μ [X])).integrable_norm_rpow two_ne_zero ENNReal.two_ne_top
      with ω
    simp only [Pi.sub_apply, Real.norm_eq_abs, coe_two, ENNReal.one_toReal,
      Real.rpow_two, sq_abs, abs_pow]
  · exact ae_of_all _ fun ω => pow_two_nonneg _
    -- 🎉 no goals
#align measure_theory.mem_ℒp.variance_eq MeasureTheory.Memℒp.variance_eq

@[simp]
theorem evariance_zero : evariance 0 μ = 0 := by simp [evariance]
                                                 -- 🎉 no goals
#align probability_theory.evariance_zero ProbabilityTheory.evariance_zero

theorem evariance_eq_zero_iff (hX : AEMeasurable X μ) :
    evariance X μ = 0 ↔ X =ᵐ[μ] fun _ => μ[X] := by
  rw [evariance, lintegral_eq_zero_iff']
  -- ⊢ (fun ω => ↑‖X ω - ∫ (x : Ω), X x ∂μ‖₊ ^ 2) =ᵐ[μ] 0 ↔ X =ᵐ[μ] fun x => ∫ (x : …
  constructor <;> intro hX <;> filter_upwards [hX] with ω hω
  -- ⊢ (fun ω => ↑‖X ω - ∫ (x : Ω), X x ∂μ‖₊ ^ 2) =ᵐ[μ] 0 → X =ᵐ[μ] fun x => ∫ (x : …
                  -- ⊢ X =ᵐ[μ] fun x => ∫ (x : Ω), X x ∂μ
                  -- ⊢ (fun ω => ↑‖X ω - ∫ (x : Ω), X x ∂μ‖₊ ^ 2) =ᵐ[μ] 0
                               -- ⊢ X ω = ∫ (x : Ω), X x ∂μ
                               -- ⊢ ↑‖X ω - ∫ (x : Ω), X x ∂μ‖₊ ^ 2 = OfNat.ofNat 0 ω
  · simp only [Pi.zero_apply, pow_eq_zero_iff, Nat.succ_pos', ENNReal.coe_eq_zero, nnnorm_eq_zero,
      sub_eq_zero] at hω
    exact hω
    -- 🎉 no goals
  · rw [hω]
    -- ⊢ ↑‖∫ (x : Ω), X x ∂μ - ∫ (x : Ω), X x ∂μ‖₊ ^ 2 = OfNat.ofNat 0 ω
    simp
    -- 🎉 no goals
  · measurability
    -- 🎉 no goals
#align probability_theory.evariance_eq_zero_iff ProbabilityTheory.evariance_eq_zero_iff

theorem evariance_mul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    evariance (fun ω => c * X ω) μ = ENNReal.ofReal (c ^ 2) * evariance X μ := by
  rw [evariance, evariance, ← lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
  -- ⊢ ∫⁻ (ω : Ω), ↑‖c * X ω - ∫ (x : Ω), c * X x ∂μ‖₊ ^ 2 ∂μ = ∫⁻ (a : Ω), ENNReal …
  congr
  -- ⊢ (fun ω => ↑‖c * X ω - ∫ (x : Ω), c * X x ∂μ‖₊ ^ 2) = fun a => ENNReal.ofReal …
  ext1 ω
  -- ⊢ ↑‖c * X ω - ∫ (x : Ω), c * X x ∂μ‖₊ ^ 2 = ENNReal.ofReal (c ^ 2) * ↑‖X ω - ∫ …
  rw [ENNReal.ofReal, ← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_mul]
  -- ⊢ ↑(‖c * X ω - ∫ (x : Ω), c * X x ∂μ‖₊ ^ 2) = ↑(Real.toNNReal (c ^ 2) * ‖X ω - …
  congr
  -- ⊢ ‖c * X ω - ∫ (x : Ω), c * X x ∂μ‖₊ ^ 2 = Real.toNNReal (c ^ 2) * ‖X ω - ∫ (x …
  rw [← sq_abs, ← Real.rpow_two, Real.toNNReal_rpow_of_nonneg (abs_nonneg _), NNReal.rpow_two,
    ← mul_pow, Real.toNNReal_mul_nnnorm _ (abs_nonneg _)]
  conv_rhs => rw [← nnnorm_norm, norm_mul, norm_abs_eq_norm, ← norm_mul, nnnorm_norm, mul_sub]
  -- ⊢ ‖c * X ω - ∫ (x : Ω), c * X x ∂μ‖₊ ^ 2 = ‖c * X ω - c * ∫ (x : Ω), X x ∂μ‖₊  …
  congr
  -- ⊢ ∫ (x : Ω), c * X x ∂μ = c * ∫ (x : Ω), X x ∂μ
  rw [mul_comm]
  -- ⊢ ∫ (x : Ω), c * X x ∂μ = (∫ (x : Ω), X x ∂μ) * c
  simp_rw [← smul_eq_mul, ← integral_smul_const, smul_eq_mul, mul_comm]
  -- 🎉 no goals
#align probability_theory.evariance_mul ProbabilityTheory.evariance_mul

scoped notation "eVar[" X "]" => ProbabilityTheory.evariance X MeasureTheory.MeasureSpace.volume

@[simp]
theorem variance_zero (μ : Measure Ω) : variance 0 μ = 0 := by
  simp only [variance, evariance_zero, ENNReal.zero_toReal]
  -- 🎉 no goals
#align probability_theory.variance_zero ProbabilityTheory.variance_zero

theorem variance_nonneg (X : Ω → ℝ) (μ : Measure Ω) : 0 ≤ variance X μ :=
  ENNReal.toReal_nonneg
#align probability_theory.variance_nonneg ProbabilityTheory.variance_nonneg

theorem variance_mul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    variance (fun ω => c * X ω) μ = c ^ 2 * variance X μ := by
  rw [variance, evariance_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
  -- ⊢ c ^ 2 * ENNReal.toReal (evariance (fun ω => X ω) μ) = c ^ 2 * variance X μ
  rfl
  -- 🎉 no goals
#align probability_theory.variance_mul ProbabilityTheory.variance_mul

theorem variance_smul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) :
    variance (c • X) μ = c ^ 2 * variance X μ :=
  variance_mul c X μ
#align probability_theory.variance_smul ProbabilityTheory.variance_smul

theorem variance_smul' {A : Type*} [CommSemiring A] [Algebra A ℝ] (c : A) (X : Ω → ℝ)
    (μ : Measure Ω) : variance (c • X) μ = c ^ 2 • variance X μ := by
  convert variance_smul (algebraMap A ℝ c) X μ using 1
  -- ⊢ variance (c • X) μ = variance (↑(algebraMap A ℝ) c • X) μ
  · congr; simp only [algebraMap_smul]
    -- ⊢ c • X = ↑(algebraMap A ℝ) c • X
           -- 🎉 no goals
  · simp only [Algebra.smul_def, map_pow]
    -- 🎉 no goals
#align probability_theory.variance_smul' ProbabilityTheory.variance_smul'

scoped notation "Var[" X "]" => ProbabilityTheory.variance X MeasureTheory.MeasureSpace.volume

variable [MeasureSpace Ω]

theorem variance_def' [@IsProbabilityMeasure Ω _ ℙ] {X : Ω → ℝ} (hX : Memℒp X 2) :
    Var[X] = 𝔼[X ^ 2] - 𝔼[X] ^ 2 := by
  rw [hX.variance_eq, sub_sq', integral_sub', integral_add']; rotate_left
  · exact hX.integrable_sq
    -- 🎉 no goals
  · convert @integrable_const Ω ℝ (_) ℙ _ _ (𝔼[X] ^ 2)
    -- 🎉 no goals
  · apply hX.integrable_sq.add
    -- ⊢ Integrable ((fun x => ∫ (x : Ω), X x) ^ 2)
    convert @integrable_const Ω ℝ (_) ℙ _ _ (𝔼[X] ^ 2)
    -- 🎉 no goals
  · exact ((hX.integrable one_le_two).const_mul 2).mul_const' _
    -- 🎉 no goals
  simp [integral_mul_right, integral_mul_left]
  -- ⊢ (∫ (a : Ω), X a ^ 2) + (∫ (x : Ω), X x) ^ 2 - (2 * ∫ (x : Ω), X x) * ∫ (x :  …
  ring
  -- 🎉 no goals
#align probability_theory.variance_def' ProbabilityTheory.variance_def'

theorem variance_le_expectation_sq [@IsProbabilityMeasure Ω _ ℙ] {X : Ω → ℝ}
    (hm : AEStronglyMeasurable X ℙ) : Var[X] ≤ 𝔼[X ^ 2] := by
  by_cases hX : Memℒp X 2
  -- ⊢ variance X ℙ ≤ ∫ (a : Ω), (X ^ 2) a
  · rw [variance_def' hX]
    -- ⊢ (∫ (a : Ω), (X ^ 2) a) - (∫ (a : Ω), X a) ^ 2 ≤ ∫ (a : Ω), (X ^ 2) a
    simp only [sq_nonneg, sub_le_self_iff]
    -- 🎉 no goals
  rw [variance, evariance_eq_lintegral_ofReal, ← integral_eq_lintegral_of_nonneg_ae]
  by_cases hint : Integrable X; swap
  · simp only [integral_undef hint, Pi.pow_apply, Pi.sub_apply, sub_zero]
    -- ⊢ ∫ (a : Ω), X a ^ 2 ≤ ∫ (a : Ω), X a ^ 2
    exact le_rfl
    -- 🎉 no goals
  · rw [integral_undef]
    -- ⊢ 0 ≤ ∫ (a : Ω), (X ^ 2) a
    · exact integral_nonneg fun a => sq_nonneg _
      -- 🎉 no goals
    · intro h
      -- ⊢ False
      have A : Memℒp (X - fun ω : Ω => 𝔼[X]) 2 ℙ :=
        (memℒp_two_iff_integrable_sq (hint.aestronglyMeasurable.sub aestronglyMeasurable_const)).2 h
      have B : Memℒp (fun _ : Ω => 𝔼[X]) 2 ℙ := memℒp_const _
      -- ⊢ False
      apply hX
      -- ⊢ Memℒp X 2
      convert A.add B
      -- ⊢ X = (X - fun ω => ∫ (a : Ω), X a) + fun x => ∫ (a : Ω), X a
      simp
      -- 🎉 no goals
  · exact @ae_of_all _ (_) _ _ fun x => sq_nonneg _
    -- 🎉 no goals
  · exact (AEMeasurable.pow_const (hm.aemeasurable.sub_const _) _).aestronglyMeasurable
    -- 🎉 no goals
#align probability_theory.variance_le_expectation_sq ProbabilityTheory.variance_le_expectation_sq

theorem evariance_def' [@IsProbabilityMeasure Ω _ ℙ] {X : Ω → ℝ} (hX : AEStronglyMeasurable X ℙ) :
    eVar[X] = (∫⁻ ω, ‖X ω‖₊ ^ 2) - ENNReal.ofReal (𝔼[X] ^ 2) := by
  by_cases hℒ : Memℒp X 2
  -- ⊢ evariance X ℙ = (∫⁻ (ω : Ω), ↑(‖X ω‖₊ ^ 2)) - ENNReal.ofReal ((∫ (a : Ω), X  …
  · rw [← hℒ.ofReal_variance_eq, variance_def' hℒ, ENNReal.ofReal_sub _ (sq_nonneg _)]
    -- ⊢ ENNReal.ofReal (∫ (a : Ω), (X ^ 2) a) - ENNReal.ofReal ((∫ (a : Ω), X a) ^ 2 …
    congr
    -- ⊢ ENNReal.ofReal (∫ (a : Ω), (X ^ 2) a) = ∫⁻ (ω : Ω), ↑(‖X ω‖₊ ^ 2)
    rw [lintegral_coe_eq_integral]
    -- ⊢ ENNReal.ofReal (∫ (a : Ω), (X ^ 2) a) = ENNReal.ofReal (∫ (a : Ω), ↑(‖X a‖₊  …
    · congr 2 with ω
      -- ⊢ (X ^ 2) ω = ↑(‖X ω‖₊ ^ 2)
      simp only [Pi.pow_apply, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, Even.pow_abs even_two]
      -- 🎉 no goals
    · exact hℒ.abs.integrable_sq
      -- 🎉 no goals
  · symm
    -- ⊢ (∫⁻ (ω : Ω), ↑(‖X ω‖₊ ^ 2)) - ENNReal.ofReal ((∫ (a : Ω), X a) ^ 2) = evaria …
    rw [evariance_eq_top hX hℒ, ENNReal.sub_eq_top_iff]
    -- ⊢ ∫⁻ (ω : Ω), ↑(‖X ω‖₊ ^ 2) = ⊤ ∧ ENNReal.ofReal ((∫ (a : Ω), X a) ^ 2) ≠ ⊤
    refine' ⟨_, ENNReal.ofReal_ne_top⟩
    -- ⊢ ∫⁻ (ω : Ω), ↑(‖X ω‖₊ ^ 2) = ⊤
    rw [Memℒp, not_and] at hℒ
    -- ⊢ ∫⁻ (ω : Ω), ↑(‖X ω‖₊ ^ 2) = ⊤
    specialize hℒ hX
    -- ⊢ ∫⁻ (ω : Ω), ↑(‖X ω‖₊ ^ 2) = ⊤
    simp only [snorm_eq_lintegral_rpow_nnnorm two_ne_zero ENNReal.two_ne_top, not_lt, top_le_iff,
      coe_two, one_div, ENNReal.rpow_eq_top_iff, inv_lt_zero, inv_pos, and_true_iff,
      or_iff_not_imp_left, not_and_or, zero_lt_two] at hℒ
    exact_mod_cast hℒ fun _ => zero_le_two
    -- 🎉 no goals
#align probability_theory.evariance_def' ProbabilityTheory.evariance_def'

/-- *Chebyshev's inequality* for `ℝ≥0∞`-valued variance. -/
theorem meas_ge_le_evariance_div_sq {X : Ω → ℝ} (hX : AEStronglyMeasurable X ℙ) {c : ℝ≥0}
    (hc : c ≠ 0) : ℙ {ω | ↑c ≤ |X ω - 𝔼[X]|} ≤ eVar[X] / c ^ 2 := by
  have A : (c : ℝ≥0∞) ≠ 0 := by rwa [Ne.def, ENNReal.coe_eq_zero]
  -- ⊢ ↑↑ℙ {ω | ↑c ≤ |X ω - ∫ (a : Ω), X a|} ≤ evariance X ℙ / ↑(c ^ 2)
  have B : AEStronglyMeasurable (fun _ : Ω => 𝔼[X]) ℙ := aestronglyMeasurable_const
  -- ⊢ ↑↑ℙ {ω | ↑c ≤ |X ω - ∫ (a : Ω), X a|} ≤ evariance X ℙ / ↑(c ^ 2)
  convert meas_ge_le_mul_pow_snorm ℙ two_ne_zero ENNReal.two_ne_top (hX.sub B) A using 1
  -- ⊢ ↑↑ℙ {ω | ↑c ≤ |X ω - ∫ (a : Ω), X a|} = ↑↑ℙ {x | ↑c ≤ ↑‖(X - fun x => ∫ (a : …
  · congr
    -- ⊢ {ω | ↑c ≤ |X ω - ∫ (a : Ω), X a|} = {x | ↑c ≤ ↑‖(X - fun x => ∫ (a : Ω), X a …
    simp only [Pi.sub_apply, ENNReal.coe_le_coe, ← Real.norm_eq_abs, ← coe_nnnorm,
      NNReal.coe_le_coe, ENNReal.ofReal_coe_nnreal]
  · rw [snorm_eq_lintegral_rpow_nnnorm two_ne_zero ENNReal.two_ne_top]
    -- ⊢ evariance X ℙ / ↑(c ^ 2) = (↑c)⁻¹ ^ ENNReal.toReal 2 * ((∫⁻ (x : Ω), ↑‖(X -  …
    simp only [show ENNReal.some (c ^ 2) = (ENNReal.some c) ^ 2 by norm_cast, coe_two, one_div,
      Pi.sub_apply]
    rw [div_eq_mul_inv, ENNReal.inv_pow, mul_comm, ENNReal.rpow_two]
    -- ⊢ (↑c)⁻¹ ^ 2 * evariance X ℙ = (↑c)⁻¹ ^ 2 * ((∫⁻ (x : Ω), ↑‖X x - ∫ (a : Ω), X …
    congr
    -- ⊢ evariance X ℙ = ((∫⁻ (x : Ω), ↑‖X x - ∫ (a : Ω), X a‖₊ ^ 2) ^ 2⁻¹) ^ 2
    simp_rw [← ENNReal.rpow_mul, inv_mul_cancel (two_ne_zero : (2 : ℝ) ≠ 0), ENNReal.rpow_two,
      ENNReal.rpow_one, evariance]
#align probability_theory.meas_ge_le_evariance_div_sq ProbabilityTheory.meas_ge_le_evariance_div_sq

/-- *Chebyshev's inequality* : one can control the deviation probability of a real random variable
from its expectation in terms of the variance. -/
theorem meas_ge_le_variance_div_sq [@IsFiniteMeasure Ω _ ℙ] {X : Ω → ℝ} (hX : Memℒp X 2) {c : ℝ}
    (hc : 0 < c) : ℙ {ω | c ≤ |X ω - 𝔼[X]|} ≤ ENNReal.ofReal (Var[X] / c ^ 2) := by
  rw [ENNReal.ofReal_div_of_pos (sq_pos_of_ne_zero _ hc.ne.symm), hX.ofReal_variance_eq]
  -- ⊢ ↑↑ℙ {ω | c ≤ |X ω - ∫ (a : Ω), X a|} ≤ evariance X ℙ / ENNReal.ofReal (c ^ 2)
  convert @meas_ge_le_evariance_div_sq _ _ _ hX.1 c.toNNReal (by simp [hc]) using 1
  -- ⊢ ↑↑ℙ {ω | c ≤ |X ω - ∫ (a : Ω), X a|} = ↑↑ℙ {ω | ↑(Real.toNNReal c) ≤ |X ω -  …
  · simp only [Real.coe_toNNReal', max_le_iff, abs_nonneg, and_true_iff]
    -- 🎉 no goals
  · rw [ENNReal.ofReal_pow hc.le, ENNReal.coe_pow]
    -- ⊢ evariance X ℙ / ENNReal.ofReal c ^ 2 = evariance X ℙ / ↑(Real.toNNReal c) ^ 2
    rfl
    -- 🎉 no goals
#align probability_theory.meas_ge_le_variance_div_sq ProbabilityTheory.meas_ge_le_variance_div_sq

-- Porting note: supplied `MeasurableSpace Ω` argument of `h` by unification
/-- The variance of the sum of two independent random variables is the sum of the variances. -/
theorem IndepFun.variance_add [@IsProbabilityMeasure Ω _ ℙ] {X Y : Ω → ℝ} (hX : Memℒp X 2)
    (hY : Memℒp Y 2) (h : @IndepFun _ _ _ (_) _ _ X Y ℙ) : Var[X + Y] = Var[X] + Var[Y] :=
  calc
    Var[X + Y] = 𝔼[fun a => X a ^ 2 + Y a ^ 2 + 2 * X a * Y a] - 𝔼[X + Y] ^ 2 := by
      simp [variance_def' (hX.add hY), add_sq']
      -- 🎉 no goals
    _ = 𝔼[X ^ 2] + 𝔼[Y ^ 2] + (2 : ℝ) * 𝔼[X * Y] - (𝔼[X] + 𝔼[Y]) ^ 2 := by
      simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply, mul_assoc]
      -- ⊢ (∫ (a : Ω), X a ^ 2 + Y a ^ 2 + 2 * (X a * Y a)) - (∫ (a : Ω), X a + Y a) ^  …
      rw [integral_add, integral_add, integral_add, integral_mul_left]
      · exact hX.integrable one_le_two
        -- 🎉 no goals
      · exact hY.integrable one_le_two
        -- 🎉 no goals
      · exact hX.integrable_sq
        -- 🎉 no goals
      · exact hY.integrable_sq
        -- 🎉 no goals
      · exact hX.integrable_sq.add hY.integrable_sq
        -- 🎉 no goals
      · apply Integrable.const_mul
        -- ⊢ Integrable fun x => X x * Y x
        exact h.integrable_mul (hX.integrable one_le_two) (hY.integrable one_le_two)
        -- 🎉 no goals
    _ = 𝔼[X ^ 2] + 𝔼[Y ^ 2] + 2 * (𝔼[X] * 𝔼[Y]) - (𝔼[X] + 𝔼[Y]) ^ 2 := by
      congr
      -- ⊢ ∫ (a : Ω), (X * Y) a = (∫ (a : Ω), X a) * ∫ (a : Ω), Y a
      exact h.integral_mul_of_integrable (hX.integrable one_le_two) (hY.integrable one_le_two)
      -- 🎉 no goals
    _ = Var[X] + Var[Y] := by simp only [variance_def', hX, hY, Pi.pow_apply]; ring
                              -- ⊢ ((∫ (a : Ω), X a ^ 2) + ∫ (a : Ω), Y a ^ 2) + ↑2 * ((∫ (a : Ω), X a) * ∫ (a  …
                                                                               -- 🎉 no goals
#align probability_theory.indep_fun.variance_add ProbabilityTheory.IndepFun.variance_add

-- Porting note: supplied `MeasurableSpace Ω` argument of `hs`, `h` by unification
/-- The variance of a finite sum of pairwise independent random variables is the sum of the
variances. -/
theorem IndepFun.variance_sum [@IsProbabilityMeasure Ω _ ℙ] {ι : Type*} {X : ι → Ω → ℝ}
    {s : Finset ι} (hs : ∀ i ∈ s, @Memℒp _ _ _ (_) (X i) 2 ℙ)
    (h : Set.Pairwise ↑s fun i j => @IndepFun _ _ _ (_) _ _ (X i) (X j) ℙ) :
    Var[∑ i in s, X i] = ∑ i in s, Var[X i] := by
  classical
  induction' s using Finset.induction_on with k s ks IH
  · simp only [Finset.sum_empty, variance_zero]
  rw [variance_def' (memℒp_finset_sum' _ hs), sum_insert ks, sum_insert ks]
  simp only [add_sq']
  calc
    𝔼[X k ^ 2 + (∑ i in s, X i) ^ 2 + 2 * X k * ∑ i in s, X i] - 𝔼[X k + ∑ i in s, X i] ^ 2 =
        𝔼[X k ^ 2] + 𝔼[(∑ i in s, X i) ^ 2] + 𝔼[2 * X k * ∑ i in s, X i] -
          (𝔼[X k] + 𝔼[∑ i in s, X i]) ^ 2 := by
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
    _ = Var[X k] + Var[∑ i in s, X i] +
        (𝔼[2 * X k * ∑ i in s, X i] - 2 * 𝔼[X k] * 𝔼[∑ i in s, X i]) := by
      rw [variance_def' (hs _ (mem_insert_self _ _)),
        variance_def' (memℒp_finset_sum' _ fun i hi => hs _ (mem_insert_of_mem hi))]
      ring
    _ = Var[X k] + Var[∑ i in s, X i] := by
      simp only [mul_assoc, integral_mul_left, Pi.mul_apply, Pi.one_apply, sum_apply,
        add_right_eq_self, mul_sum]
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
      have : ∀ (a : Ω), @OfNat.ofNat (Ω → ℝ) 2 instOfNat a = (2 : ℝ) := fun a => rfl
      conv_lhs => enter [1, 2, a]; rw [this]
      rw [integral_mul_left, IndepFun.integral_mul', sub_self]
      · apply h (mem_insert_self _ _) (mem_insert_of_mem hi)
        exact fun hki => ks (hki.symm ▸ hi)
      · exact Memℒp.aestronglyMeasurable (hs _ (mem_insert_self _ _))
      · exact Memℒp.aestronglyMeasurable (hs _ (mem_insert_of_mem hi))
    _ = Var[X k] + ∑ i in s, Var[X i] := by
      rw [IH (fun i hi => hs i (mem_insert_of_mem hi))
          (h.mono (by simp only [coe_insert, Set.subset_insert]))]
#align probability_theory.indep_fun.variance_sum ProbabilityTheory.IndepFun.variance_sum

end ProbabilityTheory
