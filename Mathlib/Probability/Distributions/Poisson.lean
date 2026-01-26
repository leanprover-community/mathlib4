/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Hanzhang Cheng
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction
public import Mathlib.Probability.Independence.Basic

/-! # Poisson distributions over ℕ

Define the Poisson measure over the natural numbers

## Main definitions
* `poissonPMFReal`: the function `fun n ↦ exp (- λ) * λ ^ n / n!`
  for `n ∈ ℕ`, which is the probability density function of a Poisson distribution with
  rate `λ > 0`.
* `poissonPMF`: `ℝ≥0∞`-valued pdf,
  `poissonPMF λ = ENNReal.ofReal (poissonPMFReal λ)`.
* `poissonMeasure`: a Poisson measure on `ℕ`, parametrized by its rate `λ`.
* `poissonMeasureReal`: the Poisson distribution on `ℝ`, obtained as the pushforward
  of `poissonMeasure` along `Nat.cast`.

## Main statements

* `poissonMeasureReal_charFun`: the characteristic function of the Poisson distribution
  is `t ↦ exp(r(exp(it) - 1))`.
* `poissonMeasure_conv_poissonMeasure`: the convolution of two Poisson distributions
  is again a Poisson distribution: `Poisson(r₁) * Poisson(r₂) = Poisson(r₁ + r₂)`.
* `poissonMeasure_add_poissonMeasure_of_indepFun`: the sum of two independent Poisson
  random variables is again Poisson.

-/

@[expose] public section

open scoped ENNReal NNReal Nat

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section PoissonPMF

/-- The pmf of the Poisson distribution depending on its rate, as a function to ℝ -/
noncomputable
def poissonPMFReal (r : ℝ≥0) (n : ℕ) : ℝ := exp (-r) * r ^ n / n !

lemma poissonPMFRealSum (r : ℝ≥0) : HasSum (fun n ↦ poissonPMFReal r n) 1 := by
  let r := r.toReal
  unfold poissonPMFReal
  apply (hasSum_mul_left_iff (exp_ne_zero r)).mp
  simp only [mul_one]
  have : (fun i ↦ rexp r * (rexp (-r) * r ^ i / ↑(Nat.factorial i))) =
      fun i ↦ r ^ i / ↑(Nat.factorial i) := by
    ext n
    rw [mul_div_assoc, exp_neg, ← mul_assoc, ← div_eq_mul_inv, div_self (exp_ne_zero r), one_mul]
  rw [this, exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp r

/-- The Poisson pmf is positive for all natural numbers -/
lemma poissonPMFReal_pos {r : ℝ≥0} {n : ℕ} (hr : 0 < r) : 0 < poissonPMFReal r n := by
  rw [poissonPMFReal]
  positivity

lemma poissonPMFReal_nonneg {r : ℝ≥0} {n : ℕ} : 0 ≤ poissonPMFReal r n := by
  unfold poissonPMFReal
  positivity

/-- The pmf of the Poisson distribution depending on its rate, as a PMF. -/
noncomputable
def poissonPMF (r : ℝ≥0) : PMF ℕ := by
  refine ⟨fun n ↦ ENNReal.ofReal (poissonPMFReal r n), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← toNNReal_one]
  exact (poissonPMFRealSum r).toNNReal (fun n ↦ poissonPMFReal_nonneg)

/-- The Poisson pmf is measurable. -/
@[fun_prop]
lemma measurable_poissonPMFReal (r : ℝ≥0) : Measurable (poissonPMFReal r) := by fun_prop

@[fun_prop]
lemma stronglyMeasurable_poissonPMFReal (r : ℝ≥0) : StronglyMeasurable (poissonPMFReal r) :=
  stronglyMeasurable_iff_measurable.mpr (measurable_poissonPMFReal r)

end PoissonPMF

/-! ## Poisson measure on ℕ -/

/-- Measure defined by the Poisson distribution -/
noncomputable
def poissonMeasure (r : ℝ≥0) : Measure ℕ := (poissonPMF r).toMeasure

instance isProbabilityMeasurePoisson (r : ℝ≥0) :
    IsProbabilityMeasure (poissonMeasure r) := PMF.toMeasure.isProbabilityMeasure (poissonPMF r)

/-! ## Poisson measure on ℝ -/

section PoissonMeasureReal

/-- Poisson distribution on `ℝ`, obtained as the image of the Poisson measure on `ℕ`.
This is useful for characteristic function arguments and convolution proofs. -/
noncomputable def poissonMeasureReal (r : ℝ≥0) : Measure ℝ :=
  (poissonMeasure r).map (↑)

lemma poissonMeasureReal_eq_poissonMeasure_map (r : ℝ≥0) :
    poissonMeasureReal r = (poissonMeasure r).map (Nat.cast : ℕ → ℝ) := rfl

instance isProbabilityMeasure_poissonMeasureReal (r : ℝ≥0) :
    IsProbabilityMeasure (poissonMeasureReal r) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- The characteristic function of the Poisson distribution with rate `r` is
`t ↦ exp(r(exp(it) - 1))`. -/
lemma poissonMeasureReal_charFun (r : ℝ≥0) (t : ℝ) :
    charFun (poissonMeasureReal r) t =
    Complex.exp (r * (Complex.exp (t * Complex.I) - 1)) := by
  rw [charFun_apply, poissonMeasureReal]
  have hm_natCast : AEMeasurable (Nat.cast : ℕ → ℝ) (poissonMeasure r) :=
    (measurable_of_countable _).aemeasurable
  rw [integral_map hm_natCast (by fun_prop), poissonMeasure, PMF.integral_eq_tsum]
  · simp_rw [show ∀ a, ((poissonPMF r) a).toReal = poissonPMFReal r a from
             fun a => ENNReal.toReal_ofReal poissonPMFReal_nonneg,
             poissonPMFReal, Complex.real_smul, real_inner_comm, RCLike.inner_apply, conj_trivial]
    have h_term_eq (a : ℕ) :
        ↑(rexp (-↑r) * ↑r ^ a / ↑a !) * Complex.exp (↑(↑a * t) * Complex.I) =
        ↑(rexp (-↑r)) * ((↑r * Complex.exp (↑t * Complex.I)) ^ a / ↑a !) := by
      push_cast; rw [mul_pow, ← Complex.exp_nat_mul]; ring_nf
    simp_rw [h_term_eq, tsum_mul_left, (NormedSpace.expSeries_div_hasSum_exp
             (↑r * Complex.exp (↑t * Complex.I))).tsum_eq]
    rw [Complex.exp_eq_exp_ℂ, Complex.ofReal_exp, Complex.exp_eq_exp_ℂ, ← NormedSpace.exp_add]
    congr 1; push_cast; ring
  · refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    calc ∫⁻ n, ‖Complex.exp (↑(inner ℝ (↑n : ℝ) t) * Complex.I)‖₊ ∂(poissonPMF r).toMeasure
        ≤ ∫⁻ _, 1 ∂(poissonPMF r).toMeasure := lintegral_mono fun n => by
          simp only [RCLike.inner_apply, conj_trivial, Complex.nnnorm_exp_ofReal_mul_I,
            ENNReal.coe_one, le_refl]
      _ = 1 := by simp only [lintegral_const, one_mul, measure_univ]
      _ < ⊤ := ENNReal.one_lt_top

/-- Convolution of Poisson distributions on `ℝ`. -/
theorem poissonMeasureReal_conv_poissonMeasureReal (r₁ r₂ : ℝ≥0) :
    poissonMeasureReal r₁ ∗ poissonMeasureReal r₂ = poissonMeasureReal (r₁ + r₂) := by
  apply Measure.ext_of_charFun
  ext t
  simp only [charFun_conv, poissonMeasureReal_charFun, ← Complex.exp_add]
  congr 1; push_cast; ring

end PoissonMeasureReal

/-! ## Convolution of Poisson measures on ℕ -/

section Convolution

-- TODO: This lemma is not specific to Poisson distributions and should be moved to another file.
lemma measurableEmbedding_natCast : MeasurableEmbedding (Nat.cast : ℕ → ℝ) :=
  Nat.isClosedEmbedding_coe_real.measurableEmbedding

theorem poissonMeasure_conv_poissonMeasure (r₁ r₂ : ℝ≥0) :
    poissonMeasure r₁ ∗ poissonMeasure r₂ = poissonMeasure (r₁ + r₂) := by
  have hconv_real := poissonMeasureReal_conv_poissonMeasureReal r₁ r₂
  simp only [poissonMeasureReal] at hconv_real
  have hmap_conv : ((poissonMeasure r₁) ∗ (poissonMeasure r₂)).map (Nat.cast : ℕ → ℝ) =
      ((poissonMeasure r₁).map Nat.cast) ∗ ((poissonMeasure r₂).map Nat.cast) := by
    convert Measure.map_conv_addMonoidHom (Nat.castAddMonoidHom ℝ) (measurable_of_countable _) <;>
      infer_instance
  rw [← hmap_conv] at hconv_real
  ext s _
  have h_meas_eq : ∀ μ : Measure ℕ, μ s = (μ.map Nat.cast) (Nat.cast '' s) := fun μ => by
    rw [measurableEmbedding_natCast.map_apply, Set.preimage_image_eq _ Nat.cast_injective]
  rw [h_meas_eq, h_meas_eq, hconv_real]

end Convolution

/-! ## Independence and sums of Poisson random variables -/

section Independence

/-- The sum of two independent Poisson random variables with rates `r₁, r₂` is a Poisson
random variable with rate `r₁ + r₂`. -/
theorem poissonMeasure_add_poissonMeasure_of_indepFun {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} (r₁ r₂ : ℝ≥0) (X Y : Ω → ℕ)
    (hXY : IndepFun X Y P) (hX : P.map X = poissonMeasure r₁)
    (hY : P.map Y = poissonMeasure r₂) :
    P.map (X + Y) = poissonMeasure (r₁ + r₂) := by
  rw [hXY.map_add_eq_map_conv_map₀', hX, hY, poissonMeasure_conv_poissonMeasure]
  · apply AEMeasurable.of_map_ne_zero; simp [NeZero.ne, hX]
  · apply AEMeasurable.of_map_ne_zero; simp [NeZero.ne, hY]
  · rw [hX]; apply IsFiniteMeasure.toSigmaFinite
  · rw [hY]; apply IsFiniteMeasure.toSigmaFinite

end Independence

end ProbabilityTheory
