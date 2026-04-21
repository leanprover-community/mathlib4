/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Etienne Marion, Hanzhang Cheng
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! # Poisson distributions over ℕ

Define the Poisson measure over the natural numbers. For `r : ℝ≥0`, `poissonMeasure r` is the
measure which to `{n}` associates `exp (-r) * r ^ n / (n)!`.

## Main definitions

* `poissonMeasure r`: a Poisson measure on `ℕ`, parametrized by its rate `r : ℝ≥0`.

## Main results

* `poissonMeasure_conv_poissonMeasure`: `Poisson(r₁) ∗ Poisson(r₂) = Poisson(r₁ + r₂)`.
* `IndepFun.hasLaw_add_poissonMeasure`: the sum of two independent Poisson random variables
  is again Poisson.
-/

@[expose] public section

open MeasureTheory Real
open scoped NNReal Nat

namespace ProbabilityTheory

/-- The poisson measure with rate `r : ℝ≥0` as a measure over `ℕ`. -/
noncomputable
def poissonMeasure (r : ℝ≥0) : Measure ℕ :=
  Measure.sum (fun n ↦ ENNReal.ofReal (exp (-r) * r ^ n / (n)!) • (.dirac n))

/-- The Poisson probability distribution with rate `r`. -/
scoped notation3 "Po(" r ")" => poissonMeasure r

/-- The Poisson probability distribution with rate `r` valued in the `AddMonoidWithOne` `R`. -/
scoped notation3 "Po(" R ", " r ")" => (poissonMeasure r).map (Nat.cast : ℕ → R)

lemma poissonMeasure_singleton (r : ℝ≥0) (n : ℕ) :
    Po(r) {n} = ENNReal.ofReal (exp (-r) * r ^ n / (n)!) := by
  rw [poissonMeasure, Measure.sum_smul_dirac_singleton]

lemma poissonMeasure_real_singleton (r : ℝ≥0) (n : ℕ) :
    Po(r).real {n} = exp (-r) * r ^ n / (n)! := by
  rw [measureReal_def, poissonMeasure_singleton, ENNReal.toReal_ofReal (by positivity)]

lemma poissonMeasure_real_singleton_pos {r : ℝ≥0} (n : ℕ) (hr : 0 < r) :
    0 < Po(r).real {n} := by
  rw [poissonMeasure_real_singleton]
  positivity

lemma hasSum_one_poissonMeasure (r : ℝ≥0) : HasSum (fun n ↦ exp (-r) * r ^ n / (n)!) 1 := by
  convert (NormedSpace.expSeries_div_hasSum_exp (r : ℝ)).mul_left (exp (-r)) using 1
  · simp_rw [mul_div_assoc]
  · simp [← exp_eq_exp_ℝ, ← exp_add]

instance (r : ℝ≥0) : IsProbabilityMeasure Po(r) :=
  (hasSum_one_poissonMeasure r).isProbabilityMeasure_sum_dirac (fun _ ↦ by positivity)

instance (r : ℝ≥0) {R : Type*} [AddMonoidWithOne R] [MeasurableSpace R] :
    IsProbabilityMeasure Po(R, r) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

section Integral

variable {E : Type*} [NormedAddCommGroup E]
variable {R : Type*} [AddMonoidWithOne R] [MeasurableSpace R]

lemma integrable_poissonMeasure_iff {r : ℝ≥0} {f : ℕ → E} :
    Integrable f Po(r) ↔ Summable (fun n ↦ exp (-r) * r ^ n / (n)! * ‖f n‖) := by
  rw [poissonMeasure, integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n ↦ ?_ * _)
  rw [ENNReal.toReal_ofReal (by positivity)]

lemma integrable_map_cast_poissonMeasure_iff {r : ℝ≥0} [Countable R] [MeasurableSingletonClass R]
  {f : R → E} : Integrable f Po(R, r) ↔ Integrable (f ∘ Nat.cast) Po(r) :=
  integrable_map_measure AEStronglyMeasurable.of_discrete (measurable_of_countable _).aemeasurable

variable [NormedSpace ℝ E]

lemma hasSum_integral_poissonMeasure [CompleteSpace E] {r : ℝ≥0} {f : ℕ → E}
    (hf : Integrable f Po(r)) :
    HasSum (fun n ↦ (exp (-r) * r ^ n / (n)!) • f n) (∫ n, f n ∂Po(r)) := by
  have : (fun n ↦ (exp (-r) * r ^ n / (n)!) • f n) =
      fun n ↦ (ENNReal.ofReal (exp (-r) * r ^ n / (n)!)).toReal • f n := by
    ext; rw [ENNReal.toReal_ofReal (by positivity)]
  rw [this]
  apply hasSum_integral_sum_dirac (by simp)
  convert integrable_poissonMeasure_iff.1 hf
  rw [ENNReal.toReal_ofReal (by positivity)]

/-- If a function is integrable with respect to `poissonMeasure r`, then its integral
against this measure is given by its sum weighted by `exp (-r) * r ^ n / n!`.

See `integral_poissonMeasure` for a version where the codomain is finite-dimensional
and does not require the integrability hypothesis. -/
lemma integral_poissonMeasure' [CompleteSpace E] {r : ℝ≥0} {f : ℕ → E}
    (hf : Integrable f Po(r)) :
    ∫ n, f n ∂Po(r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f n :=
  (hasSum_integral_poissonMeasure hf).tsum_eq.symm

lemma integral_map_cast_poissonMeasure' [CompleteSpace E] [Countable R] [MeasurableSingletonClass R]
    {r : ℝ≥0} {f : R → E} (hf : Integrable f Po(R, r)) :
    ∫ x, f x ∂Po(R, r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f (n : R) := by
  rw [integral_map (measurable_of_countable _).aemeasurable AEStronglyMeasurable.of_discrete]
  rw [integrable_map_cast_poissonMeasure_iff] at hf
  exact integral_poissonMeasure' hf

/-- The integral of a function taking values in a finite-dimensional space
against `poissonMeasure r` is given by its sum weighted by `exp (-r) * r ^ n / n!`. This version
does not require integrability, as the integral exists if and only if the sum exists, and otherwise
they are both defined to be zero.

See `integral_poissonMeasure'` with a general codomain which assumes integrability. -/
lemma integral_poissonMeasure [FiniteDimensional ℝ E] (r : ℝ≥0) (f : ℕ → E) :
    ∫ n, f n ∂Po(r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f n := by
  rw [poissonMeasure, integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (by positivity)]

lemma integral_map_cast_poissonMeasure [FiniteDimensional ℝ E] (r : ℝ≥0) [Countable R]
  [MeasurableSingletonClass R] (f : R → E) :
    ∫ x, f x ∂Po(R, r) = ∑' n, (exp (-r) * r ^ n / (n)!) • f n := by
  rw [integral_map (measurable_of_countable _).aemeasurable AEStronglyMeasurable.of_discrete,
      integral_poissonMeasure]

end Integral

section CharFun

open Complex

/-- The characteristic function of the Poisson distribution with rate `r` is
`t ↦ exp(r(exp(it) - 1))`. -/
lemma charFun_map_cast_poissonMeasure (r : ℝ≥0) (t : ℝ) :
    charFun Po(ℝ, r) t = cexp (r * (cexp (t * I) - 1)) := by
  rw [charFun_apply,
      integral_map (measurable_of_countable _).aemeasurable (by fun_prop),
      integral_poissonMeasure r]
  simp_rw [show ∀ (a : ℕ), inner ℝ (a : ℝ) t = a * t from
           fun a => by change t * a = a * t; ring]
  calc ∑' a, ((rexp (-r) * r ^ a / a ! : ℝ) : ℂ) * cexp (↑(a * t) * I)
  _ = ∑' a, (rexp (-r)) * ((r * cexp (t * I)) ^ a / a !) := by
      congr 1 with a; push_cast; rw [mul_pow, ← Complex.exp_nat_mul]; ring_nf
  _ = (rexp (-r)) * ∑' a, ((r * cexp (t * I)) ^ a / a !) := tsum_mul_left
  _ = (rexp (-r)) * cexp (r * cexp (t * I)) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp (r * cexp (t * I))).tsum_eq, exp_eq_exp_ℂ]
  _ = cexp (r * (cexp (t * I) - 1)) := by
      rw [ofReal_exp, exp_eq_exp_ℂ, ← NormedSpace.exp_add]; congr 1; push_cast; ring

/-- Convolution of Poisson distributions on `ℝ`. -/
private theorem map_cast_poissonMeasure_conv_real (r₁ r₂ : ℝ≥0) :
    Po(ℝ, r₁) ∗ Po(ℝ, r₂) = Po(ℝ, r₁ + r₂) := by
  apply Measure.ext_of_charFun
  ext t
  simp only [charFun_conv, charFun_map_cast_poissonMeasure, ← Complex.exp_add]
  congr 1; push_cast; ring

end CharFun

/-! ## Convolution of Poisson measures on ℕ -/

section Convolution

variable {R : Type*} [AddMonoidWithOne R] [MeasurableSpace R]

theorem poissonMeasure_conv_poissonMeasure (r₁ r₂ : ℝ≥0) :
    Po(r₁) ∗ Po(r₂) = Po(r₁ + r₂) := by
  apply (MeasurableEmbedding.natCast (α := ℝ)).map_injective
  rw [← Nat.coe_castAddMonoidHom, Measure.map_conv_addMonoidHom _ (by fun_prop)]
  exact map_cast_poissonMeasure_conv_real _ _

theorem map_cast_poissonMeasure_conv [MeasurableAdd₂ R] (r₁ r₂ : ℝ≥0) :
    Po(R, r₁) ∗ Po(R, r₂) = Po(R, r₁ + r₂) := by
  have h : ∀ (μ ν : Measure ℕ), (μ.map Nat.cast : Measure R) ∗ (ν.map Nat.cast) =
      (μ ∗ ν).map Nat.cast := fun μ ν ↦ by
    rw [← Nat.coe_castAddMonoidHom, Measure.map_conv_addMonoidHom _ (by fun_prop)]
  rw [h, poissonMeasure_conv_poissonMeasure]

/-- The sum of two independent Poisson random variables with rates `r₁, r₂` is a Poisson
random variable with rate `r₁ + r₂`. -/
theorem IndepFun.hasLaw_add_poissonMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {r₁ r₂ : ℝ≥0} {X Y : Ω → ℕ}
    (hXY : IndepFun X Y P) (hX : HasLaw X Po(r₁) P)
    (hY : HasLaw Y Po(r₂) P) :
    HasLaw (X + Y) Po(r₁ + r₂) P := by
  rw [← poissonMeasure_conv_poissonMeasure]
  exact hXY.hasLaw_add hX hY

/-- The sum of two independent Poisson random variables with rates `r₁, r₂` taking values in `R`
is a Poisson random variable with rate `r₁ + r₂`. -/
theorem IndepFun.hasLaw_add_map_cast_poissonMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [MeasurableAdd₂ R] {r₁ r₂ : ℝ≥0} {X Y : Ω → R} (hXY : IndepFun X Y P)
    (hX : HasLaw X Po(R, r₁) P) (hY : HasLaw Y Po(R, r₂) P) :
    HasLaw (X + Y) Po(R, r₁ + r₂) P := by
  rw [← map_cast_poissonMeasure_conv]
  exact hXY.hasLaw_add hX hY

end Convolution

section PoissonPMF

/-- The pmf of the Poisson distribution depending on its rate, as a function to ℝ -/
@[deprecated poissonMeasure (since := "2026-03-08")]
noncomputable
def poissonPMFReal (r : ℝ≥0) (n : ℕ) : ℝ := exp (-r) * r ^ n / (n)!

@[deprecated (since := "2026-03-08")]
alias poissonPMFRealSum := hasSum_one_poissonMeasure

set_option linter.deprecated false in
@[deprecated poissonMeasure_real_singleton_pos (since := "2026-03-08")]
lemma poissonPMFReal_pos {r : ℝ≥0} {n : ℕ} (hr : 0 < r) : 0 < poissonPMFReal r n := by
  rw [poissonPMFReal]
  positivity

set_option linter.deprecated false in
@[deprecated measureReal_nonneg (since := "2026-03-08")]
lemma poissonPMFReal_nonneg {r : ℝ≥0} {n : ℕ} : 0 ≤ poissonPMFReal r n := by
  unfold poissonPMFReal
  positivity

set_option linter.deprecated false in
/-- The pmf of the Poisson distribution depending on its rate, as a PMF. -/
@[deprecated poissonMeasure (since := "2026-03-08")]
noncomputable
def poissonPMF (r : ℝ≥0) : PMF ℕ := by
  refine ⟨fun n ↦ ENNReal.ofReal (poissonPMFReal r n), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← toNNReal_one]
  exact (poissonPMFRealSum r).toNNReal (fun n ↦ poissonPMFReal_nonneg)

set_option linter.deprecated false in
@[deprecated poissonMeasure (since := "2026-03-08")]
lemma poissonPMFReal_ofReal_eq_poissonPMF (r : ℝ≥0) (n : ℕ) :
    ENNReal.ofReal (poissonPMFReal r n) = poissonPMF r n := by
  simpa only [poissonPMF] using by rfl

set_option linter.deprecated false in
@[deprecated Measurable.of_discrete (since := "2026-03-08")]
lemma measurable_poissonPMFReal (r : ℝ≥0) : Measurable (poissonPMFReal r) := by fun_prop

set_option linter.deprecated false in
@[deprecated StronglyMeasurable.of_discrete (since := "2026-03-08")]
lemma stronglyMeasurable_poissonPMFReal (r : ℝ≥0) : StronglyMeasurable (poissonPMFReal r) :=
  stronglyMeasurable_iff_measurable.mpr (measurable_poissonPMFReal r)

end PoissonPMF

end ProbabilityTheory
