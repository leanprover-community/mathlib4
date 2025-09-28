/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# ℒp space

This file describes properties of almost everywhere strongly measurable functions with finite
`p`-seminorm, denoted by `eLpNorm f p μ` and defined for `p:ℝ≥0∞` as `0` if `p=0`,
`(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and `essSup ‖f‖ μ` for `p=∞`.

The Prop-valued `MemLp f p μ` states that a function `f : α → E` has finite `p`-seminorm
and is almost everywhere strongly measurable.

## Main definitions

* `eLpNorm' f p μ` : `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `f : α → F` and `p : ℝ`, where `α` is a measurable
  space and `F` is a normed group.
* `eLpNormEssSup f μ` : seminorm in `ℒ∞`, equal to the essential supremum `essSup ‖f‖ μ`.
* `eLpNorm f p μ` : for `p : ℝ≥0∞`, seminorm in `ℒp`, equal to `0` for `p=0`, to `eLpNorm' f p μ`
  for `0 < p < ∞` and to `eLpNormEssSup f μ` for `p = ∞`.

* `MemLp f p μ` : property that the function `f` is almost everywhere strongly measurable and has
  finite `p`-seminorm for the measure `μ` (`eLpNorm f p μ < ∞`)

-/

noncomputable section

open scoped NNReal ENNReal

variable {α ε ε' E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε] [ENorm ε']

namespace MeasureTheory

section Lp

/-!
### ℒp seminorm

We define the ℒp seminorm, denoted by `eLpNorm f p μ`. For real `p`, it is given by an integral
formula (for which we use the notation `eLpNorm' f p μ`), and for `p = ∞` it is the essential
supremum (for which we use the notation `eLpNormEssSup f μ`).

We also define a predicate `MemLp f p μ`, requesting that a function is almost everywhere
measurable and has finite `eLpNorm f p μ`.

This paragraph is devoted to the basic properties of these definitions. It is constructed as
follows: for a given property, we prove it for `eLpNorm'` and `eLpNormEssSup` when it makes sense,
deduce it for `eLpNorm`, and translate it in terms of `MemLp`.
-/


/-- `(∫ ‖f a‖^q ∂μ) ^ (1/q)`, which is a seminorm on the space of measurable functions for which
this quantity is finite.

Note: this is a purely auxiliary quantity; lemmas about `eLpNorm'` should only be used to
prove results about `eLpNorm`; every `eLpNorm'` lemma should have a `eLpNorm` version. -/
def eLpNorm' {_ : MeasurableSpace α} (f : α → ε) (q : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  (∫⁻ a, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q)

lemma eLpNorm'_eq_lintegral_enorm {_ : MeasurableSpace α} (f : α → ε) (q : ℝ) (μ : Measure α) :
    eLpNorm' f q μ = (∫⁻ a, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q) :=
  rfl

/-- seminorm for `ℒ∞`, equal to the essential supremum of `‖f‖`. -/
def eLpNormEssSup {_ : MeasurableSpace α} (f : α → ε) (μ : Measure α) :=
  essSup (fun x => ‖f x‖ₑ) μ

lemma eLpNormEssSup_eq_essSup_enorm {_ : MeasurableSpace α} (f : α → ε) (μ : Measure α) :
    eLpNormEssSup f μ = essSup (‖f ·‖ₑ) μ := rfl

/-- `ℒp` seminorm, equal to `0` for `p=0`, to `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and to
`essSup ‖f‖ μ` for `p = ∞`. -/
def eLpNorm {_ : MeasurableSpace α}
    (f : α → ε) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f (ENNReal.toReal p) μ

variable {μ ν : Measure α}

theorem eLpNorm_eq_eLpNorm' (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → ε} :
    eLpNorm f p μ = eLpNorm' f (ENNReal.toReal p) μ := by simp [eLpNorm, hp_ne_zero, hp_ne_top]

lemma eLpNorm_nnreal_eq_eLpNorm' {f : α → ε} {p : ℝ≥0} (hp : p ≠ 0) :
    eLpNorm f p μ = eLpNorm' f p μ :=
  eLpNorm_eq_eLpNorm' (by exact_mod_cast hp) ENNReal.coe_ne_top

theorem eLpNorm_eq_lintegral_rpow_enorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → ε} :
    eLpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
  rw [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top, eLpNorm'_eq_lintegral_enorm]

lemma eLpNorm_nnreal_eq_lintegral {f : α → ε} {p : ℝ≥0} (hp : p ≠ 0) :
    eLpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) :=
  eLpNorm_nnreal_eq_eLpNorm' hp

theorem eLpNorm_one_eq_lintegral_enorm {f : α → ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm one_ne_zero ENNReal.coe_ne_top, ENNReal.toReal_one,
    one_div_one, ENNReal.rpow_one]

@[simp]
theorem eLpNorm_exponent_top {f : α → ε} : eLpNorm f ∞ μ = eLpNormEssSup f μ := by simp [eLpNorm]

/-- The property that `f : α → E` is a.e. strongly measurable and `(∫ ‖f a‖ ^ p ∂μ) ^ (1/p)`
is finite if `p < ∞`, or `essSup ‖f‖ < ∞` if `p = ∞`. -/
def MemLp {α} {_ : MeasurableSpace α} [TopologicalSpace ε] (f : α → ε) (p : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞

theorem MemLp.aestronglyMeasurable [TopologicalSpace ε] {f : α → ε} {p : ℝ≥0∞} (h : MemLp f p μ) :
    AEStronglyMeasurable f μ :=
  h.1

lemma MemLp.aemeasurable [MeasurableSpace ε] [TopologicalSpace ε]
    [TopologicalSpace.PseudoMetrizableSpace ε] [BorelSpace ε]
    {f : α → ε} {p : ℝ≥0∞} (hf : MemLp f p μ) :
    AEMeasurable f μ :=
  hf.aestronglyMeasurable.aemeasurable

theorem lintegral_rpow_enorm_eq_rpow_eLpNorm' {f : α → ε} (hq0_lt : 0 < q) :
    ∫⁻ a, ‖f a‖ₑ ^ q ∂μ = eLpNorm' f q μ ^ q := by
  rw [eLpNorm'_eq_lintegral_enorm, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀, ENNReal.rpow_one]
  exact hq0_lt.ne'

lemma eLpNorm_nnreal_pow_eq_lintegral {f : α → ε} {p : ℝ≥0} (hp : p ≠ 0) :
    eLpNorm f p μ ^ (p : ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) ∂μ := by
  simp [eLpNorm_eq_eLpNorm' (by exact_mod_cast hp) ENNReal.coe_ne_top,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hp)]

end Lp

end MeasureTheory
