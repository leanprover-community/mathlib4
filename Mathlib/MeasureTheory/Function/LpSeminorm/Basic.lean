/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import Mathlib.Analysis.NormedSpace.IndicatorFunction
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# ℒp space

This file describes properties of almost everywhere strongly measurable functions with finite
`p`-seminorm, denoted by `eLpNorm f p μ` and defined for `p:ℝ≥0∞` as `0` if `p=0`,
`(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and `essSup ‖f‖ μ` for `p=∞`.

The Prop-valued `Memℒp f p μ` states that a function `f : α → E` has finite `p`-seminorm
and is almost everywhere strongly measurable.

## Main definitions

* `eLpNorm' f p μ` : `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `f : α → F` and `p : ℝ`, where `α` is a measurable
  space and `F` is a normed group.
* `eLpNormEssSup f μ` : seminorm in `ℒ∞`, equal to the essential supremum `essSup ‖f‖ μ`.
* `eLpNorm f p μ` : for `p : ℝ≥0∞`, seminorm in `ℒp`, equal to `0` for `p=0`, to `eLpNorm' f p μ`
  for `0 < p < ∞` and to `eLpNormEssSup f μ` for `p = ∞`.

* `Memℒp f p μ` : property that the function `f` is almost everywhere strongly measurable and has
  finite `p`-seminorm for the measure `μ` (`eLpNorm f p μ < ∞`)

-/


noncomputable section


open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal Topology

variable {α E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

namespace MeasureTheory

section ℒp

/-!
### ℒp seminorm

We define the ℒp seminorm, denoted by `eLpNorm f p μ`. For real `p`, it is given by an integral
formula (for which we use the notation `eLpNorm' f p μ`), and for `p = ∞` it is the essential
supremum (for which we use the notation `eLpNormEssSup f μ`).

We also define a predicate `Memℒp f p μ`, requesting that a function is almost everywhere
measurable and has finite `eLpNorm f p μ`.

This paragraph is devoted to the basic properties of these definitions. It is constructed as
follows: for a given property, we prove it for `eLpNorm'` and `eLpNormEssSup` when it makes sense,
deduce it for `eLpNorm`, and translate it in terms of `Memℒp`.
-/


section ℒpSpaceDefinition

/-- `(∫ ‖f a‖^q ∂μ) ^ (1/q)`, which is a seminorm on the space of measurable functions for which
this quantity is finite -/
def eLpNorm' {_ : MeasurableSpace α} (f : α → F) (q : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ q ∂μ) ^ (1 / q)

/-- seminorm for `ℒ∞`, equal to the essential supremum of `‖f‖`. -/
def eLpNormEssSup {_ : MeasurableSpace α} (f : α → F) (μ : Measure α) :=
  essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ

/-- `ℒp` seminorm, equal to `0` for `p=0`, to `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and to
`essSup ‖f‖ μ` for `p = ∞`. -/
def eLpNorm {_ : MeasurableSpace α}
    (f : α → F) (p : ℝ≥0∞) (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then eLpNormEssSup f μ else eLpNorm' f (ENNReal.toReal p) μ

@[deprecated (since := "2024-07-26")] noncomputable alias snorm := eLpNorm

theorem eLpNorm_eq_eLpNorm' (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → F} :
    eLpNorm f p μ = eLpNorm' f (ENNReal.toReal p) μ := by simp [eLpNorm, hp_ne_zero, hp_ne_top]

@[deprecated (since := "2024-07-27")] alias snorm_eq_snorm' := eLpNorm_eq_eLpNorm'

lemma eLpNorm_nnreal_eq_eLpNorm' {f : α → F} {p : ℝ≥0} (hp : p ≠ 0) :
    eLpNorm f p μ = eLpNorm' f p μ :=
  eLpNorm_eq_eLpNorm' (by exact_mod_cast hp) ENNReal.coe_ne_top

@[deprecated (since := "2024-07-27")] alias snorm_nnreal_eq_snorm' := eLpNorm_nnreal_eq_eLpNorm'

theorem eLpNorm_eq_lintegral_rpow_nnnorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → F} :
    eLpNorm f p μ = (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
  rw [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top, eLpNorm']

@[deprecated (since := "2024-07-27")]
alias snorm_eq_lintegral_rpow_nnnorm := eLpNorm_eq_lintegral_rpow_nnnorm

lemma eLpNorm_nnreal_eq_lintegral {f : α → F} {p : ℝ≥0} (hp : p ≠ 0) :
    eLpNorm f p μ = (∫⁻ x, ‖f x‖₊ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) :=
  eLpNorm_nnreal_eq_eLpNorm' hp

@[deprecated (since := "2024-07-27")] alias snorm_nnreal_eq_lintegral := eLpNorm_nnreal_eq_lintegral

theorem eLpNorm_one_eq_lintegral_nnnorm {f : α → F} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖₊ ∂μ := by
  simp_rw [eLpNorm_eq_lintegral_rpow_nnnorm one_ne_zero ENNReal.coe_ne_top, ENNReal.one_toReal,
    one_div_one, ENNReal.rpow_one]

@[deprecated (since := "2024-07-27")]
alias snorm_one_eq_lintegral_nnnorm := eLpNorm_one_eq_lintegral_nnnorm

@[simp]
theorem eLpNorm_exponent_top {f : α → F} : eLpNorm f ∞ μ = eLpNormEssSup f μ := by simp [eLpNorm]

@[deprecated (since := "2024-07-27")]
alias snorm_exponent_top := eLpNorm_exponent_top

/-- The property that `f:α→E` is ae strongly measurable and `(∫ ‖f a‖^p ∂μ)^(1/p)` is finite
if `p < ∞`, or `essSup f < ∞` if `p = ∞`. -/
def Memℒp {α} {_ : MeasurableSpace α} (f : α → E) (p : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞

theorem Memℒp.aestronglyMeasurable {f : α → E} {p : ℝ≥0∞} (h : Memℒp f p μ) :
    AEStronglyMeasurable f μ :=
  h.1

theorem lintegral_rpow_nnnorm_eq_rpow_eLpNorm' {f : α → F} (hq0_lt : 0 < q) :
    ∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ q ∂μ = eLpNorm' f q μ ^ q := by
  rw [eLpNorm', ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀, ENNReal.rpow_one]
  exact (ne_of_lt hq0_lt).symm

@[deprecated (since := "2024-07-27")]
alias lintegral_rpow_nnnorm_eq_rpow_snorm' := lintegral_rpow_nnnorm_eq_rpow_eLpNorm'

lemma eLpNorm_nnreal_pow_eq_lintegral {f : α → F} {p : ℝ≥0} (hp : p ≠ 0) :
    eLpNorm f p μ ^ (p : ℝ) = ∫⁻ x, ‖f x‖₊ ^ (p : ℝ) ∂μ := by
  simp [eLpNorm_eq_eLpNorm' (by exact_mod_cast hp) ENNReal.coe_ne_top,
    lintegral_rpow_nnnorm_eq_rpow_eLpNorm' (show 0 < (p : ℝ) from pos_iff_ne_zero.mpr hp)]

@[deprecated (since := "2024-07-27")]
alias snorm_nnreal_pow_eq_lintegral := eLpNorm_nnreal_pow_eq_lintegral

end ℒpSpaceDefinition

section Top

theorem Memℒp.eLpNorm_lt_top {f : α → E} (hfp : Memℒp f p μ) : eLpNorm f p μ < ∞ :=
  hfp.2

@[deprecated (since := "2024-07-27")]
alias Memℒp.snorm_lt_top := Memℒp.eLpNorm_lt_top

theorem Memℒp.eLpNorm_ne_top {f : α → E} (hfp : Memℒp f p μ) : eLpNorm f p μ ≠ ∞ :=
  ne_of_lt hfp.2

@[deprecated (since := "2024-07-27")]
alias Memℒp.snorm_ne_top := Memℒp.eLpNorm_ne_top

theorem lintegral_rpow_nnnorm_lt_top_of_eLpNorm'_lt_top {f : α → F} (hq0_lt : 0 < q)
    (hfq : eLpNorm' f q μ < ∞) : (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ q ∂μ) < ∞ := by
  rw [lintegral_rpow_nnnorm_eq_rpow_eLpNorm' hq0_lt]
  exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt hq0_lt) (ne_of_lt hfq)

@[deprecated (since := "2024-07-27")]
alias lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top :=
  lintegral_rpow_nnnorm_lt_top_of_eLpNorm'_lt_top

theorem lintegral_rpow_nnnorm_lt_top_of_eLpNorm_lt_top {f : α → F} (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hfp : eLpNorm f p μ < ∞) : (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) < ∞ := by
  apply lintegral_rpow_nnnorm_lt_top_of_eLpNorm'_lt_top
  · exact ENNReal.toReal_pos hp_ne_zero hp_ne_top
  · simpa [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top] using hfp

@[deprecated (since := "2024-07-27")]
alias lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top := lintegral_rpow_nnnorm_lt_top_of_eLpNorm_lt_top

theorem eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top {f : α → F} (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : eLpNorm f p μ < ∞ ↔ (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) < ∞ :=
  ⟨lintegral_rpow_nnnorm_lt_top_of_eLpNorm_lt_top hp_ne_zero hp_ne_top, by
    intro h
    have hp' := ENNReal.toReal_pos hp_ne_zero hp_ne_top
    have : 0 < 1 / p.toReal := div_pos zero_lt_one hp'
    simpa [eLpNorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top] using
      ENNReal.rpow_lt_top_of_nonneg (le_of_lt this) (ne_of_lt h)⟩

@[deprecated (since := "2024-07-27")]
alias snorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top :=
  eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top

end Top

section Zero

@[simp]
theorem eLpNorm'_exponent_zero {f : α → F} : eLpNorm' f 0 μ = 1 := by
  rw [eLpNorm', div_zero, ENNReal.rpow_zero]

@[deprecated (since := "2024-07-27")]
alias snorm'_exponent_zero := eLpNorm'_exponent_zero

@[simp]
theorem eLpNorm_exponent_zero {f : α → F} : eLpNorm f 0 μ = 0 := by simp [eLpNorm]

@[deprecated (since := "2024-07-27")]
alias snorm_exponent_zero := eLpNorm_exponent_zero

@[simp]
theorem memℒp_zero_iff_aestronglyMeasurable {f : α → E} :
    Memℒp f 0 μ ↔ AEStronglyMeasurable f μ := by simp [Memℒp, eLpNorm_exponent_zero]

@[simp]
theorem eLpNorm'_zero (hp0_lt : 0 < q) : eLpNorm' (0 : α → F) q μ = 0 := by simp [eLpNorm', hp0_lt]

@[deprecated (since := "2024-07-27")]
alias snorm'_zero := eLpNorm'_zero

@[simp]
theorem eLpNorm'_zero' (hq0_ne : q ≠ 0) (hμ : μ ≠ 0) : eLpNorm' (0 : α → F) q μ = 0 := by
  rcases le_or_lt 0 q with hq0 | hq_neg
  · exact eLpNorm'_zero (lt_of_le_of_ne hq0 hq0_ne.symm)
  · simp [eLpNorm', ENNReal.rpow_eq_zero_iff, hμ, hq_neg]

@[deprecated (since := "2024-07-27")]
alias snorm'_zero' := eLpNorm'_zero'

@[simp]
theorem eLpNormEssSup_zero : eLpNormEssSup (0 : α → F) μ = 0 := by
  simp_rw [eLpNormEssSup, Pi.zero_apply, nnnorm_zero, ENNReal.coe_zero, ← ENNReal.bot_eq_zero]
  exact essSup_const_bot

@[deprecated (since := "2024-07-27")]
alias snormEssSup_zero := eLpNormEssSup_zero

@[simp]
theorem eLpNorm_zero : eLpNorm (0 : α → F) p μ = 0 := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp only [h_top, eLpNorm_exponent_top, eLpNormEssSup_zero]
  rw [← Ne] at h0
  simp [eLpNorm_eq_eLpNorm' h0 h_top, ENNReal.toReal_pos h0 h_top]

@[deprecated (since := "2024-07-27")]
alias snorm_zero := eLpNorm_zero

@[simp]
theorem eLpNorm_zero' : eLpNorm (fun _ : α => (0 : F)) p μ = 0 := by convert eLpNorm_zero (F := F)

@[deprecated (since := "2024-07-27")]
alias snorm_zero' := eLpNorm_zero'

theorem zero_memℒp : Memℒp (0 : α → E) p μ :=
  ⟨aestronglyMeasurable_zero, by
    rw [eLpNorm_zero]
    exact ENNReal.coe_lt_top⟩

theorem zero_mem_ℒp' : Memℒp (fun _ : α => (0 : E)) p μ := zero_memℒp (E := E)

variable [MeasurableSpace α]

theorem eLpNorm'_measure_zero_of_pos {f : α → F} (hq_pos : 0 < q) :
    eLpNorm' f q (0 : Measure α) = 0 := by simp [eLpNorm', hq_pos]

@[deprecated (since := "2024-07-27")]
alias snorm'_measure_zero_of_pos := eLpNorm'_measure_zero_of_pos

theorem eLpNorm'_measure_zero_of_exponent_zero {f : α → F} : eLpNorm' f 0 (0 : Measure α) = 1 := by
  simp [eLpNorm']

@[deprecated (since := "2024-07-27")]
alias snorm'_measure_zero_of_exponent_zero := eLpNorm'_measure_zero_of_exponent_zero

theorem eLpNorm'_measure_zero_of_neg {f : α → F} (hq_neg : q < 0) :
    eLpNorm' f q (0 : Measure α) = ∞ := by simp [eLpNorm', hq_neg]

@[deprecated (since := "2024-07-27")]
alias snorm'_measure_zero_of_neg := eLpNorm'_measure_zero_of_neg

@[simp]
theorem eLpNormEssSup_measure_zero {f : α → F} : eLpNormEssSup f (0 : Measure α) = 0 := by
  simp [eLpNormEssSup]

@[deprecated (since := "2024-07-27")]
alias snormEssSup_measure_zero := eLpNormEssSup_measure_zero

@[simp]
theorem eLpNorm_measure_zero {f : α → F} : eLpNorm f p (0 : Measure α) = 0 := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp [h_top]
  rw [← Ne] at h0
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm', ENNReal.toReal_pos h0 h_top]

@[deprecated (since := "2024-07-27")]
alias snorm_measure_zero := eLpNorm_measure_zero

end Zero

section Neg

@[simp]
theorem eLpNorm'_neg {f : α → F} : eLpNorm' (-f) q μ = eLpNorm' f q μ := by simp [eLpNorm']

@[deprecated (since := "2024-07-27")]
alias snorm'_neg := eLpNorm'_neg

@[simp]
theorem eLpNorm_neg {f : α → F} : eLpNorm (-f) p μ = eLpNorm f p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp [h_top, eLpNormEssSup]
  simp [eLpNorm_eq_eLpNorm' h0 h_top]

@[deprecated (since := "2024-07-27")]
alias snorm_neg := eLpNorm_neg

theorem Memℒp.neg {f : α → E} (hf : Memℒp f p μ) : Memℒp (-f) p μ :=
  ⟨AEStronglyMeasurable.neg hf.1, by simp [hf.right]⟩

theorem memℒp_neg_iff {f : α → E} : Memℒp (-f) p μ ↔ Memℒp f p μ :=
  ⟨fun h => neg_neg f ▸ h.neg, Memℒp.neg⟩

end Neg

theorem eLpNorm_indicator_eq_restrict {f : α → E} {s : Set α} (hs : MeasurableSet s) :
    eLpNorm (s.indicator f) p μ = eLpNorm f p (μ.restrict s) := by
  rcases eq_or_ne p ∞ with rfl | hp
  · simp only [eLpNorm_exponent_top, eLpNormEssSup,
      ← ENNReal.essSup_indicator_eq_essSup_restrict hs, ENNReal.coe_indicator,
      nnnorm_indicator_eq_indicator_nnnorm]
  · rcases eq_or_ne p 0 with rfl | hp₀; · simp
    simp only [eLpNorm_eq_lintegral_rpow_nnnorm hp₀ hp, ← lintegral_indicator _ hs,
      ENNReal.coe_indicator, nnnorm_indicator_eq_indicator_nnnorm]
    congr with x
    by_cases hx : x ∈ s <;> simp [ENNReal.toReal_pos, *]

@[deprecated (since := "2024-07-27")]
alias snorm_indicator_eq_restrict := eLpNorm_indicator_eq_restrict

section Const

theorem eLpNorm'_const (c : F) (hq_pos : 0 < q) :
    eLpNorm' (fun _ : α => c) q μ = (‖c‖₊ : ℝ≥0∞) * μ Set.univ ^ (1 / q) := by
  rw [eLpNorm', lintegral_const, ENNReal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 ≤ 1 / q)]
  congr
  rw [← ENNReal.rpow_mul]
  suffices hq_cancel : q * (1 / q) = 1 by rw [hq_cancel, ENNReal.rpow_one]
  rw [one_div, mul_inv_cancel₀ (ne_of_lt hq_pos).symm]

@[deprecated (since := "2024-07-27")]
alias snorm'_const := eLpNorm'_const

theorem eLpNorm'_const' [IsFiniteMeasure μ] (c : F) (hc_ne_zero : c ≠ 0) (hq_ne_zero : q ≠ 0) :
    eLpNorm' (fun _ : α => c) q μ = (‖c‖₊ : ℝ≥0∞) * μ Set.univ ^ (1 / q) := by
  rw [eLpNorm', lintegral_const, ENNReal.mul_rpow_of_ne_top _ (measure_ne_top μ Set.univ)]
  · congr
    rw [← ENNReal.rpow_mul]
    suffices hp_cancel : q * (1 / q) = 1 by rw [hp_cancel, ENNReal.rpow_one]
    rw [one_div, mul_inv_cancel₀ hq_ne_zero]
  · rw [Ne, ENNReal.rpow_eq_top_iff, not_or, not_and_or, not_and_or]
    constructor
    · left
      rwa [ENNReal.coe_eq_zero, nnnorm_eq_zero]
    · exact Or.inl ENNReal.coe_ne_top

@[deprecated (since := "2024-07-27")]
alias snorm'_const' := eLpNorm'_const'

theorem eLpNormEssSup_const (c : F) (hμ : μ ≠ 0) :
    eLpNormEssSup (fun _ : α => c) μ = (‖c‖₊ : ℝ≥0∞) := by rw [eLpNormEssSup, essSup_const _ hμ]

@[deprecated (since := "2024-07-27")]
alias snormEssSup_const := eLpNormEssSup_const

theorem eLpNorm'_const_of_isProbabilityMeasure (c : F) (hq_pos : 0 < q) [IsProbabilityMeasure μ] :
    eLpNorm' (fun _ : α => c) q μ = (‖c‖₊ : ℝ≥0∞) := by simp [eLpNorm'_const c hq_pos, measure_univ]

@[deprecated (since := "2024-07-27")]
alias snorm'_const_of_isProbabilityMeasure := eLpNorm'_const_of_isProbabilityMeasure

theorem eLpNorm_const (c : F) (h0 : p ≠ 0) (hμ : μ ≠ 0) :
    eLpNorm (fun _ : α => c) p μ = (‖c‖₊ : ℝ≥0∞) * μ Set.univ ^ (1 / ENNReal.toReal p) := by
  by_cases h_top : p = ∞
  · simp [h_top, eLpNormEssSup_const c hμ]
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm'_const, ENNReal.toReal_pos h0 h_top]

@[deprecated (since := "2024-07-27")]
alias snorm_const := eLpNorm_const

theorem eLpNorm_const' (c : F) (h0 : p ≠ 0) (h_top : p ≠ ∞) :
    eLpNorm (fun _ : α => c) p μ = (‖c‖₊ : ℝ≥0∞) * μ Set.univ ^ (1 / ENNReal.toReal p) := by
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm'_const, ENNReal.toReal_pos h0 h_top]

@[deprecated (since := "2024-07-27")]
alias snorm_const' := eLpNorm_const'

theorem eLpNorm_const_lt_top_iff {p : ℝ≥0∞} {c : F} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    eLpNorm (fun _ : α => c) p μ < ∞ ↔ c = 0 ∨ μ Set.univ < ∞ := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  by_cases hμ : μ = 0
  · simp only [hμ, Measure.coe_zero, Pi.zero_apply, or_true_iff, ENNReal.zero_lt_top,
      eLpNorm_measure_zero]
  by_cases hc : c = 0
  · simp only [hc, true_or_iff, eq_self_iff_true, ENNReal.zero_lt_top, eLpNorm_zero']
  rw [eLpNorm_const' c hp_ne_zero hp_ne_top]
  by_cases hμ_top : μ Set.univ = ∞
  · simp [hc, hμ_top, hp]
  rw [ENNReal.mul_lt_top_iff]
  simp only [true_and_iff, one_div, ENNReal.rpow_eq_zero_iff, hμ, false_or_iff, or_false_iff,
    ENNReal.coe_lt_top, nnnorm_eq_zero, ENNReal.coe_eq_zero,
    MeasureTheory.Measure.measure_univ_eq_zero, hp, inv_lt_zero, hc, and_false_iff, false_and_iff,
    inv_pos, or_self_iff, hμ_top, Ne.lt_top hμ_top, iff_true_iff]
  exact ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.mpr hp.le) hμ_top

@[deprecated (since := "2024-07-27")]
alias snorm_const_lt_top_iff := eLpNorm_const_lt_top_iff

theorem memℒp_const (c : E) [IsFiniteMeasure μ] : Memℒp (fun _ : α => c) p μ := by
  refine ⟨aestronglyMeasurable_const, ?_⟩
  by_cases h0 : p = 0
  · simp [h0]
  by_cases hμ : μ = 0
  · simp [hμ]
  rw [eLpNorm_const c h0 hμ]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  refine ENNReal.rpow_lt_top_of_nonneg ?_ (measure_ne_top μ Set.univ)
  simp

theorem memℒp_top_const (c : E) : Memℒp (fun _ : α => c) ∞ μ := by
  refine ⟨aestronglyMeasurable_const, ?_⟩
  by_cases h : μ = 0
  · simp only [h, eLpNorm_measure_zero, ENNReal.zero_lt_top]
  · rw [eLpNorm_const _ ENNReal.top_ne_zero h]
    simp only [ENNReal.top_toReal, div_zero, ENNReal.rpow_zero, mul_one, ENNReal.coe_lt_top]

theorem memℒp_const_iff {p : ℝ≥0∞} {c : E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    Memℒp (fun _ : α => c) p μ ↔ c = 0 ∨ μ Set.univ < ∞ := by
  rw [← eLpNorm_const_lt_top_iff hp_ne_zero hp_ne_top]
  exact ⟨fun h => h.2, fun h => ⟨aestronglyMeasurable_const, h⟩⟩

end Const

lemma eLpNorm'_mono_nnnorm_ae {f : α → F} {g : α → G} (hq : 0 ≤ q) (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    eLpNorm' f q μ ≤ eLpNorm' g q μ := by
  simp only [eLpNorm']
  gcongr ?_ ^ (1/q)
  refine lintegral_mono_ae (h.mono fun x hx => ?_)
  gcongr

@[deprecated (since := "2024-07-27")]
alias snorm'_mono_nnnorm_ae := eLpNorm'_mono_nnnorm_ae

theorem eLpNorm'_mono_ae {f : α → F} {g : α → G} (hq : 0 ≤ q) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    eLpNorm' f q μ ≤ eLpNorm' g q μ :=
  eLpNorm'_mono_nnnorm_ae hq h

@[deprecated (since := "2024-07-27")]
alias snorm'_mono_ae := eLpNorm'_mono_ae

theorem eLpNorm'_congr_nnnorm_ae {f g : α → F} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊) :
    eLpNorm' f q μ = eLpNorm' g q μ := by
  have : (fun x => (‖f x‖₊ : ℝ≥0∞) ^ q) =ᵐ[μ] fun x => (‖g x‖₊ : ℝ≥0∞) ^ q :=
    hfg.mono fun x hx => by simp_rw [hx]
  simp only [eLpNorm', lintegral_congr_ae this]

@[deprecated (since := "2024-07-27")]
alias snorm'_congr_nnnorm_ae := eLpNorm'_congr_nnnorm_ae

theorem eLpNorm'_congr_norm_ae {f g : α → F} (hfg : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
    eLpNorm' f q μ = eLpNorm' g q μ :=
  eLpNorm'_congr_nnnorm_ae <| hfg.mono fun _x hx => NNReal.eq hx

@[deprecated (since := "2024-07-27")]
alias snorm'_congr_norm_ae := eLpNorm'_congr_norm_ae

theorem eLpNorm'_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : eLpNorm' f q μ = eLpNorm' g q μ :=
  eLpNorm'_congr_nnnorm_ae (hfg.fun_comp _)

@[deprecated (since := "2024-07-27")]
alias snorm'_congr_ae := eLpNorm'_congr_ae

theorem eLpNormEssSup_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) :
    eLpNormEssSup f μ = eLpNormEssSup g μ :=
  essSup_congr_ae (hfg.fun_comp (((↑) : ℝ≥0 → ℝ≥0∞) ∘ nnnorm))

@[deprecated (since := "2024-07-27")]
alias snormEssSup_congr_ae := eLpNormEssSup_congr_ae

theorem eLpNormEssSup_mono_nnnorm_ae {f g : α → F} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    eLpNormEssSup f μ ≤ eLpNormEssSup g μ :=
  essSup_mono_ae <| hfg.mono fun _x hx => ENNReal.coe_le_coe.mpr hx

@[deprecated (since := "2024-07-27")]
alias snormEssSup_mono_nnnorm_ae := eLpNormEssSup_mono_nnnorm_ae

theorem eLpNorm_mono_nnnorm_ae {f : α → F} {g : α → G} (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    eLpNorm f p μ ≤ eLpNorm g p μ := by
  simp only [eLpNorm]
  split_ifs
  · exact le_rfl
  · exact essSup_mono_ae (h.mono fun x hx => ENNReal.coe_le_coe.mpr hx)
  · exact eLpNorm'_mono_nnnorm_ae ENNReal.toReal_nonneg h

@[deprecated (since := "2024-07-27")]
alias snorm_mono_nnnorm_ae := eLpNorm_mono_nnnorm_ae

theorem eLpNorm_mono_ae {f : α → F} {g : α → G} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_nnnorm_ae h

@[deprecated (since := "2024-07-27")]
alias snorm_mono_ae := eLpNorm_mono_ae

theorem eLpNorm_mono_ae_real {f : α → F} {g : α → ℝ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_ae <| h.mono fun _x hx =>
    hx.trans ((le_abs_self _).trans (Real.norm_eq_abs _).symm.le)

@[deprecated (since := "2024-07-27")]
alias snorm_mono_ae_real := eLpNorm_mono_ae_real

theorem eLpNorm_mono_nnnorm {f : α → F} {g : α → G} (h : ∀ x, ‖f x‖₊ ≤ ‖g x‖₊) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_nnnorm_ae (Eventually.of_forall fun x => h x)

@[deprecated (since := "2024-07-27")]
alias snorm_mono_nnnorm := eLpNorm_mono_nnnorm

theorem eLpNorm_mono {f : α → F} {g : α → G} (h : ∀ x, ‖f x‖ ≤ ‖g x‖) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_ae (Eventually.of_forall fun x => h x)

@[deprecated (since := "2024-07-27")]
alias snorm_mono := eLpNorm_mono

theorem eLpNorm_mono_real {f : α → F} {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_ae_real (Eventually.of_forall fun x => h x)

@[deprecated (since := "2024-07-27")]
alias snorm_mono_real := eLpNorm_mono_real

theorem eLpNormEssSup_le_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    eLpNormEssSup f μ ≤ C :=
  essSup_le_of_ae_le (C : ℝ≥0∞) <| hfC.mono fun _x hx => ENNReal.coe_le_coe.mpr hx

@[deprecated (since := "2024-07-27")]
alias snormEssSup_le_of_ae_nnnorm_bound := eLpNormEssSup_le_of_ae_nnnorm_bound

theorem eLpNormEssSup_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    eLpNormEssSup f μ ≤ ENNReal.ofReal C :=
  eLpNormEssSup_le_of_ae_nnnorm_bound <| hfC.mono fun _x hx => hx.trans C.le_coe_toNNReal

@[deprecated (since := "2024-07-27")]
alias snormEssSup_le_of_ae_bound := eLpNormEssSup_le_of_ae_bound

theorem eLpNormEssSup_lt_top_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    eLpNormEssSup f μ < ∞ :=
  (eLpNormEssSup_le_of_ae_nnnorm_bound hfC).trans_lt ENNReal.coe_lt_top

@[deprecated (since := "2024-07-27")]
alias snormEssSup_lt_top_of_ae_nnnorm_bound := eLpNormEssSup_lt_top_of_ae_nnnorm_bound

theorem eLpNormEssSup_lt_top_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    eLpNormEssSup f μ < ∞ :=
  (eLpNormEssSup_le_of_ae_bound hfC).trans_lt ENNReal.ofReal_lt_top

@[deprecated (since := "2024-07-27")]
alias snormEssSup_lt_top_of_ae_bound := eLpNormEssSup_lt_top_of_ae_bound

theorem eLpNorm_le_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    eLpNorm f p μ ≤ C • μ Set.univ ^ p.toReal⁻¹ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  by_cases hp : p = 0
  · simp [hp]
  have : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖(C : ℝ)‖₊ := hfC.mono fun x hx => hx.trans_eq C.nnnorm_eq.symm
  refine (eLpNorm_mono_ae this).trans_eq ?_
  rw [eLpNorm_const _ hp (NeZero.ne μ), C.nnnorm_eq, one_div, ENNReal.smul_def, smul_eq_mul]

@[deprecated (since := "2024-07-27")]
alias snorm_le_of_ae_nnnorm_bound := eLpNorm_le_of_ae_nnnorm_bound

theorem eLpNorm_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    eLpNorm f p μ ≤ μ Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal C := by
  rw [← mul_comm]
  exact eLpNorm_le_of_ae_nnnorm_bound (hfC.mono fun x hx => hx.trans C.le_coe_toNNReal)

@[deprecated (since := "2024-07-27")]
alias snorm_le_of_ae_bound := eLpNorm_le_of_ae_bound

theorem eLpNorm_congr_nnnorm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊) :
    eLpNorm f p μ = eLpNorm g p μ :=
  le_antisymm (eLpNorm_mono_nnnorm_ae <| EventuallyEq.le hfg)
    (eLpNorm_mono_nnnorm_ae <| (EventuallyEq.symm hfg).le)

@[deprecated (since := "2024-07-27")]
alias snorm_congr_nnnorm_ae := eLpNorm_congr_nnnorm_ae

theorem eLpNorm_congr_norm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
    eLpNorm f p μ = eLpNorm g p μ :=
  eLpNorm_congr_nnnorm_ae <| hfg.mono fun _x hx => NNReal.eq hx

@[deprecated (since := "2024-07-27")]
alias snorm_congr_norm_ae := eLpNorm_congr_norm_ae

open scoped symmDiff in
theorem eLpNorm_indicator_sub_indicator (s t : Set α) (f : α → E) :
    eLpNorm (s.indicator f - t.indicator f) p μ = eLpNorm ((s ∆ t).indicator f) p μ :=
  eLpNorm_congr_norm_ae <| ae_of_all _ fun x ↦ by
    simp only [Pi.sub_apply, Set.apply_indicator_symmDiff norm_neg]

@[deprecated (since := "2024-07-27")]
alias snorm_indicator_sub_indicator := eLpNorm_indicator_sub_indicator

@[simp]
theorem eLpNorm'_norm {f : α → F} :
    eLpNorm' (fun a => ‖f a‖) q μ = eLpNorm' f q μ := by simp [eLpNorm']

@[deprecated (since := "2024-07-27")]
alias snorm'_norm := eLpNorm'_norm

@[simp]
theorem eLpNorm_norm (f : α → F) : eLpNorm (fun x => ‖f x‖) p μ = eLpNorm f p μ :=
  eLpNorm_congr_norm_ae <| Eventually.of_forall fun _ => norm_norm _

@[deprecated (since := "2024-07-27")]
alias snorm_norm := eLpNorm_norm

theorem eLpNorm'_norm_rpow (f : α → F) (p q : ℝ) (hq_pos : 0 < q) :
    eLpNorm' (fun x => ‖f x‖ ^ q) p μ = eLpNorm' f (p * q) μ ^ q := by
  simp_rw [eLpNorm']
  rw [← ENNReal.rpow_mul, ← one_div_mul_one_div]
  simp_rw [one_div]
  rw [mul_assoc, inv_mul_cancel₀ hq_pos.ne.symm, mul_one]
  congr
  ext1 x
  simp_rw [← ofReal_norm_eq_coe_nnnorm]
  rw [Real.norm_eq_abs, abs_eq_self.mpr (Real.rpow_nonneg (norm_nonneg _) _), mul_comm, ←
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq_pos.le, ENNReal.rpow_mul]

@[deprecated (since := "2024-07-27")]
alias snorm'_norm_rpow := eLpNorm'_norm_rpow

theorem eLpNorm_norm_rpow (f : α → F) (hq_pos : 0 < q) :
    eLpNorm (fun x => ‖f x‖ ^ q) p μ = eLpNorm f (p * ENNReal.ofReal q) μ ^ q := by
  by_cases h0 : p = 0
  · simp [h0, ENNReal.zero_rpow_of_pos hq_pos]
  by_cases hp_top : p = ∞
  · simp only [hp_top, eLpNorm_exponent_top, ENNReal.top_mul', hq_pos.not_le,
      ENNReal.ofReal_eq_zero, if_false, eLpNorm_exponent_top, eLpNormEssSup]
    have h_rpow :
      essSup (fun x : α => (‖‖f x‖ ^ q‖₊ : ℝ≥0∞)) μ =
        essSup (fun x : α => (‖f x‖₊ : ℝ≥0∞) ^ q) μ := by
      congr
      ext1 x
      conv_rhs => rw [← nnnorm_norm]
      rw [← ENNReal.coe_rpow_of_nonneg _ hq_pos.le, ENNReal.coe_inj]
      ext
      push_cast
      rw [Real.norm_rpow_of_nonneg (norm_nonneg _)]
    rw [h_rpow]
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos hq_pos
    have h_rpow_surj := (ENNReal.rpow_left_bijective hq_pos.ne.symm).2
    let iso := h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj
    exact (iso.essSup_apply (fun x => (‖f x‖₊ : ℝ≥0∞)) μ).symm
  rw [eLpNorm_eq_eLpNorm' h0 hp_top, eLpNorm_eq_eLpNorm' _ _]
  swap
  · refine mul_ne_zero h0 ?_
    rwa [Ne, ENNReal.ofReal_eq_zero, not_le]
  swap; · exact ENNReal.mul_ne_top hp_top ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq_pos.le]
  exact eLpNorm'_norm_rpow f p.toReal q hq_pos

@[deprecated (since := "2024-07-27")]
alias snorm_norm_rpow := eLpNorm_norm_rpow

theorem eLpNorm_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ :=
  eLpNorm_congr_norm_ae <| hfg.mono fun _x hx => hx ▸ rfl

@[deprecated (since := "2024-07-27")]
alias snorm_congr_ae := eLpNorm_congr_ae

theorem memℒp_congr_ae {f g : α → E} (hfg : f =ᵐ[μ] g) : Memℒp f p μ ↔ Memℒp g p μ := by
  simp only [Memℒp, eLpNorm_congr_ae hfg, aestronglyMeasurable_congr hfg]

theorem Memℒp.ae_eq {f g : α → E} (hfg : f =ᵐ[μ] g) (hf_Lp : Memℒp f p μ) : Memℒp g p μ :=
  (memℒp_congr_ae hfg).1 hf_Lp

theorem Memℒp.of_le {f : α → E} {g : α → F} (hg : Memℒp g p μ) (hf : AEStronglyMeasurable f μ)
    (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) : Memℒp f p μ :=
  ⟨hf, (eLpNorm_mono_ae hfg).trans_lt hg.eLpNorm_lt_top⟩

alias Memℒp.mono := Memℒp.of_le

theorem Memℒp.mono' {f : α → E} {g : α → ℝ} (hg : Memℒp g p μ) (hf : AEStronglyMeasurable f μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : Memℒp f p μ :=
  hg.mono hf <| h.mono fun _x hx => le_trans hx (le_abs_self _)

theorem Memℒp.congr_norm {f : α → E} {g : α → F} (hf : Memℒp f p μ) (hg : AEStronglyMeasurable g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) : Memℒp g p μ :=
  hf.mono hg <| EventuallyEq.le <| EventuallyEq.symm h

theorem memℒp_congr_norm {f : α → E} {g : α → F} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) : Memℒp f p μ ↔ Memℒp g p μ :=
  ⟨fun h2f => h2f.congr_norm hg h, fun h2g => h2g.congr_norm hf <| EventuallyEq.symm h⟩

theorem memℒp_top_of_bound {f : α → E} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : Memℒp f ∞ μ :=
  ⟨hf, by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_lt_top_of_ae_bound hfC⟩

theorem Memℒp.of_bound [IsFiniteMeasure μ] {f : α → E} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : Memℒp f p μ :=
  (memℒp_const C).of_le hf (hfC.mono fun _x hx => le_trans hx (le_abs_self _))

@[mono]
theorem eLpNorm'_mono_measure (f : α → F) (hμν : ν ≤ μ) (hq : 0 ≤ q) :
    eLpNorm' f q ν ≤ eLpNorm' f q μ := by
  simp_rw [eLpNorm']
  gcongr
  exact lintegral_mono' hμν le_rfl

@[deprecated (since := "2024-07-27")]
alias snorm'_mono_measure := eLpNorm'_mono_measure

@[mono]
theorem eLpNormEssSup_mono_measure (f : α → F) (hμν : ν ≪ μ) :
    eLpNormEssSup f ν ≤ eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup]
  exact essSup_mono_measure hμν

@[deprecated (since := "2024-07-27")]
alias snormEssSup_mono_measure := eLpNormEssSup_mono_measure

@[mono]
theorem eLpNorm_mono_measure (f : α → F) (hμν : ν ≤ μ) : eLpNorm f p ν ≤ eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_mono_measure f (Measure.absolutelyContinuous_of_le hμν)]
  simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  exact eLpNorm'_mono_measure f hμν ENNReal.toReal_nonneg

@[deprecated (since := "2024-07-27")]
alias snorm_mono_measure := eLpNorm_mono_measure

theorem Memℒp.mono_measure {f : α → E} (hμν : ν ≤ μ) (hf : Memℒp f p μ) : Memℒp f p ν :=
  ⟨hf.1.mono_measure hμν, (eLpNorm_mono_measure f hμν).trans_lt hf.2⟩

lemma eLpNorm_restrict_le (f : α → F) (p : ℝ≥0∞) (μ : Measure α) (s : Set α) :
    eLpNorm f p (μ.restrict s) ≤ eLpNorm f p μ :=
  eLpNorm_mono_measure f Measure.restrict_le_self

@[deprecated (since := "2024-07-27")]
alias snorm_restrict_le := eLpNorm_restrict_le

/-- For a function `f` with support in `s`, the Lᵖ norms of `f` with respect to `μ` and
`μ.restrict s` are the same. -/
theorem eLpNorm_restrict_eq_of_support_subset {s : Set α} {f : α → F} (hsf : f.support ⊆ s) :
    eLpNorm f p (μ.restrict s) = eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp only [hp_top, eLpNorm_exponent_top, eLpNormEssSup]
    apply ENNReal.essSup_restrict_eq_of_support_subset
    apply Function.support_subset_iff.2 (fun x hx ↦ ?_)
    simp only [ne_eq, ENNReal.coe_eq_zero, nnnorm_eq_zero] at hx
    exact Function.support_subset_iff.1 hsf x hx
  · simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top, eLpNorm']
    congr 1
    apply setLIntegral_eq_of_support_subset
    have : ¬(p.toReal ≤ 0) := by simpa only [not_le] using ENNReal.toReal_pos hp0 hp_top
    simpa [this] using hsf

@[deprecated (since := "2024-07-27")]
alias snorm_restrict_eq_of_support_subset := eLpNorm_restrict_eq_of_support_subset

theorem Memℒp.restrict (s : Set α) {f : α → E} (hf : Memℒp f p μ) : Memℒp f p (μ.restrict s) :=
  hf.mono_measure Measure.restrict_le_self

theorem eLpNorm'_smul_measure {p : ℝ} (hp : 0 ≤ p) {f : α → F} (c : ℝ≥0∞) :
    eLpNorm' f p (c • μ) = c ^ (1 / p) * eLpNorm' f p μ := by
  rw [eLpNorm', lintegral_smul_measure, ENNReal.mul_rpow_of_nonneg, eLpNorm']
  simp [hp]

@[deprecated (since := "2024-07-27")]
alias snorm'_smul_measure := eLpNorm'_smul_measure

theorem eLpNormEssSup_smul_measure {f : α → F} {c : ℝ≥0∞} (hc : c ≠ 0) :
    eLpNormEssSup f (c • μ) = eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup]
  exact essSup_smul_measure hc

@[deprecated (since := "2024-07-27")]
alias snormEssSup_smul_measure := eLpNormEssSup_smul_measure

/-- Use `eLpNorm_smul_measure_of_ne_top` instead. -/
private theorem eLpNorm_smul_measure_of_ne_zero_of_ne_top {p : ℝ≥0∞} (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) {f : α → F} (c : ℝ≥0∞) :
    eLpNorm f p (c • μ) = c ^ (1 / p).toReal • eLpNorm f p μ := by
  simp_rw [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top]
  rw [eLpNorm'_smul_measure ENNReal.toReal_nonneg]
  congr
  simp_rw [one_div]
  rw [ENNReal.toReal_inv]

@[deprecated (since := "2024-07-27")]
alias snorm_smul_measure_of_ne_zero_of_ne_top := eLpNorm_smul_measure_of_ne_zero_of_ne_top

theorem eLpNorm_smul_measure_of_ne_zero {p : ℝ≥0∞} {f : α → F} {c : ℝ≥0∞} (hc : c ≠ 0) :
    eLpNorm f p (c • μ) = c ^ (1 / p).toReal • eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_smul_measure hc]
  exact eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_top c

@[deprecated (since := "2024-07-27")]
alias snorm_smul_measure_of_ne_zero := eLpNorm_smul_measure_of_ne_zero

theorem eLpNorm_smul_measure_of_ne_top {p : ℝ≥0∞} (hp_ne_top : p ≠ ∞) {f : α → F} (c : ℝ≥0∞) :
    eLpNorm f p (c • μ) = c ^ (1 / p).toReal • eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_ne_top c

@[deprecated (since := "2024-07-27")]
alias snorm_smul_measure_of_ne_top := eLpNorm_smul_measure_of_ne_top

theorem eLpNorm_one_smul_measure {f : α → F} (c : ℝ≥0∞) :
    eLpNorm f 1 (c • μ) = c * eLpNorm f 1 μ := by
  rw [@eLpNorm_smul_measure_of_ne_top _ _ _ μ _ 1 (@ENNReal.coe_ne_top 1) f c]
  simp

@[deprecated (since := "2024-07-27")]
alias snorm_one_smul_measure := eLpNorm_one_smul_measure

theorem Memℒp.of_measure_le_smul {μ' : Measure α} (c : ℝ≥0∞) (hc : c ≠ ∞) (hμ'_le : μ' ≤ c • μ)
    {f : α → E} (hf : Memℒp f p μ) : Memℒp f p μ' := by
  refine ⟨hf.1.mono_ac (Measure.absolutelyContinuous_of_le_smul hμ'_le), ?_⟩
  refine (eLpNorm_mono_measure f hμ'_le).trans_lt ?_
  by_cases hc0 : c = 0
  · simp [hc0]
  rw [eLpNorm_smul_measure_of_ne_zero hc0, smul_eq_mul]
  refine ENNReal.mul_lt_top (Ne.lt_top ?_) hf.2
  simp [hc, hc0]

theorem Memℒp.smul_measure {f : α → E} {c : ℝ≥0∞} (hf : Memℒp f p μ) (hc : c ≠ ∞) :
    Memℒp f p (c • μ) :=
  hf.of_measure_le_smul c hc le_rfl

theorem eLpNorm_one_add_measure (f : α → F) (μ ν : Measure α) :
    eLpNorm f 1 (μ + ν) = eLpNorm f 1 μ + eLpNorm f 1 ν := by
  simp_rw [eLpNorm_one_eq_lintegral_nnnorm]
  rw [lintegral_add_measure _ μ ν]

@[deprecated (since := "2024-07-27")]
alias snorm_one_add_measure := eLpNorm_one_add_measure

theorem eLpNorm_le_add_measure_right (f : α → F) (μ ν : Measure α) {p : ℝ≥0∞} :
    eLpNorm f p μ ≤ eLpNorm f p (μ + ν) :=
  eLpNorm_mono_measure f <| Measure.le_add_right <| le_refl _

@[deprecated (since := "2024-07-27")]
alias snorm_le_add_measure_right := eLpNorm_le_add_measure_right

theorem eLpNorm_le_add_measure_left (f : α → F) (μ ν : Measure α) {p : ℝ≥0∞} :
    eLpNorm f p ν ≤ eLpNorm f p (μ + ν) :=
  eLpNorm_mono_measure f <| Measure.le_add_left <| le_refl _

@[deprecated (since := "2024-07-27")]
alias snorm_le_add_measure_left := eLpNorm_le_add_measure_left

lemma eLpNormEssSup_eq_iSup (hμ : ∀ a, μ {a} ≠ 0) (f : α → E) : eLpNormEssSup f μ = ⨆ a, ↑‖f a‖₊ :=
  essSup_eq_iSup hμ _

@[simp] lemma eLpNormEssSup_count [MeasurableSingletonClass α] (f : α → E) :
    eLpNormEssSup f .count = ⨆ a, ↑‖f a‖₊ := essSup_count _

theorem Memℒp.left_of_add_measure {f : α → E} (h : Memℒp f p (μ + ν)) : Memℒp f p μ :=
  h.mono_measure <| Measure.le_add_right <| le_refl _

theorem Memℒp.right_of_add_measure {f : α → E} (h : Memℒp f p (μ + ν)) : Memℒp f p ν :=
  h.mono_measure <| Measure.le_add_left <| le_refl _

theorem Memℒp.norm {f : α → E} (h : Memℒp f p μ) : Memℒp (fun x => ‖f x‖) p μ :=
  h.of_le h.aestronglyMeasurable.norm (Eventually.of_forall fun x => by simp)

theorem memℒp_norm_iff {f : α → E} (hf : AEStronglyMeasurable f μ) :
    Memℒp (fun x => ‖f x‖) p μ ↔ Memℒp f p μ :=
  ⟨fun h => ⟨hf, by rw [← eLpNorm_norm]; exact h.2⟩, fun h => h.norm⟩

theorem eLpNorm'_eq_zero_of_ae_zero {f : α → F} (hq0_lt : 0 < q) (hf_zero : f =ᵐ[μ] 0) :
    eLpNorm' f q μ = 0 := by rw [eLpNorm'_congr_ae hf_zero, eLpNorm'_zero hq0_lt]

@[deprecated (since := "2024-07-27")]
alias snorm'_eq_zero_of_ae_zero := eLpNorm'_eq_zero_of_ae_zero

theorem eLpNorm'_eq_zero_of_ae_zero' (hq0_ne : q ≠ 0) (hμ : μ ≠ 0) {f : α → F}
    (hf_zero : f =ᵐ[μ] 0) :
    eLpNorm' f q μ = 0 := by rw [eLpNorm'_congr_ae hf_zero, eLpNorm'_zero' hq0_ne hμ]

@[deprecated (since := "2024-07-27")]
alias snorm'_eq_zero_of_ae_zero' := eLpNorm'_eq_zero_of_ae_zero'

theorem ae_eq_zero_of_eLpNorm'_eq_zero {f : α → E} (hq0 : 0 ≤ q) (hf : AEStronglyMeasurable f μ)
    (h : eLpNorm' f q μ = 0) : f =ᵐ[μ] 0 := by
  rw [eLpNorm', ENNReal.rpow_eq_zero_iff] at h
  cases h with
  | inl h =>
    rw [lintegral_eq_zero_iff' (hf.ennnorm.pow_const q)] at h
    refine h.left.mono fun x hx => ?_
    rw [Pi.zero_apply, ENNReal.rpow_eq_zero_iff] at hx
    cases hx with
    | inl hx =>
      cases' hx with hx _
      rwa [← ENNReal.coe_zero, ENNReal.coe_inj, nnnorm_eq_zero] at hx
    | inr hx =>
      exact absurd hx.left ENNReal.coe_ne_top
  | inr h =>
    exfalso
    rw [one_div, inv_lt_zero] at h
    exact hq0.not_lt h.right

@[deprecated (since := "2024-07-27")]
alias ae_eq_zero_of_snorm'_eq_zero := ae_eq_zero_of_eLpNorm'_eq_zero

theorem eLpNorm'_eq_zero_iff (hq0_lt : 0 < q) {f : α → E} (hf : AEStronglyMeasurable f μ) :
    eLpNorm' f q μ = 0 ↔ f =ᵐ[μ] 0 :=
  ⟨ae_eq_zero_of_eLpNorm'_eq_zero (le_of_lt hq0_lt) hf, eLpNorm'_eq_zero_of_ae_zero hq0_lt⟩

@[deprecated (since := "2024-07-27")]
alias snorm'_eq_zero_iff := eLpNorm'_eq_zero_iff

theorem coe_nnnorm_ae_le_eLpNormEssSup {_ : MeasurableSpace α} (f : α → F) (μ : Measure α) :
    ∀ᵐ x ∂μ, (‖f x‖₊ : ℝ≥0∞) ≤ eLpNormEssSup f μ :=
  ENNReal.ae_le_essSup fun x => (‖f x‖₊ : ℝ≥0∞)

@[deprecated (since := "2024-07-27")]
alias coe_nnnorm_ae_le_snormEssSup := coe_nnnorm_ae_le_eLpNormEssSup

@[simp]
theorem eLpNormEssSup_eq_zero_iff {f : α → F} : eLpNormEssSup f μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp [EventuallyEq, eLpNormEssSup]

@[deprecated (since := "2024-07-27")]
alias snormEssSup_eq_zero_iff := eLpNormEssSup_eq_zero_iff

theorem eLpNorm_eq_zero_iff {f : α → E} (hf : AEStronglyMeasurable f μ) (h0 : p ≠ 0) :
    eLpNorm f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  by_cases h_top : p = ∞
  · rw [h_top, eLpNorm_exponent_top, eLpNormEssSup_eq_zero_iff]
  rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_eq_zero_iff (ENNReal.toReal_pos h0 h_top) hf

@[deprecated (since := "2024-07-27")]
alias snorm_eq_zero_iff := eLpNorm_eq_zero_iff

theorem eLpNorm_eq_zero_of_ae_zero {f : α → E} (hf : f =ᵐ[μ] 0) : eLpNorm f p μ = 0 := by
  rw [← eLpNorm_zero (p := p) (μ := μ) (α := α) (F := E)]
  exact eLpNorm_congr_ae hf

theorem ae_le_eLpNormEssSup {f : α → F} : ∀ᵐ y ∂μ, ‖f y‖₊ ≤ eLpNormEssSup f μ :=
  ae_le_essSup

@[deprecated (since := "2024-07-27")]
alias ae_le_snormEssSup := ae_le_eLpNormEssSup

theorem meas_eLpNormEssSup_lt {f : α → F} : μ { y | eLpNormEssSup f μ < ‖f y‖₊ } = 0 :=
  meas_essSup_lt

@[deprecated (since := "2024-07-27")]
alias meas_snormEssSup_lt := meas_eLpNormEssSup_lt

lemma eLpNormEssSup_piecewise {s : Set α} (f g : α → E) [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) :
    eLpNormEssSup (Set.piecewise s f g) μ
      = max (eLpNormEssSup f (μ.restrict s)) (eLpNormEssSup g (μ.restrict sᶜ)) := by
  simp only [eLpNormEssSup, ← ENNReal.essSup_piecewise hs]
  congr with x
  by_cases hx : x ∈ s <;> simp [hx]

@[deprecated (since := "2024-07-27")]
alias snormEssSup_piecewise := eLpNormEssSup_piecewise

lemma eLpNorm_top_piecewise {s : Set α} (f g : α → E) [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) :
    eLpNorm (Set.piecewise s f g) ∞ μ
      = max (eLpNorm f ∞ (μ.restrict s)) (eLpNorm g ∞ (μ.restrict sᶜ)) :=
  eLpNormEssSup_piecewise f g hs

@[deprecated (since := "2024-07-27")]
alias snorm_top_piecewise := eLpNorm_top_piecewise

section MapMeasure

variable {β : Type*} {mβ : MeasurableSpace β} {f : α → β} {g : β → E}

theorem eLpNormEssSup_map_measure (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : eLpNormEssSup g (Measure.map f μ) = eLpNormEssSup (g ∘ f) μ :=
  essSup_map_measure hg.ennnorm hf

@[deprecated (since := "2024-07-27")]
alias snormEssSup_map_measure := eLpNormEssSup_map_measure

theorem eLpNorm_map_measure (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : eLpNorm g p (Measure.map f μ) = eLpNorm (g ∘ f) p μ := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, eLpNorm_exponent_top]
    exact eLpNormEssSup_map_measure hg hf
  simp_rw [eLpNorm_eq_lintegral_rpow_nnnorm hp_zero hp_top]
  rw [lintegral_map' (hg.ennnorm.pow_const p.toReal) hf]
  rfl

@[deprecated (since := "2024-07-27")]
alias snorm_map_measure := eLpNorm_map_measure

theorem memℒp_map_measure_iff (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : Memℒp g p (Measure.map f μ) ↔ Memℒp (g ∘ f) p μ := by
  simp [Memℒp, eLpNorm_map_measure hg hf, hg.comp_aemeasurable hf, hg]

theorem Memℒp.comp_of_map (hg : Memℒp g p (Measure.map f μ)) (hf : AEMeasurable f μ) :
    Memℒp (g ∘ f) p μ :=
  (memℒp_map_measure_iff hg.aestronglyMeasurable hf).1 hg

theorem eLpNorm_comp_measurePreserving {ν : MeasureTheory.Measure β} (hg : AEStronglyMeasurable g ν)
    (hf : MeasurePreserving f μ ν) : eLpNorm (g ∘ f) p μ = eLpNorm g p ν :=
  Eq.symm <| hf.map_eq ▸ eLpNorm_map_measure (hf.map_eq ▸ hg) hf.aemeasurable

@[deprecated (since := "2024-07-27")]
alias snorm_comp_measurePreserving := eLpNorm_comp_measurePreserving

theorem AEEqFun.eLpNorm_compMeasurePreserving {ν : MeasureTheory.Measure β} (g : β →ₘ[ν] E)
    (hf : MeasurePreserving f μ ν) :
    eLpNorm (g.compMeasurePreserving f hf) p μ = eLpNorm g p ν := by
  rw [eLpNorm_congr_ae (g.coeFn_compMeasurePreserving _)]
  exact eLpNorm_comp_measurePreserving g.aestronglyMeasurable hf

@[deprecated (since := "2024-07-27")]
alias AEEqFun.snorm_compMeasurePreserving := AEEqFun.eLpNorm_compMeasurePreserving

theorem Memℒp.comp_measurePreserving {ν : MeasureTheory.Measure β} (hg : Memℒp g p ν)
    (hf : MeasurePreserving f μ ν) : Memℒp (g ∘ f) p μ :=
  .comp_of_map (hf.map_eq.symm ▸ hg) hf.aemeasurable

theorem _root_.MeasurableEmbedding.eLpNormEssSup_map_measure {g : β → F}
    (hf : MeasurableEmbedding f) : eLpNormEssSup g (Measure.map f μ) = eLpNormEssSup (g ∘ f) μ :=
  hf.essSup_map_measure

@[deprecated (since := "2024-07-27")]
alias _root_.MeasurableEmbedding.snormEssSup_map_measure :=
  _root_.MeasurableEmbedding.eLpNormEssSup_map_measure

theorem _root_.MeasurableEmbedding.eLpNorm_map_measure {g : β → F} (hf : MeasurableEmbedding f) :
    eLpNorm g p (Measure.map f μ) = eLpNorm (g ∘ f) p μ := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp : p = ∞
  · simp_rw [hp, eLpNorm_exponent_top]
    exact hf.essSup_map_measure
  · simp_rw [eLpNorm_eq_lintegral_rpow_nnnorm hp_zero hp]
    rw [hf.lintegral_map]
    rfl

@[deprecated (since := "2024-07-27")]
alias _root_.MeasurableEmbedding.snorm_map_measure := _root_.MeasurableEmbedding.eLpNorm_map_measure

theorem _root_.MeasurableEmbedding.memℒp_map_measure_iff {g : β → F} (hf : MeasurableEmbedding f) :
    Memℒp g p (Measure.map f μ) ↔ Memℒp (g ∘ f) p μ := by
  simp_rw [Memℒp, hf.aestronglyMeasurable_map_iff, hf.eLpNorm_map_measure]

theorem _root_.MeasurableEquiv.memℒp_map_measure_iff (f : α ≃ᵐ β) {g : β → F} :
    Memℒp g p (Measure.map f μ) ↔ Memℒp (g ∘ f) p μ :=
  f.measurableEmbedding.memℒp_map_measure_iff

end MapMeasure

section Monotonicity

theorem eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) {p : ℝ} (hp : 0 < p) :
    eLpNorm' f p μ ≤ c • eLpNorm' g p μ := by
  simp_rw [eLpNorm']
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.smul_def, smul_eq_mul,
    ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne.symm, ENNReal.rpow_one,
    ← ENNReal.coe_rpow_of_nonneg _ hp.le, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top, ←
    ENNReal.coe_mul]
  apply lintegral_mono_ae
  simp_rw [ENNReal.coe_le_coe, ← NNReal.mul_rpow, NNReal.rpow_le_rpow_iff hp]
  exact h

@[deprecated (since := "2024-07-27")]
alias snorm'_le_nnreal_smul_snorm'_of_ae_le_mul := eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul

theorem eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : eLpNormEssSup f μ ≤ c • eLpNormEssSup g μ :=
  calc
    essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ ≤ essSup (fun x => (↑(c * ‖g x‖₊) : ℝ≥0∞)) μ :=
      essSup_mono_ae <| h.mono fun x hx => ENNReal.coe_le_coe.mpr hx
    _ = essSup (fun x => (c * ‖g x‖₊ : ℝ≥0∞)) μ := by simp_rw [ENNReal.coe_mul]
    _ = c • essSup (fun x => (‖g x‖₊ : ℝ≥0∞)) μ := ENNReal.essSup_const_mul

@[deprecated (since := "2024-07-27")]
alias snormEssSup_le_nnreal_smul_snormEssSup_of_ae_le_mul :=
  eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul

theorem eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) (p : ℝ≥0∞) : eLpNorm f p μ ≤ c • eLpNorm g p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · rw [h_top]
    exact eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul h
  simp_rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul h (ENNReal.toReal_pos h0 h_top)

@[deprecated (since := "2024-07-27")]
alias snorm_le_nnreal_smul_snorm_of_ae_le_mul := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul

-- TODO: add the whole family of lemmas?
private theorem le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg {α} [LinearOrderedSemiring α]
    {a b c : α} (ha : 0 ≤ a) (hb : b < 0) (hc : 0 ≤ c) : a ≤ b * c ↔ a = 0 ∧ c = 0 := by
  constructor
  · intro h
    exact
      ⟨(h.trans (mul_nonpos_of_nonpos_of_nonneg hb.le hc)).antisymm ha,
        (nonpos_of_mul_nonneg_right (ha.trans h) hb).antisymm hc⟩
  · rintro ⟨rfl, rfl⟩
    rw [mul_zero]

/-- When `c` is negative, `‖f x‖ ≤ c * ‖g x‖` is nonsense and forces both `f` and `g` to have an
`eLpNorm` of `0`. -/
theorem eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg {f : α → F} {g : α → G} {c : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (hc : c < 0) (p : ℝ≥0∞) :
    eLpNorm f p μ = 0 ∧ eLpNorm g p μ = 0 := by
  simp_rw [le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg (norm_nonneg _) hc (norm_nonneg _),
    norm_eq_zero, eventually_and] at h
  change f =ᵐ[μ] 0 ∧ g =ᵐ[μ] 0 at h
  simp [eLpNorm_congr_ae h.1, eLpNorm_congr_ae h.2]

@[deprecated (since := "2024-07-27")]
alias snorm_eq_zero_and_zero_of_ae_le_mul_neg := eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg

theorem eLpNorm_le_mul_eLpNorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (p : ℝ≥0∞) :
    eLpNorm f p μ ≤ ENNReal.ofReal c * eLpNorm g p μ :=
  eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (h.mono fun _x hx => hx.trans <| mul_le_mul_of_nonneg_right c.le_coe_toNNReal (norm_nonneg _)) _

@[deprecated (since := "2024-07-27")]
alias snorm_le_mul_snorm_of_ae_le_mul := eLpNorm_le_mul_eLpNorm_of_ae_le_mul

theorem Memℒp.of_nnnorm_le_mul {f : α → E} {g : α → F} {c : ℝ≥0} (hg : Memℒp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : Memℒp f p μ :=
  ⟨hf,
    (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hfg p).trans_lt <|
      ENNReal.mul_lt_top ENNReal.coe_lt_top hg.eLpNorm_lt_top⟩

theorem Memℒp.of_le_mul {f : α → E} {g : α → F} {c : ℝ} (hg : Memℒp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : Memℒp f p μ :=
  ⟨hf,
    (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hfg p).trans_lt <|
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top⟩

end Monotonicity

/-!
### Bounded actions by normed rings
In this section we show inequalities on the norm.
-/

section BoundedSMul

variable {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 E] [MulActionWithZero 𝕜 F]
variable [BoundedSMul 𝕜 E] [BoundedSMul 𝕜 F]

theorem eLpNorm'_const_smul_le (c : 𝕜) (f : α → F) (hq_pos : 0 < q) :
    eLpNorm' (c • f) q μ ≤ ‖c‖₊ • eLpNorm' f q μ :=
  eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul (Eventually.of_forall fun _ => nnnorm_smul_le _ _)
    hq_pos

@[deprecated (since := "2024-07-27")]
alias snorm'_const_smul_le := eLpNorm'_const_smul_le

theorem eLpNormEssSup_const_smul_le (c : 𝕜) (f : α → F) :
    eLpNormEssSup (c • f) μ ≤ ‖c‖₊ • eLpNormEssSup f μ :=
  eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul
    (Eventually.of_forall fun _ => by simp [nnnorm_smul_le])

@[deprecated (since := "2024-07-27")]
alias snormEssSup_const_smul_le := eLpNormEssSup_const_smul_le

theorem eLpNorm_const_smul_le (c : 𝕜) (f : α → F) : eLpNorm (c • f) p μ ≤ ‖c‖₊ • eLpNorm f p μ :=
  eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (Eventually.of_forall fun _ => by simp [nnnorm_smul_le]) _

@[deprecated (since := "2024-07-27")]
alias snorm_const_smul_le := eLpNorm_const_smul_le

theorem Memℒp.const_smul {f : α → E} (hf : Memℒp f p μ) (c : 𝕜) : Memℒp (c • f) p μ :=
  ⟨AEStronglyMeasurable.const_smul hf.1 c,
    (eLpNorm_const_smul_le c f).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩

theorem Memℒp.const_mul {R} [NormedRing R] {f : α → R} (hf : Memℒp f p μ) (c : R) :
    Memℒp (fun x => c * f x) p μ :=
  hf.const_smul c

end BoundedSMul

/-!
### Bounded actions by normed division rings
The inequalities in the previous section are now tight.
-/


section NormedSpace

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [MulActionWithZero 𝕜 E] [Module 𝕜 F]
variable [BoundedSMul 𝕜 E] [BoundedSMul 𝕜 F]

theorem eLpNorm'_const_smul {f : α → F} (c : 𝕜) (hq_pos : 0 < q) :
    eLpNorm' (c • f) q μ = ‖c‖₊ • eLpNorm' f q μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp [eLpNorm', hq_pos]
  refine le_antisymm (eLpNorm'_const_smul_le _ _ hq_pos) ?_
  have : eLpNorm' _ q μ ≤ _ := eLpNorm'_const_smul_le c⁻¹ (c • f) hq_pos
  rwa [inv_smul_smul₀ hc, nnnorm_inv, le_inv_smul_iff_of_pos (nnnorm_pos.2 hc)] at this

@[deprecated (since := "2024-07-27")]
alias snorm'_const_smul := eLpNorm'_const_smul

theorem eLpNormEssSup_const_smul (c : 𝕜) (f : α → F) :
    eLpNormEssSup (c • f) μ = (‖c‖₊ : ℝ≥0∞) * eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup, Pi.smul_apply, nnnorm_smul, ENNReal.coe_mul, ENNReal.essSup_const_mul]

@[deprecated (since := "2024-07-27")]
alias snormEssSup_const_smul := eLpNormEssSup_const_smul

theorem eLpNorm_const_smul (c : 𝕜) (f : α → F) :
    eLpNorm (c • f) p μ = (‖c‖₊ : ℝ≥0∞) * eLpNorm f p μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  refine le_antisymm (eLpNorm_const_smul_le _ _) ?_
  have : eLpNorm _ p μ ≤ _ := eLpNorm_const_smul_le c⁻¹ (c • f)
  rwa [inv_smul_smul₀ hc, nnnorm_inv, le_inv_smul_iff_of_pos (nnnorm_pos.2 hc)] at this

@[deprecated (since := "2024-07-27")]
alias snorm_const_smul := eLpNorm_const_smul

end NormedSpace

theorem le_eLpNorm_of_bddBelow (hp : p ≠ 0) (hp' : p ≠ ∞) {f : α → F} (C : ℝ≥0) {s : Set α}
    (hs : MeasurableSet s) (hf : ∀ᵐ x ∂μ, x ∈ s → C ≤ ‖f x‖₊) :
    C • μ s ^ (1 / p.toReal) ≤ eLpNorm f p μ := by
  rw [ENNReal.smul_def, smul_eq_mul, eLpNorm_eq_lintegral_rpow_nnnorm hp hp',
    one_div, ENNReal.le_rpow_inv_iff (ENNReal.toReal_pos hp hp'),
    ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, ← ENNReal.rpow_mul,
    inv_mul_cancel₀ (ENNReal.toReal_pos hp hp').ne.symm, ENNReal.rpow_one, ← setLIntegral_const,
    ← lintegral_indicator _ hs]
  refine lintegral_mono_ae ?_
  filter_upwards [hf] with x hx
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs] at hx ⊢
    gcongr
    exact hx hxs
  · simp [Set.indicator_of_not_mem hxs]

@[deprecated (since := "2024-07-27")]
alias le_snorm_of_bddBelow := le_eLpNorm_of_bddBelow

@[deprecated (since := "2024-06-26")]
alias snorm_indicator_ge_of_bdd_below := le_snorm_of_bddBelow

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜}

theorem Memℒp.re (hf : Memℒp f p μ) : Memℒp (fun x => RCLike.re (f x)) p μ := by
  have : ∀ x, ‖RCLike.re (f x)‖ ≤ 1 * ‖f x‖ := by
    intro x
    rw [one_mul]
    exact RCLike.norm_re_le_norm (f x)
  refine hf.of_le_mul ?_ (Eventually.of_forall this)
  exact RCLike.continuous_re.comp_aestronglyMeasurable hf.1

theorem Memℒp.im (hf : Memℒp f p μ) : Memℒp (fun x => RCLike.im (f x)) p μ := by
  have : ∀ x, ‖RCLike.im (f x)‖ ≤ 1 * ‖f x‖ := by
    intro x
    rw [one_mul]
    exact RCLike.norm_im_le_norm (f x)
  refine hf.of_le_mul ?_ (Eventually.of_forall this)
  exact RCLike.continuous_im.comp_aestronglyMeasurable hf.1

end RCLike

section Liminf

variable [MeasurableSpace E] [OpensMeasurableSpace E] {R : ℝ≥0}

theorem ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd {p : ℝ≥0∞} {f : ℕ → α → E}
    (hfmeas : ∀ n, Measurable (f n)) (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) :
    ∀ᵐ x ∂μ, liminf (fun n => ((‖f n x‖₊ : ℝ≥0∞) ^ p.toReal : ℝ≥0∞)) atTop < ∞ := by
  by_cases hp0 : p.toReal = 0
  · simp only [hp0, ENNReal.rpow_zero]
    filter_upwards with _
    rw [liminf_const (1 : ℝ≥0∞)]
    exact ENNReal.one_lt_top
  have hp : p ≠ 0 := fun h => by simp [h] at hp0
  have hp' : p ≠ ∞ := fun h => by simp [h] at hp0
  refine
    ae_lt_top (measurable_liminf fun n => (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.toReal)
      (lt_of_le_of_lt
          (lintegral_liminf_le fun n => (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.toReal)
          (lt_of_le_of_lt ?_
            (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top :
              (R : ℝ≥0∞) ^ p.toReal < ∞))).ne
  simp_rw [eLpNorm_eq_lintegral_rpow_nnnorm hp hp', one_div] at hbdd
  simp_rw [liminf_eq, eventually_atTop]
  exact
    sSup_le fun b ⟨a, ha⟩ =>
      (ha a le_rfl).trans ((ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hp hp')).1 (hbdd _))

@[deprecated (since := "2024-07-27")]
alias ae_bdd_liminf_atTop_rpow_of_snorm_bdd := ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd

theorem ae_bdd_liminf_atTop_of_eLpNorm_bdd {p : ℝ≥0∞} (hp : p ≠ 0) {f : ℕ → α → E}
    (hfmeas : ∀ n, Measurable (f n)) (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) :
    ∀ᵐ x ∂μ, liminf (fun n => (‖f n x‖₊ : ℝ≥0∞)) atTop < ∞ := by
  by_cases hp' : p = ∞
  · subst hp'
    simp_rw [eLpNorm_exponent_top] at hbdd
    have : ∀ n, ∀ᵐ x ∂μ, (‖f n x‖₊ : ℝ≥0∞) < R + 1 := fun n =>
      ae_lt_of_essSup_lt
        (lt_of_le_of_lt (hbdd n) <| ENNReal.lt_add_right ENNReal.coe_ne_top one_ne_zero)
    rw [← ae_all_iff] at this
    filter_upwards [this] with x hx using lt_of_le_of_lt
        (liminf_le_of_frequently_le' <| Frequently.of_forall fun n => (hx n).le)
        (ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.one_lt_top⟩)
  filter_upwards [ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd hfmeas hbdd] with x hx
  have hppos : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have :
    liminf (fun n => (‖f n x‖₊ : ℝ≥0∞) ^ p.toReal) atTop =
      liminf (fun n => (‖f n x‖₊ : ℝ≥0∞)) atTop ^ p.toReal := by
    change
      liminf (fun n => ENNReal.orderIsoRpow p.toReal hppos (‖f n x‖₊ : ℝ≥0∞)) atTop =
        ENNReal.orderIsoRpow p.toReal hppos (liminf (fun n => (‖f n x‖₊ : ℝ≥0∞)) atTop)
    refine (OrderIso.liminf_apply (ENNReal.orderIsoRpow p.toReal _) ?_ ?_ ?_ ?_).symm <;>
      isBoundedDefault
  rw [this] at hx
  rw [← ENNReal.rpow_one (liminf (fun n => ‖f n x‖₊) atTop), ← mul_inv_cancel₀ hppos.ne.symm,
    ENNReal.rpow_mul]
  exact ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 hppos.le) hx.ne

@[deprecated (since := "2024-07-27")]
alias ae_bdd_liminf_atTop_of_snorm_bdd := ae_bdd_liminf_atTop_of_eLpNorm_bdd

end Liminf

/-- A continuous function with compact support belongs to `L^∞`.
See `Continuous.memℒp_of_hasCompactSupport` for a version for `L^p`. -/
theorem _root_.Continuous.memℒp_top_of_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {f : X → E} (hf : Continuous f) (h'f : HasCompactSupport f) (μ : Measure X) : Memℒp f ⊤ μ := by
  borelize E
  rcases hf.bounded_above_of_compact_support h'f with ⟨C, hC⟩
  apply memℒp_top_of_bound ?_ C (Filter.Eventually.of_forall hC)
  exact (hf.stronglyMeasurable_of_hasCompactSupport h'f).aestronglyMeasurable

section UnifTight

/-- A single function that is `Memℒp f p μ` is tight with respect to `μ`. -/
theorem Memℒp.exists_eLpNorm_indicator_compl_lt {β : Type*} [NormedAddCommGroup β] (hp_top : p ≠ ∞)
    {f : α → β} (hf : Memℒp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : Set α, MeasurableSet s ∧ μ s < ∞ ∧ eLpNorm (sᶜ.indicator f) p μ < ε := by
  rcases eq_or_ne p 0 with rfl | hp₀
  · use ∅; simp [pos_iff_ne_zero.2 hε] -- first take care of `p = 0`
  · obtain ⟨s, hsm, hs, hε⟩ :
        ∃ s, MeasurableSet s ∧ μ s < ∞ ∧ ∫⁻ a in sᶜ, (‖f a‖₊) ^ p.toReal ∂μ < ε ^ p.toReal := by
      apply exists_setLintegral_compl_lt
      · exact ((eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top hp₀ hp_top).1 hf.2).ne
      · simp [*]
    refine ⟨s, hsm, hs, ?_⟩
    rwa [eLpNorm_indicator_eq_restrict hsm.compl, eLpNorm_eq_lintegral_rpow_nnnorm hp₀ hp_top,
      one_div, ENNReal.rpow_inv_lt_iff]
    simp [ENNReal.toReal_pos, *]

@[deprecated (since := "2024-07-27")]
alias Memℒp.exists_snorm_indicator_compl_lt := Memℒp.exists_eLpNorm_indicator_compl_lt

end UnifTight
end ℒp

end MeasureTheory
