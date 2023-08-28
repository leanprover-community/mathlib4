/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import Mathlib.Analysis.NormedSpace.IndicatorFunction
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Integral.MeanInequalities

#align_import measure_theory.function.lp_seminorm from "leanprover-community/mathlib"@"c4015acc0a223449d44061e27ddac1835a3852b9"

/-!
# ℒp space

This file describes properties of almost everywhere strongly measurable functions with finite
`p`-seminorm, denoted by `snorm f p μ` and defined for `p:ℝ≥0∞` as `0` if `p=0`,
`(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and `essSup ‖f‖ μ` for `p=∞`.

The Prop-valued `Memℒp f p μ` states that a function `f : α → E` has finite `p`-seminorm
and is almost everywhere strongly measurable.

## Main definitions

* `snorm' f p μ` : `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `f : α → F` and `p : ℝ`, where `α` is a measurable
  space and `F` is a normed group.
* `snormEssSup f μ` : seminorm in `ℒ∞`, equal to the essential supremum `ess_sup ‖f‖ μ`.
* `snorm f p μ` : for `p : ℝ≥0∞`, seminorm in `ℒp`, equal to `0` for `p=0`, to `snorm' f p μ`
  for `0 < p < ∞` and to `snormEssSup f μ` for `p = ∞`.

* `Memℒp f p μ` : property that the function `f` is almost everywhere strongly measurable and has
  finite `p`-seminorm for the measure `μ` (`snorm f p μ < ∞`)

-/


noncomputable section

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220
set_option linter.uppercaseLean3 false

open TopologicalSpace MeasureTheory Filter

open NNReal ENNReal BigOperators Topology MeasureTheory

variable {α E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

namespace MeasureTheory

section ℒp

/-!
### ℒp seminorm

We define the ℒp seminorm, denoted by `snorm f p μ`. For real `p`, it is given by an integral
formula (for which we use the notation `snorm' f p μ`), and for `p = ∞` it is the essential
supremum (for which we use the notation `snormEssSup f μ`).

We also define a predicate `Memℒp f p μ`, requesting that a function is almost everywhere
measurable and has finite `snorm f p μ`.

This paragraph is devoted to the basic properties of these definitions. It is constructed as
follows: for a given property, we prove it for `snorm'` and `snormEssSup` when it makes sense,
deduce it for `snorm`, and translate it in terms of `Memℒp`.
-/


section ℒpSpaceDefinition

/-- `(∫ ‖f a‖^q ∂μ) ^ (1/q)`, which is a seminorm on the space of measurable functions for which
this quantity is finite -/
def snorm' {_ : MeasurableSpace α} (f : α → F) (q : ℝ) (μ : Measure α) : ℝ≥0∞ :=
  (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ q ∂μ) ^ (1 / q)
#align measure_theory.snorm' MeasureTheory.snorm'

/-- seminorm for `ℒ∞`, equal to the essential supremum of `‖f‖`. -/
def snormEssSup {_ : MeasurableSpace α} (f : α → F) (μ : Measure α) :=
  essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ
#align measure_theory.snorm_ess_sup MeasureTheory.snormEssSup

/-- `ℒp` seminorm, equal to `0` for `p=0`, to `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and to
`essSup ‖f‖ μ` for `p = ∞`. -/
def snorm {_ : MeasurableSpace α} (f : α → F) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = 0 then 0 else if p = ∞ then snormEssSup f μ else snorm' f (ENNReal.toReal p) μ
#align measure_theory.snorm MeasureTheory.snorm

theorem snorm_eq_snorm' (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → F} :
    snorm f p μ = snorm' f (ENNReal.toReal p) μ := by simp [snorm, hp_ne_zero, hp_ne_top]
#align measure_theory.snorm_eq_snorm' MeasureTheory.snorm_eq_snorm'

theorem snorm_eq_lintegral_rpow_nnnorm (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {f : α → F} :
    snorm f p μ = (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
  rw [snorm_eq_snorm' hp_ne_zero hp_ne_top, snorm']
#align measure_theory.snorm_eq_lintegral_rpow_nnnorm MeasureTheory.snorm_eq_lintegral_rpow_nnnorm

theorem snorm_one_eq_lintegral_nnnorm {f : α → F} : snorm f 1 μ = ∫⁻ x, ‖f x‖₊ ∂μ := by
  simp_rw [snorm_eq_lintegral_rpow_nnnorm one_ne_zero ENNReal.coe_ne_top, ENNReal.one_toReal,
    one_div_one, ENNReal.rpow_one]
#align measure_theory.snorm_one_eq_lintegral_nnnorm MeasureTheory.snorm_one_eq_lintegral_nnnorm

@[simp]
theorem snorm_exponent_top {f : α → F} : snorm f ∞ μ = snormEssSup f μ := by simp [snorm]
#align measure_theory.snorm_exponent_top MeasureTheory.snorm_exponent_top

/-- The property that `f:α→E` is ae strongly measurable and `(∫ ‖f a‖^p ∂μ)^(1/p)` is finite
if `p < ∞`, or `essSup f < ∞` if `p = ∞`. -/
def Memℒp {α} {_ : MeasurableSpace α} (f : α → E) (p : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ snorm f p μ < ∞
#align measure_theory.mem_ℒp MeasureTheory.Memℒp

-- Porting note: TODO Delete this when leanprover/lean4#2243 is fixed.
theorem memℒp_def {α} {_ : MeasurableSpace α} (f : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    Memℒp f p μ ↔ (AEStronglyMeasurable f μ ∧ snorm f p μ < ∞) :=
  Iff.rfl

attribute [eqns memℒp_def] Memℒp

theorem Memℒp.aestronglyMeasurable {f : α → E} {p : ℝ≥0∞} (h : Memℒp f p μ) :
    AEStronglyMeasurable f μ :=
  h.1
#align measure_theory.mem_ℒp.ae_strongly_measurable MeasureTheory.Memℒp.aestronglyMeasurable

theorem lintegral_rpow_nnnorm_eq_rpow_snorm' {f : α → F} (hq0_lt : 0 < q) :
    (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ q ∂μ) = snorm' f q μ ^ q := by
  rw [snorm', ← ENNReal.rpow_mul, one_div, inv_mul_cancel, ENNReal.rpow_one]
  exact (ne_of_lt hq0_lt).symm
#align measure_theory.lintegral_rpow_nnnorm_eq_rpow_snorm' MeasureTheory.lintegral_rpow_nnnorm_eq_rpow_snorm'

end ℒpSpaceDefinition

section Top

theorem Memℒp.snorm_lt_top {f : α → E} (hfp : Memℒp f p μ) : snorm f p μ < ∞ :=
  hfp.2
#align measure_theory.mem_ℒp.snorm_lt_top MeasureTheory.Memℒp.snorm_lt_top

theorem Memℒp.snorm_ne_top {f : α → E} (hfp : Memℒp f p μ) : snorm f p μ ≠ ∞ :=
  ne_of_lt hfp.2
#align measure_theory.mem_ℒp.snorm_ne_top MeasureTheory.Memℒp.snorm_ne_top

theorem lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top {f : α → F} (hq0_lt : 0 < q)
    (hfq : snorm' f q μ < ∞) : (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ q ∂μ) < ∞ := by
  rw [lintegral_rpow_nnnorm_eq_rpow_snorm' hq0_lt]
  exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt hq0_lt) (ne_of_lt hfq)
#align measure_theory.lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top MeasureTheory.lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top

theorem lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top {f : α → F} (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hfp : snorm f p μ < ∞) : (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) < ∞ := by
  apply lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top
  · exact ENNReal.toReal_pos hp_ne_zero hp_ne_top
  · simpa [snorm_eq_snorm' hp_ne_zero hp_ne_top] using hfp
#align measure_theory.lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top MeasureTheory.lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top

theorem snorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top {f : α → F} (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : snorm f p μ < ∞ ↔ (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) < ∞ :=
  ⟨lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top hp_ne_zero hp_ne_top, by
    intro h
    have hp' := ENNReal.toReal_pos hp_ne_zero hp_ne_top
    have : 0 < 1 / p.toReal := div_pos zero_lt_one hp'
    simpa [snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top] using
      ENNReal.rpow_lt_top_of_nonneg (le_of_lt this) (ne_of_lt h)⟩
#align measure_theory.snorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top MeasureTheory.snorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top

end Top

section Zero

@[simp]
theorem snorm'_exponent_zero {f : α → F} : snorm' f 0 μ = 1 := by
  rw [snorm', _root_.div_zero, ENNReal.rpow_zero]
#align measure_theory.snorm'_exponent_zero MeasureTheory.snorm'_exponent_zero

@[simp]
theorem snorm_exponent_zero {f : α → F} : snorm f 0 μ = 0 := by simp [snorm]
#align measure_theory.snorm_exponent_zero MeasureTheory.snorm_exponent_zero

theorem memℒp_zero_iff_aestronglyMeasurable {f : α → E} : Memℒp f 0 μ ↔ AEStronglyMeasurable f μ :=
  by simp [Memℒp, snorm_exponent_zero]
#align measure_theory.mem_ℒp_zero_iff_ae_strongly_measurable MeasureTheory.memℒp_zero_iff_aestronglyMeasurable

@[simp]
theorem snorm'_zero (hp0_lt : 0 < q) : snorm' (0 : α → F) q μ = 0 := by simp [snorm', hp0_lt]
#align measure_theory.snorm'_zero MeasureTheory.snorm'_zero

@[simp]
theorem snorm'_zero' (hq0_ne : q ≠ 0) (hμ : μ ≠ 0) : snorm' (0 : α → F) q μ = 0 := by
  cases' le_or_lt 0 q with hq0 hq_neg
  · exact snorm'_zero (lt_of_le_of_ne hq0 hq0_ne.symm)
  · simp [snorm', ENNReal.rpow_eq_zero_iff, hμ, hq_neg]
#align measure_theory.snorm'_zero' MeasureTheory.snorm'_zero'

@[simp]
theorem snormEssSup_zero : snormEssSup (0 : α → F) μ = 0 := by
  simp_rw [snormEssSup, Pi.zero_apply, nnnorm_zero, ENNReal.coe_zero, ← ENNReal.bot_eq_zero]
  exact essSup_const_bot
#align measure_theory.snorm_ess_sup_zero MeasureTheory.snormEssSup_zero

@[simp]
theorem snorm_zero : snorm (0 : α → F) p μ = 0 := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp only [h_top, snorm_exponent_top, snormEssSup_zero]
  rw [← Ne.def] at h0
  simp [snorm_eq_snorm' h0 h_top, ENNReal.toReal_pos h0 h_top]
#align measure_theory.snorm_zero MeasureTheory.snorm_zero

@[simp]
theorem snorm_zero' : snorm (fun _ : α => (0 : F)) p μ = 0 := by convert snorm_zero (F := F)
#align measure_theory.snorm_zero' MeasureTheory.snorm_zero'

theorem zero_memℒp : Memℒp (0 : α → E) p μ :=
  ⟨aestronglyMeasurable_zero, by
    rw [snorm_zero]
    exact ENNReal.coe_lt_top⟩
#align measure_theory.zero_mem_ℒp MeasureTheory.zero_memℒp

theorem zero_mem_ℒp' : Memℒp (fun _ : α => (0 : E)) p μ := zero_memℒp (E := E)
#align measure_theory.zero_mem_ℒp' MeasureTheory.zero_mem_ℒp'

variable [MeasurableSpace α]

theorem snorm'_measure_zero_of_pos {f : α → F} (hq_pos : 0 < q) : snorm' f q (0 : Measure α) = 0 :=
  by simp [snorm', hq_pos]
#align measure_theory.snorm'_measure_zero_of_pos MeasureTheory.snorm'_measure_zero_of_pos

theorem snorm'_measure_zero_of_exponent_zero {f : α → F} : snorm' f 0 (0 : Measure α) = 1 := by
  simp [snorm']
#align measure_theory.snorm'_measure_zero_of_exponent_zero MeasureTheory.snorm'_measure_zero_of_exponent_zero

theorem snorm'_measure_zero_of_neg {f : α → F} (hq_neg : q < 0) : snorm' f q (0 : Measure α) = ∞ :=
  by simp [snorm', hq_neg]
#align measure_theory.snorm'_measure_zero_of_neg MeasureTheory.snorm'_measure_zero_of_neg

@[simp]
theorem snormEssSup_measure_zero {f : α → F} : snormEssSup f (0 : Measure α) = 0 := by
  simp [snormEssSup]
#align measure_theory.snorm_ess_sup_measure_zero MeasureTheory.snormEssSup_measure_zero

@[simp]
theorem snorm_measure_zero {f : α → F} : snorm f p (0 : Measure α) = 0 := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp [h_top]
  rw [← Ne.def] at h0
  simp [snorm_eq_snorm' h0 h_top, snorm', ENNReal.toReal_pos h0 h_top]
#align measure_theory.snorm_measure_zero MeasureTheory.snorm_measure_zero

end Zero

section Neg

@[simp]
theorem snorm'_neg {f : α → F} : snorm' (-f) q μ = snorm' f q μ := by simp [snorm']
#align measure_theory.snorm'_neg MeasureTheory.snorm'_neg

@[simp]
theorem snorm_neg {f : α → F} : snorm (-f) p μ = snorm f p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp [h_top, snormEssSup]
  simp [snorm_eq_snorm' h0 h_top]
#align measure_theory.snorm_neg MeasureTheory.snorm_neg

theorem Memℒp.neg {f : α → E} (hf : Memℒp f p μ) : Memℒp (-f) p μ :=
  ⟨AEStronglyMeasurable.neg hf.1, by simp [hf.right]⟩
#align measure_theory.mem_ℒp.neg MeasureTheory.Memℒp.neg

theorem memℒp_neg_iff {f : α → E} : Memℒp (-f) p μ ↔ Memℒp f p μ :=
  ⟨fun h => neg_neg f ▸ h.neg, Memℒp.neg⟩
#align measure_theory.mem_ℒp_neg_iff MeasureTheory.memℒp_neg_iff

end Neg

section Const

theorem snorm'_const (c : F) (hq_pos : 0 < q) :
    snorm' (fun _ : α => c) q μ = (‖c‖₊ : ℝ≥0∞) * μ Set.univ ^ (1 / q) := by
  rw [snorm', lintegral_const, ENNReal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 ≤ 1 / q)]
  congr
  rw [← ENNReal.rpow_mul]
  suffices hq_cancel : q * (1 / q) = 1; · rw [hq_cancel, ENNReal.rpow_one]
  rw [one_div, mul_inv_cancel (ne_of_lt hq_pos).symm]
#align measure_theory.snorm'_const MeasureTheory.snorm'_const

theorem snorm'_const' [IsFiniteMeasure μ] (c : F) (hc_ne_zero : c ≠ 0) (hq_ne_zero : q ≠ 0) :
    snorm' (fun _ : α => c) q μ = (‖c‖₊ : ℝ≥0∞) * μ Set.univ ^ (1 / q) := by
  rw [snorm', lintegral_const, ENNReal.mul_rpow_of_ne_top _ (measure_ne_top μ Set.univ)]
  · congr
    rw [← ENNReal.rpow_mul]
    suffices hp_cancel : q * (1 / q) = 1
    · rw [hp_cancel, ENNReal.rpow_one]
    rw [one_div, mul_inv_cancel hq_ne_zero]
  · rw [Ne.def, ENNReal.rpow_eq_top_iff, not_or, not_and_or, not_and_or]
    constructor
    · left
      rwa [ENNReal.coe_eq_zero, nnnorm_eq_zero]
    · exact Or.inl ENNReal.coe_ne_top
#align measure_theory.snorm'_const' MeasureTheory.snorm'_const'

theorem snormEssSup_const (c : F) (hμ : μ ≠ 0) : snormEssSup (fun _ : α => c) μ = (‖c‖₊ : ℝ≥0∞) :=
  by rw [snormEssSup, essSup_const _ hμ]
#align measure_theory.snorm_ess_sup_const MeasureTheory.snormEssSup_const

theorem snorm'_const_of_isProbabilityMeasure (c : F) (hq_pos : 0 < q) [IsProbabilityMeasure μ] :
    snorm' (fun _ : α => c) q μ = (‖c‖₊ : ℝ≥0∞) := by simp [snorm'_const c hq_pos, measure_univ]
#align measure_theory.snorm'_const_of_is_probability_measure MeasureTheory.snorm'_const_of_isProbabilityMeasure

theorem snorm_const (c : F) (h0 : p ≠ 0) (hμ : μ ≠ 0) :
    snorm (fun _ : α => c) p μ = (‖c‖₊ : ℝ≥0∞) * μ Set.univ ^ (1 / ENNReal.toReal p) := by
  by_cases h_top : p = ∞
  · simp [h_top, snormEssSup_const c hμ]
  simp [snorm_eq_snorm' h0 h_top, snorm'_const, ENNReal.toReal_pos h0 h_top]
#align measure_theory.snorm_const MeasureTheory.snorm_const

theorem snorm_const' (c : F) (h0 : p ≠ 0) (h_top : p ≠ ∞) :
    snorm (fun _ : α => c) p μ = (‖c‖₊ : ℝ≥0∞) * μ Set.univ ^ (1 / ENNReal.toReal p) := by
  simp [snorm_eq_snorm' h0 h_top, snorm'_const, ENNReal.toReal_pos h0 h_top]
#align measure_theory.snorm_const' MeasureTheory.snorm_const'

theorem snorm_const_lt_top_iff {p : ℝ≥0∞} {c : F} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    snorm (fun _ : α => c) p μ < ∞ ↔ c = 0 ∨ μ Set.univ < ∞ := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  by_cases hμ : μ = 0
  · simp only [hμ, Measure.coe_zero, Pi.zero_apply, or_true_iff, WithTop.zero_lt_top,
      snorm_measure_zero]
  by_cases hc : c = 0
  · simp only [hc, true_or_iff, eq_self_iff_true, WithTop.zero_lt_top, snorm_zero']
  rw [snorm_const' c hp_ne_zero hp_ne_top]
  by_cases hμ_top : μ Set.univ = ∞
  · simp [hc, hμ_top, hp]
  rw [ENNReal.mul_lt_top_iff]
  simp only [true_and_iff, one_div, ENNReal.rpow_eq_zero_iff, hμ, false_or_iff, or_false_iff,
    ENNReal.coe_lt_top, nnnorm_eq_zero, ENNReal.coe_eq_zero,
    MeasureTheory.Measure.measure_univ_eq_zero, hp, inv_lt_zero, hc, and_false_iff, false_and_iff,
    _root_.inv_pos, or_self_iff, hμ_top, Ne.lt_top hμ_top, iff_true_iff]
  exact ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.mpr hp.le) hμ_top
#align measure_theory.snorm_const_lt_top_iff MeasureTheory.snorm_const_lt_top_iff

theorem memℒp_const (c : E) [IsFiniteMeasure μ] : Memℒp (fun _ : α => c) p μ := by
  refine' ⟨aestronglyMeasurable_const, _⟩
  by_cases h0 : p = 0
  · simp [h0]
  by_cases hμ : μ = 0
  · simp [hμ]
  rw [snorm_const c h0 hμ]
  refine' ENNReal.mul_lt_top ENNReal.coe_ne_top _
  refine' (ENNReal.rpow_lt_top_of_nonneg _ (measure_ne_top μ Set.univ)).ne
  simp
#align measure_theory.mem_ℒp_const MeasureTheory.memℒp_const

theorem memℒp_top_const (c : E) : Memℒp (fun _ : α => c) ∞ μ := by
  refine' ⟨aestronglyMeasurable_const, _⟩
  by_cases h : μ = 0
  · simp only [h, snorm_measure_zero, WithTop.zero_lt_top]
  · rw [snorm_const _ ENNReal.top_ne_zero h]
    simp only [ENNReal.top_toReal, _root_.div_zero, ENNReal.rpow_zero, mul_one, ENNReal.coe_lt_top]
#align measure_theory.mem_ℒp_top_const MeasureTheory.memℒp_top_const

theorem memℒp_const_iff {p : ℝ≥0∞} {c : E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    Memℒp (fun _ : α => c) p μ ↔ c = 0 ∨ μ Set.univ < ∞ := by
  rw [← snorm_const_lt_top_iff hp_ne_zero hp_ne_top]
  exact ⟨fun h => h.2, fun h => ⟨aestronglyMeasurable_const, h⟩⟩
#align measure_theory.mem_ℒp_const_iff MeasureTheory.memℒp_const_iff

end Const

theorem snorm'_mono_nnnorm_ae {f : α → F} {g : α → G} (hq : 0 ≤ q) (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    snorm' f q μ ≤ snorm' g q μ := by
  rw [snorm']
  refine' ENNReal.rpow_le_rpow _ (one_div_nonneg.2 hq)
  refine' lintegral_mono_ae (h.mono fun x hx => _)
  exact ENNReal.rpow_le_rpow (ENNReal.coe_le_coe.2 hx) hq
#align measure_theory.snorm'_mono_nnnorm_ae MeasureTheory.snorm'_mono_nnnorm_ae

theorem snorm'_mono_ae {f : α → F} {g : α → G} (hq : 0 ≤ q) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    snorm' f q μ ≤ snorm' g q μ :=
  snorm'_mono_nnnorm_ae hq h
#align measure_theory.snorm'_mono_ae MeasureTheory.snorm'_mono_ae

theorem snorm'_congr_nnnorm_ae {f g : α → F} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊) :
    snorm' f q μ = snorm' g q μ := by
  have : (fun x => (‖f x‖₊ : ℝ≥0∞) ^ q) =ᵐ[μ] fun x => (‖g x‖₊ : ℝ≥0∞) ^ q :=
    hfg.mono fun x hx => by simp_rw [hx]
  simp only [snorm', lintegral_congr_ae this]
#align measure_theory.snorm'_congr_nnnorm_ae MeasureTheory.snorm'_congr_nnnorm_ae

theorem snorm'_congr_norm_ae {f g : α → F} (hfg : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
    snorm' f q μ = snorm' g q μ :=
  snorm'_congr_nnnorm_ae <| hfg.mono fun _x hx => NNReal.eq hx
#align measure_theory.snorm'_congr_norm_ae MeasureTheory.snorm'_congr_norm_ae

theorem snorm'_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : snorm' f q μ = snorm' g q μ :=
  snorm'_congr_nnnorm_ae (hfg.fun_comp _)
#align measure_theory.snorm'_congr_ae MeasureTheory.snorm'_congr_ae

theorem snormEssSup_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : snormEssSup f μ = snormEssSup g μ :=
  essSup_congr_ae (hfg.fun_comp (((↑) : ℝ≥0 → ℝ≥0∞) ∘ nnnorm))
#align measure_theory.snorm_ess_sup_congr_ae MeasureTheory.snormEssSup_congr_ae

theorem snormEssSup_mono_nnnorm_ae {f g : α → F} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    snormEssSup f μ ≤ snormEssSup g μ :=
  essSup_mono_ae <| hfg.mono fun _x hx => ENNReal.coe_le_coe.mpr hx
#align measure_theory.snorm_ess_sup_mono_nnnorm_ae MeasureTheory.snormEssSup_mono_nnnorm_ae

theorem snorm_mono_nnnorm_ae {f : α → F} {g : α → G} (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    snorm f p μ ≤ snorm g p μ := by
  simp only [snorm]
  split_ifs
  · exact le_rfl
  · exact essSup_mono_ae (h.mono fun x hx => ENNReal.coe_le_coe.mpr hx)
  · exact snorm'_mono_nnnorm_ae ENNReal.toReal_nonneg h
#align measure_theory.snorm_mono_nnnorm_ae MeasureTheory.snorm_mono_nnnorm_ae

theorem snorm_mono_ae {f : α → F} {g : α → G} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    snorm f p μ ≤ snorm g p μ :=
  snorm_mono_nnnorm_ae h
#align measure_theory.snorm_mono_ae MeasureTheory.snorm_mono_ae

theorem snorm_mono_ae_real {f : α → F} {g : α → ℝ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) :
    snorm f p μ ≤ snorm g p μ :=
  snorm_mono_ae <| h.mono fun _x hx => hx.trans ((le_abs_self _).trans (Real.norm_eq_abs _).symm.le)
#align measure_theory.snorm_mono_ae_real MeasureTheory.snorm_mono_ae_real

theorem snorm_mono_nnnorm {f : α → F} {g : α → G} (h : ∀ x, ‖f x‖₊ ≤ ‖g x‖₊) :
    snorm f p μ ≤ snorm g p μ :=
  snorm_mono_nnnorm_ae (eventually_of_forall fun x => h x)
#align measure_theory.snorm_mono_nnnorm MeasureTheory.snorm_mono_nnnorm

theorem snorm_mono {f : α → F} {g : α → G} (h : ∀ x, ‖f x‖ ≤ ‖g x‖) : snorm f p μ ≤ snorm g p μ :=
  snorm_mono_ae (eventually_of_forall fun x => h x)
#align measure_theory.snorm_mono MeasureTheory.snorm_mono

theorem snorm_mono_real {f : α → F} {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) :
    snorm f p μ ≤ snorm g p μ :=
  snorm_mono_ae_real (eventually_of_forall fun x => h x)
#align measure_theory.snorm_mono_real MeasureTheory.snorm_mono_real

theorem snormEssSup_le_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    snormEssSup f μ ≤ C :=
  essSup_le_of_ae_le (C : ℝ≥0∞) <| hfC.mono fun _x hx => ENNReal.coe_le_coe.mpr hx
#align measure_theory.snorm_ess_sup_le_of_ae_nnnorm_bound MeasureTheory.snormEssSup_le_of_ae_nnnorm_bound

theorem snormEssSup_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    snormEssSup f μ ≤ ENNReal.ofReal C :=
  snormEssSup_le_of_ae_nnnorm_bound <| hfC.mono fun _x hx => hx.trans C.le_coe_toNNReal
#align measure_theory.snorm_ess_sup_le_of_ae_bound MeasureTheory.snormEssSup_le_of_ae_bound

theorem snormEssSup_lt_top_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    snormEssSup f μ < ∞ :=
  (snormEssSup_le_of_ae_nnnorm_bound hfC).trans_lt ENNReal.coe_lt_top
#align measure_theory.snorm_ess_sup_lt_top_of_ae_nnnorm_bound MeasureTheory.snormEssSup_lt_top_of_ae_nnnorm_bound

theorem snormEssSup_lt_top_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    snormEssSup f μ < ∞ :=
  (snormEssSup_le_of_ae_bound hfC).trans_lt ENNReal.ofReal_lt_top
#align measure_theory.snorm_ess_sup_lt_top_of_ae_bound MeasureTheory.snormEssSup_lt_top_of_ae_bound

theorem snorm_le_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    snorm f p μ ≤ C • μ Set.univ ^ p.toReal⁻¹ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  by_cases hp : p = 0
  · simp [hp]
  have : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖(C : ℝ)‖₊ := hfC.mono fun x hx => hx.trans_eq C.nnnorm_eq.symm
  refine' (snorm_mono_ae this).trans_eq _
  rw [snorm_const _ hp (NeZero.ne μ), C.nnnorm_eq, one_div, ENNReal.smul_def, smul_eq_mul]
#align measure_theory.snorm_le_of_ae_nnnorm_bound MeasureTheory.snorm_le_of_ae_nnnorm_bound

theorem snorm_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    snorm f p μ ≤ μ Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal C := by
  rw [← mul_comm]
  exact snorm_le_of_ae_nnnorm_bound (hfC.mono fun x hx => hx.trans C.le_coe_toNNReal)
#align measure_theory.snorm_le_of_ae_bound MeasureTheory.snorm_le_of_ae_bound

theorem snorm_congr_nnnorm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊) :
    snorm f p μ = snorm g p μ :=
  le_antisymm (snorm_mono_nnnorm_ae <| EventuallyEq.le hfg)
    (snorm_mono_nnnorm_ae <| (EventuallyEq.symm hfg).le)
#align measure_theory.snorm_congr_nnnorm_ae MeasureTheory.snorm_congr_nnnorm_ae

theorem snorm_congr_norm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
    snorm f p μ = snorm g p μ :=
  snorm_congr_nnnorm_ae <| hfg.mono fun _x hx => NNReal.eq hx
#align measure_theory.snorm_congr_norm_ae MeasureTheory.snorm_congr_norm_ae

theorem snorm_indicator_sub_indicator (s t : Set α) (f : α → E) :
    snorm (s.indicator f - t.indicator f) p μ = snorm ((s ∆ t).indicator f) p μ :=
    snorm_congr_norm_ae <| ae_of_all _ fun x ↦ by
  simp only [Pi.sub_apply, Set.apply_indicator_symmDiff norm_neg]

@[simp]
theorem snorm'_norm {f : α → F} : snorm' (fun a => ‖f a‖) q μ = snorm' f q μ := by simp [snorm']
#align measure_theory.snorm'_norm MeasureTheory.snorm'_norm

@[simp]
theorem snorm_norm (f : α → F) : snorm (fun x => ‖f x‖) p μ = snorm f p μ :=
  snorm_congr_norm_ae <| eventually_of_forall fun _ => norm_norm _
#align measure_theory.snorm_norm MeasureTheory.snorm_norm

theorem snorm'_norm_rpow (f : α → F) (p q : ℝ) (hq_pos : 0 < q) :
    snorm' (fun x => ‖f x‖ ^ q) p μ = snorm' f (p * q) μ ^ q := by
  simp_rw [snorm']
  rw [← ENNReal.rpow_mul, ← one_div_mul_one_div]
  simp_rw [one_div]
  rw [mul_assoc, inv_mul_cancel hq_pos.ne.symm, mul_one]
  congr
  ext1 x
  simp_rw [← ofReal_norm_eq_coe_nnnorm]
  rw [Real.norm_eq_abs, abs_eq_self.mpr (Real.rpow_nonneg_of_nonneg (norm_nonneg _) _), mul_comm, ←
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq_pos.le, ENNReal.rpow_mul]
#align measure_theory.snorm'_norm_rpow MeasureTheory.snorm'_norm_rpow

theorem snorm_norm_rpow (f : α → F) (hq_pos : 0 < q) :
    snorm (fun x => ‖f x‖ ^ q) p μ = snorm f (p * ENNReal.ofReal q) μ ^ q := by
  by_cases h0 : p = 0
  · simp [h0, ENNReal.zero_rpow_of_pos hq_pos]
  by_cases hp_top : p = ∞
  · simp only [hp_top, snorm_exponent_top, ENNReal.top_mul', hq_pos.not_le, ENNReal.ofReal_eq_zero,
      if_false, snorm_exponent_top, snormEssSup]
    have h_rpow :
      essSup (fun x : α => (‖‖f x‖ ^ q‖₊ : ℝ≥0∞)) μ =
        essSup (fun x : α => (‖f x‖₊ : ℝ≥0∞) ^ q) μ := by
      congr
      ext1 x
      conv_rhs => rw [← nnnorm_norm]
      rw [ENNReal.coe_rpow_of_nonneg _ hq_pos.le, ENNReal.coe_eq_coe]
      ext
      push_cast
      rw [Real.norm_rpow_of_nonneg (norm_nonneg _)]
    rw [h_rpow]
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos hq_pos
    have h_rpow_surj := (ENNReal.rpow_left_bijective hq_pos.ne.symm).2
    let iso := h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj
    exact (iso.essSup_apply (fun x => (‖f x‖₊ : ℝ≥0∞)) μ).symm
  rw [snorm_eq_snorm' h0 hp_top, snorm_eq_snorm' _ _]
  swap;
  · refine' mul_ne_zero h0 _
    rwa [Ne.def, ENNReal.ofReal_eq_zero, not_le]
  swap; · exact ENNReal.mul_ne_top hp_top ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq_pos.le]
  exact snorm'_norm_rpow f p.toReal q hq_pos
#align measure_theory.snorm_norm_rpow MeasureTheory.snorm_norm_rpow

theorem snorm_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : snorm f p μ = snorm g p μ :=
  snorm_congr_norm_ae <| hfg.mono fun _x hx => hx ▸ rfl
#align measure_theory.snorm_congr_ae MeasureTheory.snorm_congr_ae

theorem memℒp_congr_ae {f g : α → E} (hfg : f =ᵐ[μ] g) : Memℒp f p μ ↔ Memℒp g p μ := by
  simp only [Memℒp, snorm_congr_ae hfg, aestronglyMeasurable_congr hfg]
#align measure_theory.mem_ℒp_congr_ae MeasureTheory.memℒp_congr_ae

theorem Memℒp.ae_eq {f g : α → E} (hfg : f =ᵐ[μ] g) (hf_Lp : Memℒp f p μ) : Memℒp g p μ :=
  (memℒp_congr_ae hfg).1 hf_Lp
#align measure_theory.mem_ℒp.ae_eq MeasureTheory.Memℒp.ae_eq

theorem Memℒp.of_le {f : α → E} {g : α → F} (hg : Memℒp g p μ) (hf : AEStronglyMeasurable f μ)
    (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) : Memℒp f p μ :=
  ⟨hf, (snorm_mono_ae hfg).trans_lt hg.snorm_lt_top⟩
#align measure_theory.mem_ℒp.of_le MeasureTheory.Memℒp.of_le

alias Memℒp.mono := Memℒp.of_le
#align measure_theory.mem_ℒp.mono MeasureTheory.Memℒp.mono

theorem Memℒp.mono' {f : α → E} {g : α → ℝ} (hg : Memℒp g p μ) (hf : AEStronglyMeasurable f μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : Memℒp f p μ :=
  hg.mono hf <| h.mono fun _x hx => le_trans hx (le_abs_self _)
#align measure_theory.mem_ℒp.mono' MeasureTheory.Memℒp.mono'

theorem Memℒp.congr_norm {f : α → E} {g : α → F} (hf : Memℒp f p μ) (hg : AEStronglyMeasurable g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) : Memℒp g p μ :=
  hf.mono hg <| EventuallyEq.le <| EventuallyEq.symm h
#align measure_theory.mem_ℒp.congr_norm MeasureTheory.Memℒp.congr_norm

theorem memℒp_congr_norm {f : α → E} {g : α → F} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) : Memℒp f p μ ↔ Memℒp g p μ :=
  ⟨fun h2f => h2f.congr_norm hg h, fun h2g => h2g.congr_norm hf <| EventuallyEq.symm h⟩
#align measure_theory.mem_ℒp_congr_norm MeasureTheory.memℒp_congr_norm

theorem memℒp_top_of_bound {f : α → E} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : Memℒp f ∞ μ :=
  ⟨hf, by
    rw [snorm_exponent_top]
    exact snormEssSup_lt_top_of_ae_bound hfC⟩
#align measure_theory.mem_ℒp_top_of_bound MeasureTheory.memℒp_top_of_bound

theorem Memℒp.of_bound [IsFiniteMeasure μ] {f : α → E} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : Memℒp f p μ :=
  (memℒp_const C).of_le hf (hfC.mono fun _x hx => le_trans hx (le_abs_self _))
#align measure_theory.mem_ℒp.of_bound MeasureTheory.Memℒp.of_bound

@[mono]
theorem snorm'_mono_measure (f : α → F) (hμν : ν ≤ μ) (hq : 0 ≤ q) :
    snorm' f q ν ≤ snorm' f q μ := by
  simp_rw [snorm']
  suffices h_integral_mono : (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ q ∂ν) ≤ ∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ q ∂μ from
    ENNReal.rpow_le_rpow h_integral_mono (by simp [hq])
  exact lintegral_mono' hμν le_rfl
#align measure_theory.snorm'_mono_measure MeasureTheory.snorm'_mono_measure

@[mono]
theorem snormEssSup_mono_measure (f : α → F) (hμν : ν ≪ μ) : snormEssSup f ν ≤ snormEssSup f μ := by
  simp_rw [snormEssSup]
  exact essSup_mono_measure hμν
#align measure_theory.snorm_ess_sup_mono_measure MeasureTheory.snormEssSup_mono_measure

@[mono]
theorem snorm_mono_measure (f : α → F) (hμν : ν ≤ μ) : snorm f p ν ≤ snorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, snormEssSup_mono_measure f (Measure.absolutelyContinuous_of_le hμν)]
  simp_rw [snorm_eq_snorm' hp0 hp_top]
  exact snorm'_mono_measure f hμν ENNReal.toReal_nonneg
#align measure_theory.snorm_mono_measure MeasureTheory.snorm_mono_measure

theorem Memℒp.mono_measure {f : α → E} (hμν : ν ≤ μ) (hf : Memℒp f p μ) : Memℒp f p ν :=
  ⟨hf.1.mono_measure hμν, (snorm_mono_measure f hμν).trans_lt hf.2⟩
#align measure_theory.mem_ℒp.mono_measure MeasureTheory.Memℒp.mono_measure

theorem Memℒp.restrict (s : Set α) {f : α → E} (hf : Memℒp f p μ) : Memℒp f p (μ.restrict s) :=
  hf.mono_measure Measure.restrict_le_self
#align measure_theory.mem_ℒp.restrict MeasureTheory.Memℒp.restrict

theorem snorm'_smul_measure {p : ℝ} (hp : 0 ≤ p) {f : α → F} (c : ℝ≥0∞) :
    snorm' f p (c • μ) = c ^ (1 / p) * snorm' f p μ := by
  rw [snorm', lintegral_smul_measure, ENNReal.mul_rpow_of_nonneg, snorm']
  simp [hp]
#align measure_theory.snorm'_smul_measure MeasureTheory.snorm'_smul_measure

theorem snormEssSup_smul_measure {f : α → F} {c : ℝ≥0∞} (hc : c ≠ 0) :
    snormEssSup f (c • μ) = snormEssSup f μ := by
  simp_rw [snormEssSup]
  exact essSup_smul_measure hc
#align measure_theory.snorm_ess_sup_smul_measure MeasureTheory.snormEssSup_smul_measure

/-- Use `snorm_smul_measure_of_ne_top` instead. -/
private theorem snorm_smul_measure_of_ne_zero_of_ne_top {p : ℝ≥0∞} (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) {f : α → F} (c : ℝ≥0∞) :
    snorm f p (c • μ) = c ^ (1 / p).toReal • snorm f p μ := by
  simp_rw [snorm_eq_snorm' hp_ne_zero hp_ne_top]
  rw [snorm'_smul_measure ENNReal.toReal_nonneg]
  congr
  simp_rw [one_div]
  rw [ENNReal.toReal_inv]

theorem snorm_smul_measure_of_ne_zero {p : ℝ≥0∞} {f : α → F} {c : ℝ≥0∞} (hc : c ≠ 0) :
    snorm f p (c • μ) = c ^ (1 / p).toReal • snorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, snormEssSup_smul_measure hc]
  exact snorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_top c
#align measure_theory.snorm_smul_measure_of_ne_zero MeasureTheory.snorm_smul_measure_of_ne_zero

theorem snorm_smul_measure_of_ne_top {p : ℝ≥0∞} (hp_ne_top : p ≠ ∞) {f : α → F} (c : ℝ≥0∞) :
    snorm f p (c • μ) = c ^ (1 / p).toReal • snorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact snorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_ne_top c
#align measure_theory.snorm_smul_measure_of_ne_top MeasureTheory.snorm_smul_measure_of_ne_top

theorem snorm_one_smul_measure {f : α → F} (c : ℝ≥0∞) : snorm f 1 (c • μ) = c * snorm f 1 μ := by
  rw [@snorm_smul_measure_of_ne_top _ _ _ μ _ 1 (@ENNReal.coe_ne_top 1) f c]
  simp
#align measure_theory.snorm_one_smul_measure MeasureTheory.snorm_one_smul_measure

theorem Memℒp.of_measure_le_smul {μ' : Measure α} (c : ℝ≥0∞) (hc : c ≠ ∞) (hμ'_le : μ' ≤ c • μ)
    {f : α → E} (hf : Memℒp f p μ) : Memℒp f p μ' := by
  refine' ⟨hf.1.mono' (Measure.absolutelyContinuous_of_le_smul hμ'_le), _⟩
  refine' (snorm_mono_measure f hμ'_le).trans_lt _
  by_cases hc0 : c = 0
  · simp [hc0]
  rw [snorm_smul_measure_of_ne_zero hc0, smul_eq_mul]
  refine' ENNReal.mul_lt_top _ hf.2.ne
  simp [hc, hc0]
#align measure_theory.mem_ℒp.of_measure_le_smul MeasureTheory.Memℒp.of_measure_le_smul

theorem Memℒp.smul_measure {f : α → E} {c : ℝ≥0∞} (hf : Memℒp f p μ) (hc : c ≠ ∞) :
    Memℒp f p (c • μ) :=
  hf.of_measure_le_smul c hc le_rfl
#align measure_theory.mem_ℒp.smul_measure MeasureTheory.Memℒp.smul_measure

theorem snorm_one_add_measure (f : α → F) (μ ν : Measure α) :
    snorm f 1 (μ + ν) = snorm f 1 μ + snorm f 1 ν := by
  simp_rw [snorm_one_eq_lintegral_nnnorm]
  rw [lintegral_add_measure _ μ ν]
#align measure_theory.snorm_one_add_measure MeasureTheory.snorm_one_add_measure

theorem snorm_le_add_measure_right (f : α → F) (μ ν : Measure α) {p : ℝ≥0∞} :
    snorm f p μ ≤ snorm f p (μ + ν) :=
  snorm_mono_measure f <| Measure.le_add_right <| le_refl _
#align measure_theory.snorm_le_add_measure_right MeasureTheory.snorm_le_add_measure_right

theorem snorm_le_add_measure_left (f : α → F) (μ ν : Measure α) {p : ℝ≥0∞} :
    snorm f p ν ≤ snorm f p (μ + ν) :=
  snorm_mono_measure f <| Measure.le_add_left <| le_refl _
#align measure_theory.snorm_le_add_measure_left MeasureTheory.snorm_le_add_measure_left

theorem Memℒp.left_of_add_measure {f : α → E} (h : Memℒp f p (μ + ν)) : Memℒp f p μ :=
  h.mono_measure <| Measure.le_add_right <| le_refl _
#align measure_theory.mem_ℒp.left_of_add_measure MeasureTheory.Memℒp.left_of_add_measure

theorem Memℒp.right_of_add_measure {f : α → E} (h : Memℒp f p (μ + ν)) : Memℒp f p ν :=
  h.mono_measure <| Measure.le_add_left <| le_refl _
#align measure_theory.mem_ℒp.right_of_add_measure MeasureTheory.Memℒp.right_of_add_measure

theorem Memℒp.norm {f : α → E} (h : Memℒp f p μ) : Memℒp (fun x => ‖f x‖) p μ :=
  h.of_le h.aestronglyMeasurable.norm (eventually_of_forall fun x => by simp)
#align measure_theory.mem_ℒp.norm MeasureTheory.Memℒp.norm

theorem memℒp_norm_iff {f : α → E} (hf : AEStronglyMeasurable f μ) :
    Memℒp (fun x => ‖f x‖) p μ ↔ Memℒp f p μ :=
  ⟨fun h => ⟨hf, by rw [← snorm_norm]; exact h.2⟩, fun h => h.norm⟩
#align measure_theory.mem_ℒp_norm_iff MeasureTheory.memℒp_norm_iff

theorem snorm'_eq_zero_of_ae_zero {f : α → F} (hq0_lt : 0 < q) (hf_zero : f =ᵐ[μ] 0) :
    snorm' f q μ = 0 := by rw [snorm'_congr_ae hf_zero, snorm'_zero hq0_lt]
#align measure_theory.snorm'_eq_zero_of_ae_zero MeasureTheory.snorm'_eq_zero_of_ae_zero

theorem snorm'_eq_zero_of_ae_zero' (hq0_ne : q ≠ 0) (hμ : μ ≠ 0) {f : α → F} (hf_zero : f =ᵐ[μ] 0) :
    snorm' f q μ = 0 := by rw [snorm'_congr_ae hf_zero, snorm'_zero' hq0_ne hμ]
#align measure_theory.snorm'_eq_zero_of_ae_zero' MeasureTheory.snorm'_eq_zero_of_ae_zero'

theorem ae_eq_zero_of_snorm'_eq_zero {f : α → E} (hq0 : 0 ≤ q) (hf : AEStronglyMeasurable f μ)
    (h : snorm' f q μ = 0) : f =ᵐ[μ] 0 := by
  rw [snorm', ENNReal.rpow_eq_zero_iff] at h
  cases h with
  | inl h =>
    rw [lintegral_eq_zero_iff' (hf.ennnorm.pow_const q)] at h
    refine' h.left.mono fun x hx => _
    rw [Pi.zero_apply, ENNReal.rpow_eq_zero_iff] at hx
    cases hx with
    | inl hx =>
      cases' hx with hx _
      rwa [← ENNReal.coe_zero, ENNReal.coe_eq_coe, nnnorm_eq_zero] at hx
    | inr hx =>
      exact absurd hx.left ENNReal.coe_ne_top
  | inr h =>
    exfalso
    rw [one_div, inv_lt_zero] at h
    exact hq0.not_lt h.right
#align measure_theory.ae_eq_zero_of_snorm'_eq_zero MeasureTheory.ae_eq_zero_of_snorm'_eq_zero

theorem snorm'_eq_zero_iff (hq0_lt : 0 < q) {f : α → E} (hf : AEStronglyMeasurable f μ) :
    snorm' f q μ = 0 ↔ f =ᵐ[μ] 0 :=
  ⟨ae_eq_zero_of_snorm'_eq_zero (le_of_lt hq0_lt) hf, snorm'_eq_zero_of_ae_zero hq0_lt⟩
#align measure_theory.snorm'_eq_zero_iff MeasureTheory.snorm'_eq_zero_iff

theorem coe_nnnorm_ae_le_snormEssSup {_ : MeasurableSpace α} (f : α → F) (μ : Measure α) :
    ∀ᵐ x ∂μ, (‖f x‖₊ : ℝ≥0∞) ≤ snormEssSup f μ :=
  ENNReal.ae_le_essSup fun x => (‖f x‖₊ : ℝ≥0∞)
#align measure_theory.coe_nnnorm_ae_le_snorm_ess_sup MeasureTheory.coe_nnnorm_ae_le_snormEssSup

@[simp]
theorem snormEssSup_eq_zero_iff {f : α → F} : snormEssSup f μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp [EventuallyEq, snormEssSup]
#align measure_theory.snorm_ess_sup_eq_zero_iff MeasureTheory.snormEssSup_eq_zero_iff

theorem snorm_eq_zero_iff {f : α → E} (hf : AEStronglyMeasurable f μ) (h0 : p ≠ 0) :
    snorm f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  by_cases h_top : p = ∞
  · rw [h_top, snorm_exponent_top, snormEssSup_eq_zero_iff]
  rw [snorm_eq_snorm' h0 h_top]
  exact snorm'_eq_zero_iff (ENNReal.toReal_pos h0 h_top) hf
#align measure_theory.snorm_eq_zero_iff MeasureTheory.snorm_eq_zero_iff

theorem snorm'_add_le {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hq1 : 1 ≤ q) : snorm' (f + g) q μ ≤ snorm' f q μ + snorm' g q μ :=
  calc
    (∫⁻ a, (‖(f + g) a‖₊ : ℝ≥0∞) ^ q ∂μ) ^ (1 / q) ≤
        (∫⁻ a, ((fun a => (‖f a‖₊ : ℝ≥0∞)) + fun a => (‖g a‖₊ : ℝ≥0∞)) a ^ q ∂μ) ^ (1 / q) := by
      refine' ENNReal.rpow_le_rpow _ (by simp [le_trans zero_le_one hq1] : 0 ≤ 1 / q)
      refine' lintegral_mono fun a => ENNReal.rpow_le_rpow _ (le_trans zero_le_one hq1)
      simp only [Pi.add_apply, ← ENNReal.coe_add, ENNReal.coe_le_coe, nnnorm_add_le]
    _ ≤ snorm' f q μ + snorm' g q μ := ENNReal.lintegral_Lp_add_le hf.ennnorm hg.ennnorm hq1
#align measure_theory.snorm'_add_le MeasureTheory.snorm'_add_le

theorem snorm'_add_le_of_le_one {f g : α → E} (hf : AEStronglyMeasurable f μ) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) : snorm' (f + g) q μ ≤ (2 : ℝ≥0∞) ^ (1 / q - 1) * (snorm' f q μ + snorm' g q μ) :=
  calc
    (∫⁻ a, (‖(f + g) a‖₊ : ℝ≥0∞) ^ q ∂μ) ^ (1 / q) ≤
        (∫⁻ a, ((fun a => (‖f a‖₊ : ℝ≥0∞)) + fun a => (‖g a‖₊ : ℝ≥0∞)) a ^ q ∂μ) ^ (1 / q) := by
      refine' ENNReal.rpow_le_rpow _ (by simp [hq0] : 0 ≤ 1 / q)
      refine' lintegral_mono fun a => ENNReal.rpow_le_rpow _ hq0
      simp only [Pi.add_apply, ← ENNReal.coe_add, ENNReal.coe_le_coe, nnnorm_add_le]
    _ ≤ (2 : ℝ≥0∞) ^ (1 / q - 1) * (snorm' f q μ + snorm' g q μ) :=
      ENNReal.lintegral_Lp_add_le_of_le_one hf.ennnorm hq0 hq1
#align measure_theory.snorm'_add_le_of_le_one MeasureTheory.snorm'_add_le_of_le_one

theorem snormEssSup_add_le {f g : α → F} :
    snormEssSup (f + g) μ ≤ snormEssSup f μ + snormEssSup g μ := by
  refine' le_trans (essSup_mono_ae (eventually_of_forall fun x => _)) (ENNReal.essSup_add_le _ _)
  simp_rw [Pi.add_apply, ← ENNReal.coe_add, ENNReal.coe_le_coe]
  exact nnnorm_add_le _ _
#align measure_theory.snorm_ess_sup_add_le MeasureTheory.snormEssSup_add_le

theorem snorm_add_le {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp1 : 1 ≤ p) : snorm (f + g) p μ ≤ snorm f p μ + snorm g p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, snormEssSup_add_le]
  have hp1_real : 1 ≤ p.toReal := by
    rwa [← ENNReal.one_toReal, ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top]
  repeat rw [snorm_eq_snorm' hp0 hp_top]
  exact snorm'_add_le hf hg hp1_real
#align measure_theory.snorm_add_le MeasureTheory.snorm_add_le

/-- A constant for the inequality `‖f + g‖_{L^p} ≤ C * (‖f‖_{L^p} + ‖g‖_{L^p})`. It is equal to `1`
for `p ≥ 1` or `p = 0`, and `2^(1/p-1)` in the more tricky interval `(0, 1)`. -/
def LpAddConst (p : ℝ≥0∞) : ℝ≥0 :=
  if p ∈ Set.Ioo (0 : ℝ≥0∞) 1 then (2 : ℝ≥0) ^ (1 / p.toReal - 1) else 1
#align measure_theory.Lp_add_const MeasureTheory.LpAddConst

theorem LpAddConst_of_one_le {p : ℝ≥0∞} (hp : 1 ≤ p) : LpAddConst p = 1 :=
  if_neg fun h ↦ hp.not_lt h.2
#align measure_theory.Lp_add_const_of_one_le MeasureTheory.LpAddConst_of_one_le

theorem LpAddConst_zero : LpAddConst 0 = 1 := if_neg fun h ↦ h.1.ne rfl
#align measure_theory.Lp_add_const_zero MeasureTheory.LpAddConst_zero

theorem LpAddConst_lt_top (p : ℝ≥0∞) : LpAddConst p < ∞ := ENNReal.coe_lt_top
#align measure_theory.Lp_add_const_lt_top MeasureTheory.LpAddConst_lt_top

theorem snorm_add_le' {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : ℝ≥0∞) : snorm (f + g) p μ ≤ LpAddConst p * (snorm f p μ + snorm g p μ) := by
  rcases eq_or_ne p 0 with (rfl | hp)
  · simp only [snorm_exponent_zero, add_zero, mul_zero, le_zero_iff]
  rcases lt_or_le p 1 with (h'p | h'p)
  · simp only [snorm_eq_snorm' hp (h'p.trans ENNReal.one_lt_top).ne]
    convert snorm'_add_le_of_le_one hf ENNReal.toReal_nonneg _
    · have : p ∈ Set.Ioo (0 : ℝ≥0∞) 1 := ⟨hp.bot_lt, h'p⟩
      simp only [LpAddConst, if_pos this]
      rw [← ENNReal.coe_rpow_of_nonneg, ENNReal.coe_ofNat]
      refine sub_nonneg.2 ((one_le_div ?_).2 ?_)
      · exact ENNReal.toReal_pos hp h'p.ne_top
      · exact ENNReal.toReal_le_coe_of_le_coe h'p.le
    · simpa using ENNReal.toReal_mono ENNReal.one_ne_top h'p.le
  · simp [LpAddConst_of_one_le h'p]
    exact snorm_add_le hf hg h'p
#align measure_theory.snorm_add_le' MeasureTheory.snorm_add_le'

variable (μ E)

/-- Technical lemma to control the addition of functions in `L^p` even for `p < 1`.
Given `δ > 0`, there exists `η` such that two functions bounded by `η` in `L^p`
have a sum bounded by `δ`. One could take any `η < δ / 2` for `p ≥ 1`,
but the point of the lemma is that it works also for `p < 1`.
-/
theorem exists_Lp_half (p : ℝ≥0∞) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ η : ℝ≥0, 0 < η ∧ ∀ (f g : α → E), AEStronglyMeasurable f μ → AEStronglyMeasurable g μ →
      snorm f p μ ≤ η → snorm g p μ ≤ η → snorm (f + g) p μ < δ := by
  obtain ⟨η, hη₀, hηδ⟩ : ∃ η : ℝ≥0, 0 < η ∧ η * (2 * LpAddConst p) < δ :=
    ENNReal.exists_nnreal_pos_mul_lt (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hδ
  refine ⟨η, hη₀, fun f g hfm hgm hf hg ↦ ?_⟩
  calc
    snorm (f + g) p μ ≤ LpAddConst p * (snorm f p μ + snorm g p μ) := snorm_add_le' hfm hgm p
    _ ≤ LpAddConst p * (η + η) := by gcongr
    _ = η * (2 * LpAddConst p) := by ring
    _ < δ := hηδ
#align measure_theory.exists_Lp_half MeasureTheory.exists_Lp_half

variable {μ E}

theorem snorm_sub_le' {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (p : ℝ≥0∞) : snorm (f - g) p μ ≤ LpAddConst p * (snorm f p μ + snorm g p μ) := by
  simpa only [sub_eq_add_neg, snorm_neg] using snorm_add_le' hf hg.neg p
#align measure_theory.snorm_sub_le' MeasureTheory.snorm_sub_le'

theorem snorm_sub_le {f g : α → E} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp : 1 ≤ p) : snorm (f - g) p μ ≤ snorm f p μ + snorm g p μ := by
  simpa [LpAddConst_of_one_le hp] using snorm_sub_le' hf hg p
#align measure_theory.snorm_sub_le MeasureTheory.snorm_sub_le

theorem snorm_add_lt_top {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) :
    snorm (f + g) p μ < ∞ :=
  calc
    snorm (f + g) p μ ≤ LpAddConst p * (snorm f p μ + snorm g p μ) :=
      snorm_add_le' hf.aestronglyMeasurable hg.aestronglyMeasurable p
    _ < ∞ := ENNReal.mul_lt_top ENNReal.coe_ne_top <| ENNReal.add_ne_top.2 ⟨hf.2.ne, hg.2.ne⟩
#align measure_theory.snorm_add_lt_top MeasureTheory.snorm_add_lt_top

theorem ae_le_snormEssSup {f : α → F} : ∀ᵐ y ∂μ, ‖f y‖₊ ≤ snormEssSup f μ :=
  ae_le_essSup
#align measure_theory.ae_le_snorm_ess_sup MeasureTheory.ae_le_snormEssSup

theorem meas_snormEssSup_lt {f : α → F} : μ { y | snormEssSup f μ < ‖f y‖₊ } = 0 :=
  meas_essSup_lt
#align measure_theory.meas_snorm_ess_sup_lt MeasureTheory.meas_snormEssSup_lt

section MapMeasure

variable {β : Type*} {mβ : MeasurableSpace β} {f : α → β} {g : β → E}

theorem snormEssSup_map_measure (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : snormEssSup g (Measure.map f μ) = snormEssSup (g ∘ f) μ :=
  essSup_map_measure hg.ennnorm hf
#align measure_theory.snorm_ess_sup_map_measure MeasureTheory.snormEssSup_map_measure

theorem snorm_map_measure (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    snorm g p (Measure.map f μ) = snorm (g ∘ f) p μ := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, snorm_exponent_zero]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, snorm_exponent_top]
    exact snormEssSup_map_measure hg hf
  simp_rw [snorm_eq_lintegral_rpow_nnnorm hp_zero hp_top]
  rw [lintegral_map' (hg.ennnorm.pow_const p.toReal) hf]
  rfl
#align measure_theory.snorm_map_measure MeasureTheory.snorm_map_measure

theorem memℒp_map_measure_iff (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : Memℒp g p (Measure.map f μ) ↔ Memℒp (g ∘ f) p μ := by
  simp [Memℒp, snorm_map_measure hg hf, hg.comp_aemeasurable hf, hg]
#align measure_theory.mem_ℒp_map_measure_iff MeasureTheory.memℒp_map_measure_iff

theorem Memℒp.comp_of_map (hg : Memℒp g p (Measure.map f μ)) (hf : AEMeasurable f μ) :
    Memℒp (g ∘ f) p μ :=
  (memℒp_map_measure_iff hg.aestronglyMeasurable hf).1 hg

theorem snorm_comp_measurePreserving {ν : MeasureTheory.Measure β} (hg : AEStronglyMeasurable g ν)
    (hf : MeasurePreserving f μ ν) : snorm (g ∘ f) p μ = snorm g p ν :=
  Eq.symm <| hf.map_eq ▸ snorm_map_measure (hf.map_eq ▸ hg) hf.aemeasurable

theorem AEEqFun.snorm_compMeasurePreserving {ν : MeasureTheory.Measure β} (g : β →ₘ[ν] E)
    (hf : MeasurePreserving f μ ν) :
    snorm (g.compMeasurePreserving f hf) p μ = snorm g p ν := by
  rw [snorm_congr_ae (g.coeFn_compMeasurePreserving _)]
  exact snorm_comp_measurePreserving g.aestronglyMeasurable hf

theorem Memℒp.comp_measurePreserving {ν : MeasureTheory.Measure β} (hg : Memℒp g p ν)
    (hf : MeasurePreserving f μ ν) : Memℒp (g ∘ f) p μ :=
  .comp_of_map (hf.map_eq.symm ▸ hg) hf.aemeasurable

theorem _root_.MeasurableEmbedding.snormEssSup_map_measure {g : β → F}
    (hf : MeasurableEmbedding f) : snormEssSup g (Measure.map f μ) = snormEssSup (g ∘ f) μ :=
  hf.essSup_map_measure
#align measurable_embedding.snorm_ess_sup_map_measure MeasurableEmbedding.snormEssSup_map_measure

theorem _root_.MeasurableEmbedding.snorm_map_measure {g : β → F} (hf : MeasurableEmbedding f) :
    snorm g p (Measure.map f μ) = snorm (g ∘ f) p μ := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, snorm_exponent_zero]
  by_cases hp : p = ∞
  · simp_rw [hp, snorm_exponent_top]
    exact hf.essSup_map_measure
  · simp_rw [snorm_eq_lintegral_rpow_nnnorm hp_zero hp]
    rw [hf.lintegral_map]
    rfl
#align measurable_embedding.snorm_map_measure MeasurableEmbedding.snorm_map_measure

theorem _root_.MeasurableEmbedding.memℒp_map_measure_iff {g : β → F} (hf : MeasurableEmbedding f) :
    Memℒp g p (Measure.map f μ) ↔ Memℒp (g ∘ f) p μ := by
  simp_rw [Memℒp, hf.aestronglyMeasurable_map_iff, hf.snorm_map_measure]
#align measurable_embedding.mem_ℒp_map_measure_iff MeasurableEmbedding.memℒp_map_measure_iff

theorem _root_.MeasurableEquiv.memℒp_map_measure_iff (f : α ≃ᵐ β) {g : β → F} :
    Memℒp g p (Measure.map f μ) ↔ Memℒp (g ∘ f) p μ :=
  f.measurableEmbedding.memℒp_map_measure_iff
#align measurable_equiv.mem_ℒp_map_measure_iff MeasurableEquiv.memℒp_map_measure_iff

end MapMeasure

section Trim

theorem snorm'_trim (hm : m ≤ m0) {f : α → E} (hf : StronglyMeasurable[m] f) :
    snorm' f q (ν.trim hm) = snorm' f q ν := by
  simp_rw [snorm']
  congr 1
  refine' lintegral_trim hm _
  refine' @Measurable.pow_const _ _ _ _ _ _ _ m _ (@Measurable.coe_nnreal_ennreal _ m _ _) q
  apply @StronglyMeasurable.measurable
  exact @StronglyMeasurable.nnnorm α m _ _ _ hf
#align measure_theory.snorm'_trim MeasureTheory.snorm'_trim

theorem limsup_trim (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : Measurable[m] f) :
    (ν.trim hm).ae.limsup f = ν.ae.limsup f := by
  simp_rw [limsup_eq]
  suffices h_set_eq : { a : ℝ≥0∞ | ∀ᵐ n ∂ν.trim hm, f n ≤ a } = { a : ℝ≥0∞ | ∀ᵐ n ∂ν, f n ≤ a }
  · rw [h_set_eq]
  ext1 a
  suffices h_meas_eq : ν { x | ¬f x ≤ a } = ν.trim hm { x | ¬f x ≤ a }
  · simp_rw [Set.mem_setOf_eq, ae_iff, h_meas_eq]; rfl
  refine' (trim_measurableSet_eq hm _).symm
  refine' @MeasurableSet.compl _ _ m (@measurableSet_le ℝ≥0∞ _ _ _ _ m _ _ _ _ _ hf _)
  exact @measurable_const _ _ _ m _
#align measure_theory.limsup_trim MeasureTheory.limsup_trim

theorem essSup_trim (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : Measurable[m] f) :
    essSup f (ν.trim hm) = essSup f ν := by
  simp_rw [essSup]
  exact limsup_trim hm hf
#align measure_theory.ess_sup_trim MeasureTheory.essSup_trim

theorem snormEssSup_trim (hm : m ≤ m0) {f : α → E} (hf : StronglyMeasurable[m] f) :
    snormEssSup f (ν.trim hm) = snormEssSup f ν :=
  essSup_trim _ (@StronglyMeasurable.ennnorm _ m _ _ _ hf)
#align measure_theory.snorm_ess_sup_trim MeasureTheory.snormEssSup_trim

theorem snorm_trim (hm : m ≤ m0) {f : α → E} (hf : StronglyMeasurable[m] f) :
    snorm f p (ν.trim hm) = snorm f p ν := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simpa only [h_top, snorm_exponent_top] using snormEssSup_trim hm hf
  simpa only [snorm_eq_snorm' h0 h_top] using snorm'_trim hm hf
#align measure_theory.snorm_trim MeasureTheory.snorm_trim

theorem snorm_trim_ae (hm : m ≤ m0) {f : α → E} (hf : AEStronglyMeasurable f (ν.trim hm)) :
    snorm f p (ν.trim hm) = snorm f p ν := by
  rw [snorm_congr_ae hf.ae_eq_mk, snorm_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk)]
  exact snorm_trim hm hf.stronglyMeasurable_mk
#align measure_theory.snorm_trim_ae MeasureTheory.snorm_trim_ae

theorem memℒp_of_memℒp_trim (hm : m ≤ m0) {f : α → E} (hf : Memℒp f p (ν.trim hm)) : Memℒp f p ν :=
  ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim hm hf.1,
    (le_of_eq (snorm_trim_ae hm hf.1).symm).trans_lt hf.2⟩
#align measure_theory.mem_ℒp_of_mem_ℒp_trim MeasureTheory.memℒp_of_memℒp_trim

end Trim

theorem snorm'_le_snorm'_mul_rpow_measure_univ {p q : ℝ} (hp0_lt : 0 < p) (hpq : p ≤ q) {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    snorm' f p μ ≤ snorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) := by
  have hq0_lt : 0 < q := lt_of_lt_of_le hp0_lt hpq
  by_cases hpq_eq : p = q
  · rw [hpq_eq, sub_self, ENNReal.rpow_zero, mul_one]
  have hpq : p < q := lt_of_le_of_ne hpq hpq_eq
  let g := fun _ : α => (1 : ℝ≥0∞)
  have h_rw : (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p ∂μ) = ∫⁻ a, ((‖f a‖₊ : ℝ≥0∞) * g a) ^ p ∂μ :=
    lintegral_congr fun a => by simp
  repeat' rw [snorm']
  rw [h_rw]
  let r := p * q / (q - p)
  have hpqr : 1 / p = 1 / q + 1 / r := by
    field_simp [(ne_of_lt hp0_lt).symm, (ne_of_lt hq0_lt).symm]
    ring
  calc
    (∫⁻ a : α, (↑‖f a‖₊ * g a) ^ p ∂μ) ^ (1 / p) ≤
        (∫⁻ a : α, ↑‖f a‖₊ ^ q ∂μ) ^ (1 / q) * (∫⁻ a : α, g a ^ r ∂μ) ^ (1 / r) :=
      ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.ennnorm aemeasurable_const
    _ = (∫⁻ a : α, ↑‖f a‖₊ ^ q ∂μ) ^ (1 / q) * μ Set.univ ^ (1 / p - 1 / q) := by
      rw [hpqr]; simp
#align measure_theory.snorm'_le_snorm'_mul_rpow_measure_univ MeasureTheory.snorm'_le_snorm'_mul_rpow_measure_univ

theorem snorm'_le_snormEssSup_mul_rpow_measure_univ (hq_pos : 0 < q) {f : α → F} :
    snorm' f q μ ≤ snormEssSup f μ * μ Set.univ ^ (1 / q) := by
  have h_le : (∫⁻ a : α, (‖f a‖₊ : ℝ≥0∞) ^ q ∂μ) ≤ ∫⁻ _ : α, snormEssSup f μ ^ q ∂μ := by
    refine' lintegral_mono_ae _
    have h_nnnorm_le_snorm_ess_sup := coe_nnnorm_ae_le_snormEssSup f μ
    refine' h_nnnorm_le_snorm_ess_sup.mono fun x hx => ENNReal.rpow_le_rpow hx (le_of_lt hq_pos)
  rw [snorm', ← ENNReal.rpow_one (snormEssSup f μ)]
  nth_rw 2 [← mul_inv_cancel (ne_of_lt hq_pos).symm]
  rw [ENNReal.rpow_mul, one_div, ← ENNReal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 ≤ q⁻¹)]
  refine' ENNReal.rpow_le_rpow _ (by simp [hq_pos.le])
  rwa [lintegral_const] at h_le
#align measure_theory.snorm'_le_snorm_ess_sup_mul_rpow_measure_univ MeasureTheory.snorm'_le_snormEssSup_mul_rpow_measure_univ

theorem snorm_le_snorm_mul_rpow_measure_univ {p q : ℝ≥0∞} (hpq : p ≤ q) {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    snorm f p μ ≤ snorm f q μ * μ Set.univ ^ (1 / p.toReal - 1 / q.toReal) := by
  by_cases hp0 : p = 0
  · simp [hp0, zero_le]
  rw [← Ne.def] at hp0
  have hp0_lt : 0 < p := lt_of_le_of_ne (zero_le _) hp0.symm
  have hq0_lt : 0 < q := lt_of_lt_of_le hp0_lt hpq
  by_cases hq_top : q = ∞
  · simp only [hq_top, _root_.div_zero, one_div, ENNReal.top_toReal, sub_zero, snorm_exponent_top,
      GroupWithZero.inv_zero]
    by_cases hp_top : p = ∞
    · simp only [hp_top, ENNReal.rpow_zero, mul_one, ENNReal.top_toReal, sub_zero,
        GroupWithZero.inv_zero, snorm_exponent_top]
      exact le_rfl
    rw [snorm_eq_snorm' hp0 hp_top]
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0_lt.ne' hp_top
    refine' (snorm'_le_snormEssSup_mul_rpow_measure_univ hp_pos).trans (le_of_eq _)
    congr
    exact one_div _
  have hp_lt_top : p < ∞ := hpq.trans_lt (lt_top_iff_ne_top.mpr hq_top)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0_lt.ne' hp_lt_top.ne
  rw [snorm_eq_snorm' hp0_lt.ne.symm hp_lt_top.ne, snorm_eq_snorm' hq0_lt.ne.symm hq_top]
  have hpq_real : p.toReal ≤ q.toReal := by rwa [ENNReal.toReal_le_toReal hp_lt_top.ne hq_top]
  exact snorm'_le_snorm'_mul_rpow_measure_univ hp_pos hpq_real hf
#align measure_theory.snorm_le_snorm_mul_rpow_measure_univ MeasureTheory.snorm_le_snorm_mul_rpow_measure_univ

theorem snorm'_le_snorm'_of_exponent_le {m : MeasurableSpace α} {p q : ℝ} (hp0_lt : 0 < p)
    (hpq : p ≤ q) (μ : Measure α) [IsProbabilityMeasure μ] {f : α → E}
    (hf : AEStronglyMeasurable f μ) : snorm' f p μ ≤ snorm' f q μ := by
  have h_le_μ := snorm'_le_snorm'_mul_rpow_measure_univ hp0_lt hpq hf
  rwa [measure_univ, ENNReal.one_rpow, mul_one] at h_le_μ
#align measure_theory.snorm'_le_snorm'_of_exponent_le MeasureTheory.snorm'_le_snorm'_of_exponent_le

theorem snorm'_le_snormEssSup (hq_pos : 0 < q) {f : α → F} [IsProbabilityMeasure μ] :
    snorm' f q μ ≤ snormEssSup f μ :=
  le_trans (snorm'_le_snormEssSup_mul_rpow_measure_univ hq_pos) (le_of_eq (by simp [measure_univ]))
#align measure_theory.snorm'_le_snorm_ess_sup MeasureTheory.snorm'_le_snormEssSup

theorem snorm_le_snorm_of_exponent_le {p q : ℝ≥0∞} (hpq : p ≤ q) [IsProbabilityMeasure μ]
    {f : α → E} (hf : AEStronglyMeasurable f μ) : snorm f p μ ≤ snorm f q μ :=
  (snorm_le_snorm_mul_rpow_measure_univ hpq hf).trans (le_of_eq (by simp [measure_univ]))
#align measure_theory.snorm_le_snorm_of_exponent_le MeasureTheory.snorm_le_snorm_of_exponent_le

theorem snorm'_lt_top_of_snorm'_lt_top_of_exponent_le {p q : ℝ} [IsFiniteMeasure μ] {f : α → E}
    (hf : AEStronglyMeasurable f μ) (hfq_lt_top : snorm' f q μ < ∞) (hp_nonneg : 0 ≤ p)
    (hpq : p ≤ q) : snorm' f p μ < ∞ := by
  cases' le_or_lt p 0 with hp_nonpos hp_pos
  · rw [le_antisymm hp_nonpos hp_nonneg]
    simp
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  calc
    snorm' f p μ ≤ snorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) :=
      snorm'_le_snorm'_mul_rpow_measure_univ hp_pos hpq hf
    _ < ∞ := by
      rw [ENNReal.mul_lt_top_iff]
      refine' Or.inl ⟨hfq_lt_top, ENNReal.rpow_lt_top_of_nonneg _ (measure_ne_top μ Set.univ)⟩
      rwa [le_sub_comm, sub_zero, one_div, one_div, inv_le_inv hq_pos hp_pos]
#align measure_theory.snorm'_lt_top_of_snorm'_lt_top_of_exponent_le MeasureTheory.snorm'_lt_top_of_snorm'_lt_top_of_exponent_le

variable (μ)

theorem pow_mul_meas_ge_le_snorm {f : α → E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    (ε * μ { x | ε ≤ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal }) ^ (1 / p.toReal) ≤ snorm f p μ := by
  rw [snorm_eq_lintegral_rpow_nnnorm hp_ne_zero hp_ne_top]
  exact
    ENNReal.rpow_le_rpow (mul_meas_ge_le_lintegral₀ (hf.ennnorm.pow_const _) ε)
      (one_div_nonneg.2 ENNReal.toReal_nonneg)
#align measure_theory.pow_mul_meas_ge_le_snorm MeasureTheory.pow_mul_meas_ge_le_snorm

theorem mul_meas_ge_le_pow_snorm {f : α → E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal } ≤ snorm f p μ ^ p.toReal := by
  have : 1 / p.toReal * p.toReal = 1 := by
    refine' one_div_mul_cancel _
    rw [Ne, ENNReal.toReal_eq_zero_iff]
    exact not_or_of_not hp_ne_zero hp_ne_top
  rw [← ENNReal.rpow_one (ε * μ { x | ε ≤ (‖f x‖₊ : ℝ≥0∞) ^ p.toReal }), ← this, ENNReal.rpow_mul]
  exact
    ENNReal.rpow_le_rpow (pow_mul_meas_ge_le_snorm μ hp_ne_zero hp_ne_top hf ε)
      ENNReal.toReal_nonneg
#align measure_theory.mul_meas_ge_le_pow_snorm MeasureTheory.mul_meas_ge_le_pow_snorm

/-- A version of Markov's inequality using Lp-norms. -/
theorem mul_meas_ge_le_pow_snorm' {f : α → E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) (ε : ℝ≥0∞) :
    ε ^ p.toReal * μ { x | ε ≤ ‖f x‖₊ } ≤ snorm f p μ ^ p.toReal := by
  convert mul_meas_ge_le_pow_snorm μ hp_ne_zero hp_ne_top hf (ε ^ p.toReal) using 4
  ext x
  rw [ENNReal.rpow_le_rpow_iff (ENNReal.toReal_pos hp_ne_zero hp_ne_top)]
#align measure_theory.mul_meas_ge_le_pow_snorm' MeasureTheory.mul_meas_ge_le_pow_snorm'

theorem meas_ge_le_mul_pow_snorm {f : α → E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf : AEStronglyMeasurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    μ { x | ε ≤ ‖f x‖₊ } ≤ ε⁻¹ ^ p.toReal * snorm f p μ ^ p.toReal := by
  by_cases ε = ∞
  · simp [h]
  have hεpow : ε ^ p.toReal ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hε) h).ne.symm
  have hεpow' : ε ^ p.toReal ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg h
  rw [ENNReal.inv_rpow, ← ENNReal.mul_le_mul_left hεpow hεpow', ← mul_assoc,
    ENNReal.mul_inv_cancel hεpow hεpow', one_mul]
  exact mul_meas_ge_le_pow_snorm' μ hp_ne_zero hp_ne_top hf ε
#align measure_theory.meas_ge_le_mul_pow_snorm MeasureTheory.meas_ge_le_mul_pow_snorm

variable {μ}

theorem Memℒp.memℒp_of_exponent_le {p q : ℝ≥0∞} [IsFiniteMeasure μ] {f : α → E} (hfq : Memℒp f q μ)
    (hpq : p ≤ q) : Memℒp f p μ := by
  cases' hfq with hfq_m hfq_lt_top
  by_cases hp0 : p = 0
  · rwa [hp0, memℒp_zero_iff_aestronglyMeasurable]
  rw [← Ne.def] at hp0
  refine' ⟨hfq_m, _⟩
  by_cases hp_top : p = ∞
  · have hq_top : q = ∞ := by rwa [hp_top, top_le_iff] at hpq
    rw [hp_top]
    rwa [hq_top] at hfq_lt_top
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  by_cases hq_top : q = ∞
  · rw [snorm_eq_snorm' hp0 hp_top]
    rw [hq_top, snorm_exponent_top] at hfq_lt_top
    refine' lt_of_le_of_lt (snorm'_le_snormEssSup_mul_rpow_measure_univ hp_pos) _
    refine' ENNReal.mul_lt_top hfq_lt_top.ne _
    exact (ENNReal.rpow_lt_top_of_nonneg (by simp [hp_pos.le]) (measure_ne_top μ Set.univ)).ne
  have hq0 : q ≠ 0 := by
    by_contra hq_eq_zero
    have hp_eq_zero : p = 0 := le_antisymm (by rwa [hq_eq_zero] at hpq) (zero_le _)
    rw [hp_eq_zero, ENNReal.zero_toReal] at hp_pos
    exact (lt_irrefl _) hp_pos
  have hpq_real : p.toReal ≤ q.toReal := by rwa [ENNReal.toReal_le_toReal hp_top hq_top]
  rw [snorm_eq_snorm' hp0 hp_top]
  rw [snorm_eq_snorm' hq0 hq_top] at hfq_lt_top
  exact snorm'_lt_top_of_snorm'_lt_top_of_exponent_le hfq_m hfq_lt_top (le_of_lt hp_pos) hpq_real
#align measure_theory.mem_ℒp.mem_ℒp_of_exponent_le MeasureTheory.Memℒp.memℒp_of_exponent_le

section MeasurableAdd

-- variable [MeasurableAdd₂ E]
theorem snorm'_sum_le {ι} {f : ι → α → E} {s : Finset ι}
    (hfs : ∀ i, i ∈ s → AEStronglyMeasurable (f i) μ) (hq1 : 1 ≤ q) :
    snorm' (∑ i in s, f i) q μ ≤ ∑ i in s, snorm' (f i) q μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α → E => snorm' f q μ)
    (fun f => AEStronglyMeasurable f μ) (snorm'_zero (zero_lt_one.trans_le hq1))
    (fun _f _g hf hg => snorm'_add_le hf hg hq1) (fun _f _g hf hg => hf.add hg) _ hfs
#align measure_theory.snorm'_sum_le MeasureTheory.snorm'_sum_le

theorem snorm_sum_le {ι} {f : ι → α → E} {s : Finset ι}
    (hfs : ∀ i, i ∈ s → AEStronglyMeasurable (f i) μ) (hp1 : 1 ≤ p) :
    snorm (∑ i in s, f i) p μ ≤ ∑ i in s, snorm (f i) p μ :=
  Finset.le_sum_of_subadditive_on_pred (fun f : α → E => snorm f p μ)
    (fun f => AEStronglyMeasurable f μ) snorm_zero (fun _f _g hf hg => snorm_add_le hf hg hp1)
    (fun _f _g hf hg => hf.add hg) _ hfs
#align measure_theory.snorm_sum_le MeasureTheory.snorm_sum_le

theorem Memℒp.add {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) : Memℒp (f + g) p μ :=
  ⟨AEStronglyMeasurable.add hf.1 hg.1, snorm_add_lt_top hf hg⟩
#align measure_theory.mem_ℒp.add MeasureTheory.Memℒp.add

theorem Memℒp.sub {f g : α → E} (hf : Memℒp f p μ) (hg : Memℒp g p μ) : Memℒp (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg
#align measure_theory.mem_ℒp.sub MeasureTheory.Memℒp.sub

theorem memℒp_finset_sum {ι} (s : Finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, Memℒp (f i) p μ) :
    Memℒp (fun a => ∑ i in s, f i a) p μ := by
  haveI : DecidableEq ι := Classical.decEq _
  revert hf
  refine' Finset.induction_on s _ _
  · simp only [zero_mem_ℒp', Finset.sum_empty, imp_true_iff]
  · intro i s his ih hf
    simp only [his, Finset.sum_insert, not_false_iff]
    exact (hf i (s.mem_insert_self i)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
#align measure_theory.mem_ℒp_finset_sum MeasureTheory.memℒp_finset_sum

theorem memℒp_finset_sum' {ι} (s : Finset ι) {f : ι → α → E} (hf : ∀ i ∈ s, Memℒp (f i) p μ) :
    Memℒp (∑ i in s, f i) p μ := by
  convert memℒp_finset_sum s hf using 1
  ext x
  simp
#align measure_theory.mem_ℒp_finset_sum' MeasureTheory.memℒp_finset_sum'

end MeasurableAdd

section Monotonicity

theorem snorm'_le_nnreal_smul_snorm'_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) {p : ℝ} (hp : 0 < p) : snorm' f p μ ≤ c • snorm' g p μ := by
  simp_rw [snorm']
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.smul_def, smul_eq_mul,
    ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel hp.ne.symm, ENNReal.rpow_one,
    ENNReal.coe_rpow_of_nonneg _ hp.le, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top, ←
    ENNReal.coe_mul]
  apply lintegral_mono_ae
  simp_rw [ENNReal.coe_le_coe, ← NNReal.mul_rpow, NNReal.rpow_le_rpow_iff hp]
  exact h
#align measure_theory.snorm'_le_nnreal_smul_snorm'_of_ae_le_mul MeasureTheory.snorm'_le_nnreal_smul_snorm'_of_ae_le_mul

theorem snormEssSup_le_nnreal_smul_snormEssSup_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : snormEssSup f μ ≤ c • snormEssSup g μ :=
  calc
    essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ ≤ essSup (fun x => (↑(c * ‖g x‖₊) : ℝ≥0∞)) μ :=
      essSup_mono_ae <| h.mono fun x hx => ENNReal.coe_le_coe.mpr hx
    _ = essSup (fun x => (c * ‖g x‖₊ : ℝ≥0∞)) μ := by simp_rw [ENNReal.coe_mul]
    _ = c • essSup (fun x => (‖g x‖₊ : ℝ≥0∞)) μ := ENNReal.essSup_const_mul
#align measure_theory.snorm_ess_sup_le_nnreal_smul_snorm_ess_sup_of_ae_le_mul MeasureTheory.snormEssSup_le_nnreal_smul_snormEssSup_of_ae_le_mul

theorem snorm_le_nnreal_smul_snorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) (p : ℝ≥0∞) : snorm f p μ ≤ c • snorm g p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · rw [h_top]
    exact snormEssSup_le_nnreal_smul_snormEssSup_of_ae_le_mul h
  simp_rw [snorm_eq_snorm' h0 h_top]
  exact snorm'_le_nnreal_smul_snorm'_of_ae_le_mul h (ENNReal.toReal_pos h0 h_top)
#align measure_theory.snorm_le_nnreal_smul_snorm_of_ae_le_mul MeasureTheory.snorm_le_nnreal_smul_snorm_of_ae_le_mul

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
`snorm` of `0`. -/
theorem snorm_eq_zero_and_zero_of_ae_le_mul_neg {f : α → F} {g : α → G} {c : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (hc : c < 0) (p : ℝ≥0∞) :
    snorm f p μ = 0 ∧ snorm g p μ = 0 := by
  simp_rw [le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg (norm_nonneg _) hc (norm_nonneg _),
    norm_eq_zero, eventually_and] at h
  change f =ᵐ[μ] 0 ∧ g =ᵐ[μ] 0 at h
  simp [snorm_congr_ae h.1, snorm_congr_ae h.2]
#align measure_theory.snorm_eq_zero_and_zero_of_ae_le_mul_neg MeasureTheory.snorm_eq_zero_and_zero_of_ae_le_mul_neg

theorem snorm_le_mul_snorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (p : ℝ≥0∞) : snorm f p μ ≤ ENNReal.ofReal c * snorm g p μ :=
  snorm_le_nnreal_smul_snorm_of_ae_le_mul
    (h.mono fun _x hx => hx.trans <| mul_le_mul_of_nonneg_right c.le_coe_toNNReal (norm_nonneg _)) _
#align measure_theory.snorm_le_mul_snorm_of_ae_le_mul MeasureTheory.snorm_le_mul_snorm_of_ae_le_mul

theorem Memℒp.of_nnnorm_le_mul {f : α → E} {g : α → F} {c : ℝ≥0} (hg : Memℒp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : Memℒp f p μ :=
  ⟨hf,
    (snorm_le_nnreal_smul_snorm_of_ae_le_mul hfg p).trans_lt <|
      ENNReal.mul_lt_top ENNReal.coe_ne_top hg.snorm_ne_top⟩
#align measure_theory.mem_ℒp.of_nnnorm_le_mul MeasureTheory.Memℒp.of_nnnorm_le_mul

theorem Memℒp.of_le_mul {f : α → E} {g : α → F} {c : ℝ} (hg : Memℒp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : Memℒp f p μ :=
  ⟨hf,
    (snorm_le_mul_snorm_of_ae_le_mul hfg p).trans_lt <|
      ENNReal.mul_lt_top ENNReal.ofReal_ne_top hg.snorm_ne_top⟩
#align measure_theory.mem_ℒp.of_le_mul MeasureTheory.Memℒp.of_le_mul

theorem snorm'_le_snorm'_mul_snorm' {p q r : ℝ} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {g : α → F} (hg : AEStronglyMeasurable g μ) (b : E → F → G)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊) (hp0_lt : 0 < p) (hpq : p < q)
    (hpqr : 1 / p = 1 / q + 1 / r) :
    snorm' (fun x => b (f x) (g x)) p μ ≤ snorm' f q μ * snorm' g r μ := by
  rw [snorm']
  calc
    (∫⁻ a : α, ↑‖b (f a) (g a)‖₊ ^ p ∂μ) ^ (1 / p) ≤
        (∫⁻ a : α, ↑(‖f a‖₊ * ‖g a‖₊) ^ p ∂μ) ^ (1 / p) :=
      (ENNReal.rpow_le_rpow_iff <| one_div_pos.mpr hp0_lt).mpr <|
        lintegral_mono_ae <|
          h.mono fun a ha => (ENNReal.rpow_le_rpow_iff hp0_lt).mpr <| ENNReal.coe_le_coe.mpr <| ha
    _ ≤ _ := ?_
  simp_rw [snorm', ENNReal.coe_mul]
  exact ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.ennnorm hg.ennnorm
#align measure_theory.snorm'_le_snorm'_mul_snorm' MeasureTheory.snorm'_le_snorm'_mul_snorm'

theorem snorm_le_snorm_top_mul_snorm (p : ℝ≥0∞) (f : α → E) {g : α → F}
    (hg : AEStronglyMeasurable g μ) (b : E → F → G)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊) :
    snorm (fun x => b (f x) (g x)) p μ ≤ snorm f ∞ μ * snorm g p μ := by
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, snorm_exponent_top]
    refine' le_trans (essSup_mono_ae <| h.mono fun a ha => _) (ENNReal.essSup_mul_le _ _)
    simp_rw [Pi.mul_apply, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    exact ha
  by_cases hp_zero : p = 0
  · simp only [hp_zero, snorm_exponent_zero, mul_zero, le_zero_iff]
  simp_rw [snorm_eq_lintegral_rpow_nnnorm hp_zero hp_top, snorm_exponent_top, snormEssSup]
  calc
    (∫⁻ x, (‖b (f x) (g x)‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal) ≤
        (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal * (‖g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
      refine' ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr ENNReal.toReal_nonneg)
      refine' lintegral_mono_ae (h.mono fun a ha => _)
      rw [← ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
      refine' ENNReal.rpow_le_rpow _ ENNReal.toReal_nonneg
      rw [← ENNReal.coe_mul, ENNReal.coe_le_coe]
      exact ha
    _ ≤
        (∫⁻ x, essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ ^ p.toReal * (‖g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^
          (1 / p.toReal) := by
      refine' ENNReal.rpow_le_rpow _ _
      swap;
      · rw [one_div_nonneg]
        exact ENNReal.toReal_nonneg
      refine' lintegral_mono_ae _
      filter_upwards [@ENNReal.ae_le_essSup _ _ μ fun x => (‖f x‖₊ : ℝ≥0∞)]with x hx
      exact mul_le_mul_right' (ENNReal.rpow_le_rpow hx ENNReal.toReal_nonneg) _
    _ = essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ *
        (∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
      rw [lintegral_const_mul'']
      swap; · exact hg.nnnorm.aemeasurable.coe_nnreal_ennreal.pow aemeasurable_const
      rw [ENNReal.mul_rpow_of_nonneg]
      swap;
      · rw [one_div_nonneg]
        exact ENNReal.toReal_nonneg
      rw [← ENNReal.rpow_mul, one_div, mul_inv_cancel, ENNReal.rpow_one]
      rw [Ne.def, ENNReal.toReal_eq_zero_iff, not_or]
      exact ⟨hp_zero, hp_top⟩
#align measure_theory.snorm_le_snorm_top_mul_snorm MeasureTheory.snorm_le_snorm_top_mul_snorm

theorem snorm_le_snorm_mul_snorm_top (p : ℝ≥0∞) {f : α → E} (hf : AEStronglyMeasurable f μ)
    (g : α → F) (b : E → F → G) (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊) :
    snorm (fun x => b (f x) (g x)) p μ ≤ snorm f p μ * snorm g ∞ μ := by
  rw [← snorm_norm f, ← snorm_norm g]
  refine' (snorm_mono_ae_real h).trans _
  simp_rw [mul_comm ‖f _‖₊, val_eq_coe, NNReal.coe_mul, coe_nnnorm]
  rw [mul_comm]
  refine' snorm_le_snorm_top_mul_snorm p (fun x => ‖g x‖) hf.norm _ (h.mono fun x _ => _)
  simp_rw [nnnorm_mul]
  rfl
#align measure_theory.snorm_le_snorm_mul_snorm_top MeasureTheory.snorm_le_snorm_mul_snorm_top

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
theorem snorm_le_snorm_mul_snorm_of_nnnorm {p q r : ℝ≥0∞} {f : α → E}
    (hf : AEStronglyMeasurable f μ) {g : α → F} (hg : AEStronglyMeasurable g μ) (b : E → F → G)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊) (hpqr : 1 / p = 1 / q + 1 / r) :
    snorm (fun x => b (f x) (g x)) p μ ≤ snorm f q μ * snorm g r μ := by
  by_cases hp_zero : p = 0
  · simp [hp_zero]
  have hq_ne_zero : q ≠ 0 := by
    intro hq_zero
    simp only [hq_zero, hp_zero, one_div, ENNReal.inv_zero, top_add, ENNReal.inv_eq_top] at hpqr
  have hr_ne_zero : r ≠ 0 := by
    intro hr_zero
    simp only [hr_zero, hp_zero, one_div, ENNReal.inv_zero, add_top, ENNReal.inv_eq_top] at hpqr
  by_cases hq_top : q = ∞
  · have hpr : p = r := by
      simpa only [hq_top, one_div, ENNReal.inv_top, zero_add, inv_inj] using hpqr
    rw [← hpr, hq_top]
    exact snorm_le_snorm_top_mul_snorm p f hg b h
  by_cases hr_top : r = ∞
  · have hpq : p = q := by
      simpa only [hr_top, one_div, ENNReal.inv_top, add_zero, inv_inj] using hpqr
    rw [← hpq, hr_top]
    exact snorm_le_snorm_mul_snorm_top p hf g b h
  have hpq : p < q := by
    suffices 1 / q < 1 / p by rwa [one_div, one_div, ENNReal.inv_lt_inv] at this
    rw [hpqr]
    refine' ENNReal.lt_add_right _ _
    · simp only [hq_ne_zero, one_div, Ne.def, ENNReal.inv_eq_top, not_false_iff]
    · simp only [hr_top, one_div, Ne.def, ENNReal.inv_eq_zero, not_false_iff]
  rw [snorm_eq_snorm' hp_zero (hpq.trans_le le_top).ne, snorm_eq_snorm' hq_ne_zero hq_top,
    snorm_eq_snorm' hr_ne_zero hr_top]
  refine' snorm'_le_snorm'_mul_snorm' hf hg _ h _ _ _
  · exact ENNReal.toReal_pos hp_zero (hpq.trans_le le_top).ne
  · exact ENNReal.toReal_strict_mono hq_top hpq
  rw [← ENNReal.one_toReal, ← ENNReal.toReal_div, ← ENNReal.toReal_div, ← ENNReal.toReal_div, hpqr,
    ENNReal.toReal_add]
  · simp only [hq_ne_zero, one_div, Ne.def, ENNReal.inv_eq_top, not_false_iff]
  · simp only [hr_ne_zero, one_div, Ne.def, ENNReal.inv_eq_top, not_false_iff]
#align measure_theory.snorm_le_snorm_mul_snorm_of_nnnorm MeasureTheory.snorm_le_snorm_mul_snorm_of_nnnorm

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
theorem snorm_le_snorm_mul_snorm'_of_norm {p q r : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {g : α → F} (hg : AEStronglyMeasurable g μ) (b : E → F → G)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ ≤ ‖f x‖ * ‖g x‖) (hpqr : 1 / p = 1 / q + 1 / r) :
    snorm (fun x => b (f x) (g x)) p μ ≤ snorm f q μ * snorm g r μ :=
  snorm_le_snorm_mul_snorm_of_nnnorm hf hg b h hpqr
#align measure_theory.snorm_le_snorm_mul_snorm'_of_norm MeasureTheory.snorm_le_snorm_mul_snorm'_of_norm

end Monotonicity

/-!
### Bounded actions by normed rings
In this section we show inequalities on the norm.
-/


section BoundedSMul

variable {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 E] [MulActionWithZero 𝕜 F]

variable [BoundedSMul 𝕜 E] [BoundedSMul 𝕜 F]

theorem snorm'_const_smul_le (c : 𝕜) (f : α → F) (hq_pos : 0 < q) :
    snorm' (c • f) q μ ≤ ‖c‖₊ • snorm' f q μ :=
  snorm'_le_nnreal_smul_snorm'_of_ae_le_mul (eventually_of_forall fun _ => nnnorm_smul_le _ _)
    hq_pos
#align measure_theory.snorm'_const_smul_le MeasureTheory.snorm'_const_smul_le

theorem snormEssSup_const_smul_le (c : 𝕜) (f : α → F) :
    snormEssSup (c • f) μ ≤ ‖c‖₊ • snormEssSup f μ :=
  snormEssSup_le_nnreal_smul_snormEssSup_of_ae_le_mul
    (eventually_of_forall fun _ => nnnorm_smul_le _ _)
#align measure_theory.snorm_ess_sup_const_smul_le MeasureTheory.snormEssSup_const_smul_le

theorem snorm_const_smul_le (c : 𝕜) (f : α → F) : snorm (c • f) p μ ≤ ‖c‖₊ • snorm f p μ :=
  snorm_le_nnreal_smul_snorm_of_ae_le_mul (eventually_of_forall fun _ => nnnorm_smul_le _ _) _
#align measure_theory.snorm_const_smul_le MeasureTheory.snorm_const_smul_le

theorem Memℒp.const_smul {f : α → E} (hf : Memℒp f p μ) (c : 𝕜) : Memℒp (c • f) p μ :=
  ⟨AEStronglyMeasurable.const_smul hf.1 c,
    (snorm_const_smul_le c f).trans_lt (ENNReal.mul_lt_top ENNReal.coe_ne_top hf.2.ne)⟩
#align measure_theory.mem_ℒp.const_smul MeasureTheory.Memℒp.const_smul

theorem Memℒp.const_mul {R} [NormedRing R] {f : α → R} (hf : Memℒp f p μ) (c : R) :
    Memℒp (fun x => c * f x) p μ :=
  hf.const_smul c
#align measure_theory.mem_ℒp.const_mul MeasureTheory.Memℒp.const_mul

theorem snorm'_smul_le_mul_snorm' {p q r : ℝ} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {φ : α → 𝕜} (hφ : AEStronglyMeasurable φ μ) (hp0_lt : 0 < p) (hpq : p < q)
    (hpqr : 1 / p = 1 / q + 1 / r) : snorm' (φ • f) p μ ≤ snorm' φ q μ * snorm' f r μ :=
  snorm'_le_snorm'_mul_snorm' hφ hf (· • ·) (eventually_of_forall fun _ => nnnorm_smul_le _ _)
    hp0_lt hpq hpqr
#align measure_theory.snorm'_smul_le_mul_snorm' MeasureTheory.snorm'_smul_le_mul_snorm'

theorem snorm_smul_le_snorm_top_mul_snorm (p : ℝ≥0∞) {f : α → E} (hf : AEStronglyMeasurable f μ)
    (φ : α → 𝕜) : snorm (φ • f) p μ ≤ snorm φ ∞ μ * snorm f p μ :=
  (snorm_le_snorm_top_mul_snorm p φ hf (· • ·) (eventually_of_forall fun _ => nnnorm_smul_le _ _) :
    _)
#align measure_theory.snorm_smul_le_snorm_top_mul_snorm MeasureTheory.snorm_smul_le_snorm_top_mul_snorm

theorem snorm_smul_le_snorm_mul_snorm_top (p : ℝ≥0∞) (f : α → E) {φ : α → 𝕜}
    (hφ : AEStronglyMeasurable φ μ) : snorm (φ • f) p μ ≤ snorm φ p μ * snorm f ∞ μ :=
  (snorm_le_snorm_mul_snorm_top p hφ f (· • ·) (eventually_of_forall fun _ => nnnorm_smul_le _ _) :
    _)
#align measure_theory.snorm_smul_le_snorm_mul_snorm_top MeasureTheory.snorm_smul_le_snorm_mul_snorm_top

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of a scalar product `φ • f`. -/
theorem snorm_smul_le_mul_snorm {p q r : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {φ : α → 𝕜} (hφ : AEStronglyMeasurable φ μ) (hpqr : 1 / p = 1 / q + 1 / r) :
    snorm (φ • f) p μ ≤ snorm φ q μ * snorm f r μ :=
  (snorm_le_snorm_mul_snorm_of_nnnorm hφ hf (· • ·)
      (eventually_of_forall fun _ => nnnorm_smul_le _ _) hpqr :
    _)
#align measure_theory.snorm_smul_le_mul_snorm MeasureTheory.snorm_smul_le_mul_snorm

theorem Memℒp.smul {p q r : ℝ≥0∞} {f : α → E} {φ : α → 𝕜} (hf : Memℒp f r μ) (hφ : Memℒp φ q μ)
    (hpqr : 1 / p = 1 / q + 1 / r) : Memℒp (φ • f) p μ :=
  ⟨hφ.1.smul hf.1,
    (snorm_smul_le_mul_snorm hf.1 hφ.1 hpqr).trans_lt
      (ENNReal.mul_lt_top hφ.snorm_ne_top hf.snorm_ne_top)⟩
#align measure_theory.mem_ℒp.smul MeasureTheory.Memℒp.smul

theorem Memℒp.smul_of_top_right {p : ℝ≥0∞} {f : α → E} {φ : α → 𝕜} (hf : Memℒp f p μ)
    (hφ : Memℒp φ ∞ μ) : Memℒp (φ • f) p μ := by
  apply hf.smul hφ
  simp only [ENNReal.div_top, zero_add]
#align measure_theory.mem_ℒp.smul_of_top_right MeasureTheory.Memℒp.smul_of_top_right

theorem Memℒp.smul_of_top_left {p : ℝ≥0∞} {f : α → E} {φ : α → 𝕜} (hf : Memℒp f ∞ μ)
    (hφ : Memℒp φ p μ) : Memℒp (φ • f) p μ := by
  apply hf.smul hφ
  simp only [ENNReal.div_top, add_zero]
#align measure_theory.mem_ℒp.smul_of_top_left MeasureTheory.Memℒp.smul_of_top_left

end BoundedSMul

/-!
### Bounded actions by normed division rings
The inequalities in the previous section are now tight.
-/


section NormedSpace

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [MulActionWithZero 𝕜 E] [Module 𝕜 F]

variable [BoundedSMul 𝕜 E] [BoundedSMul 𝕜 F]

theorem snorm'_const_smul {f : α → F} (c : 𝕜) (hq_pos : 0 < q) :
    snorm' (c • f) q μ = ‖c‖₊ • snorm' f q μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp [snorm', hq_pos]
  refine' le_antisymm (snorm'_const_smul_le _ _ hq_pos) _
  have : snorm' _ q μ ≤ _ := snorm'_const_smul_le c⁻¹ (c • f) hq_pos
  rwa [inv_smul_smul₀ hc, nnnorm_inv, ENNReal.le_inv_smul_iff (nnnorm_ne_zero_iff.mpr hc)] at this
#align measure_theory.snorm'_const_smul MeasureTheory.snorm'_const_smul

theorem snormEssSup_const_smul (c : 𝕜) (f : α → F) :
    snormEssSup (c • f) μ = (‖c‖₊ : ℝ≥0∞) * snormEssSup f μ := by
  simp_rw [snormEssSup, Pi.smul_apply, nnnorm_smul, ENNReal.coe_mul, ENNReal.essSup_const_mul]
#align measure_theory.snorm_ess_sup_const_smul MeasureTheory.snormEssSup_const_smul

theorem snorm_const_smul (c : 𝕜) (f : α → F) :
    snorm (c • f) p μ = (‖c‖₊ : ℝ≥0∞) * snorm f p μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  refine' le_antisymm (snorm_const_smul_le _ _) _
  have : snorm _ p μ ≤ _ := snorm_const_smul_le c⁻¹ (c • f)
  rwa [inv_smul_smul₀ hc, nnnorm_inv, ENNReal.le_inv_smul_iff (nnnorm_ne_zero_iff.mpr hc)] at this
#align measure_theory.snorm_const_smul MeasureTheory.snorm_const_smul

end NormedSpace

theorem snorm_indicator_ge_of_bdd_below (hp : p ≠ 0) (hp' : p ≠ ∞) {f : α → F} (C : ℝ≥0) {s : Set α}
    (hs : MeasurableSet s) (hf : ∀ᵐ x ∂μ, x ∈ s → C ≤ ‖s.indicator f x‖₊) :
    C • μ s ^ (1 / p.toReal) ≤ snorm (s.indicator f) p μ := by
  rw [ENNReal.smul_def, smul_eq_mul, snorm_eq_lintegral_rpow_nnnorm hp hp',
    ENNReal.le_rpow_one_div_iff (ENNReal.toReal_pos hp hp'),
    ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, ← ENNReal.rpow_mul,
    one_div_mul_cancel (ENNReal.toReal_pos hp hp').ne.symm, ENNReal.rpow_one, ← set_lintegral_const,
    ← lintegral_indicator _ hs]
  refine' lintegral_mono_ae _
  filter_upwards [hf] with x hx
  rw [nnnorm_indicator_eq_indicator_nnnorm]
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs] at hx ⊢
    exact ENNReal.rpow_le_rpow (ENNReal.coe_le_coe.2 (hx hxs)) ENNReal.toReal_nonneg
  · simp [Set.indicator_of_not_mem hxs]
#align measure_theory.snorm_indicator_ge_of_bdd_below MeasureTheory.snorm_indicator_ge_of_bdd_below

section IsROrC

variable {𝕜 : Type*} [IsROrC 𝕜] {f : α → 𝕜}

theorem Memℒp.re (hf : Memℒp f p μ) : Memℒp (fun x => IsROrC.re (f x)) p μ := by
  have : ∀ x, ‖IsROrC.re (f x)‖ ≤ 1 * ‖f x‖ := by
    intro x
    rw [one_mul]
    exact IsROrC.norm_re_le_norm (f x)
  refine' hf.of_le_mul _ (eventually_of_forall this)
  exact IsROrC.continuous_re.comp_aestronglyMeasurable hf.1
#align measure_theory.mem_ℒp.re MeasureTheory.Memℒp.re

theorem Memℒp.im (hf : Memℒp f p μ) : Memℒp (fun x => IsROrC.im (f x)) p μ := by
  have : ∀ x, ‖IsROrC.im (f x)‖ ≤ 1 * ‖f x‖ := by
    intro x
    rw [one_mul]
    exact IsROrC.norm_im_le_norm (f x)
  refine' hf.of_le_mul _ (eventually_of_forall this)
  exact IsROrC.continuous_im.comp_aestronglyMeasurable hf.1
#align measure_theory.mem_ℒp.im MeasureTheory.Memℒp.im

end IsROrC

section Liminf

variable [MeasurableSpace E] [OpensMeasurableSpace E] {R : ℝ≥0}

theorem ae_bdd_liminf_atTop_rpow_of_snorm_bdd {p : ℝ≥0∞} {f : ℕ → α → E}
    (hfmeas : ∀ n, Measurable (f n)) (hbdd : ∀ n, snorm (f n) p μ ≤ R) :
    ∀ᵐ x ∂μ, liminf (fun n => ((‖f n x‖₊ : ℝ≥0∞) ^ p.toReal : ℝ≥0∞)) atTop < ∞ := by
  by_cases hp0 : p.toReal = 0
  · simp only [hp0, ENNReal.rpow_zero]
    refine' eventually_of_forall fun x => _
    rw [liminf_const (1 : ℝ≥0∞)]
    exact ENNReal.one_lt_top
  have hp : p ≠ 0 := fun h => by simp [h] at hp0
  have hp' : p ≠ ∞ := fun h => by simp [h] at hp0
  refine'
    ae_lt_top (measurable_liminf fun n => (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.toReal)
      (lt_of_le_of_lt
          (lintegral_liminf_le fun n => (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.toReal)
          (lt_of_le_of_lt _
            (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.coe_ne_top :
              (R : ℝ≥0∞) ^ p.toReal < ∞))).ne
  simp_rw [snorm_eq_lintegral_rpow_nnnorm hp hp'] at hbdd
  simp_rw [liminf_eq, eventually_atTop]
  exact
    sSup_le fun b ⟨a, ha⟩ =>
      (ha a le_rfl).trans ((ENNReal.rpow_one_div_le_iff (ENNReal.toReal_pos hp hp')).1 (hbdd _))
#align measure_theory.ae_bdd_liminf_at_top_rpow_of_snorm_bdd MeasureTheory.ae_bdd_liminf_atTop_rpow_of_snorm_bdd

theorem ae_bdd_liminf_atTop_of_snorm_bdd {p : ℝ≥0∞} (hp : p ≠ 0) {f : ℕ → α → E}
    (hfmeas : ∀ n, Measurable (f n)) (hbdd : ∀ n, snorm (f n) p μ ≤ R) :
    ∀ᵐ x ∂μ, liminf (fun n => (‖f n x‖₊ : ℝ≥0∞)) atTop < ∞ := by
  by_cases hp' : p = ∞
  · subst hp'
    simp_rw [snorm_exponent_top] at hbdd
    have : ∀ n, ∀ᵐ x ∂μ, (‖f n x‖₊ : ℝ≥0∞) < R + 1 := fun n =>
      ae_lt_of_essSup_lt
        (lt_of_le_of_lt (hbdd n) <| ENNReal.lt_add_right ENNReal.coe_ne_top one_ne_zero)
    rw [← ae_all_iff] at this
    filter_upwards [this]with x hx using lt_of_le_of_lt
        (liminf_le_of_frequently_le' <| frequently_of_forall fun n => (hx n).le)
        (ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.one_lt_top⟩)
  filter_upwards [ae_bdd_liminf_atTop_rpow_of_snorm_bdd hfmeas hbdd] with x hx
  have hppos : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have :
    liminf (fun n => (‖f n x‖₊ : ℝ≥0∞) ^ p.toReal) atTop =
      liminf (fun n => (‖f n x‖₊ : ℝ≥0∞)) atTop ^ p.toReal := by
    change
      liminf (fun n => ENNReal.orderIsoRpow p.toReal hppos (‖f n x‖₊ : ℝ≥0∞)) atTop =
        ENNReal.orderIsoRpow p.toReal hppos (liminf (fun n => (‖f n x‖₊ : ℝ≥0∞)) atTop)
    refine' (OrderIso.liminf_apply (ENNReal.orderIsoRpow p.toReal _) _ _ _ _).symm <;>
      isBoundedDefault
  rw [this] at hx
  rw [← ENNReal.rpow_one (liminf (fun n => ‖f n x‖₊) atTop), ← mul_inv_cancel hppos.ne.symm,
    ENNReal.rpow_mul]
  exact ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 hppos.le) hx.ne
#align measure_theory.ae_bdd_liminf_at_top_of_snorm_bdd MeasureTheory.ae_bdd_liminf_atTop_of_snorm_bdd

end Liminf

/-- A continuous function with compact support belongs to `L^∞`. -/
theorem _root_.Continuous.memℒp_top_of_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {f : X → E} (hf : Continuous f) (h'f : HasCompactSupport f) (μ : Measure X) : Memℒp f ⊤ μ := by
  borelize E
  rcases hf.bounded_above_of_compact_support h'f with ⟨C, hC⟩
  apply memℒp_top_of_bound ?_ C (Filter.eventually_of_forall hC)
  exact (hf.stronglyMeasurable_of_hasCompactSupport h'f).aestronglyMeasurable

end ℒp

end MeasureTheory
