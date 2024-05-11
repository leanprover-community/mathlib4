/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

#align_import measure_theory.function.lp_seminorm from "leanprover-community/mathlib"@"c4015acc0a223449d44061e27ddac1835a3852b9"
/-!
# ℒp seminorm

In this file we define `ℒᵖ` seminorm, denoted by `MeasureTheory.snorm f p μ`.

- For `p = ∞`, it is the essential supemum of `(‖f x‖₊ : ℝ≥0∞)`.
- For `1 ≤ p < ∞`, it is the `p`-th root of the integral of `‖f x‖₊ ^ p`.
- For `0 < p ≤ 1`, it is the integral of `‖f x‖₊ ^ p`.
- For `p = 0`, it is the measure of the support of `f`.

We also define a predicate `MeasureTheory.Memℒp f p μ`,
requesting that a function is almost everywhere strongly measurable and has finite `ℒᵖ` seminorm.

This file contains definitions and a few trivial lemmas about these definitions.
More properties can be found in other files in this folder.

## Implementation notes

While different sources agree on the the choice of a seminorm on `ℒᵖ` for `p ≥ 1`,
there are two competing formulas for `0 < p < 1`:
the integral of `‖f x‖₊ ^ p` and the `p`-th root of this integral.

The former seminorm satisfies the triangle inequality for all `p`
but is not homogeneous in `f`:
we have `snorm (c • f) p μ = ‖c‖₊ ^ p * snorm f p μ`
instead of `snorm (c • f) p μ = ‖c‖₊ * snorm f p μ`
(both formulas omit some type conversions).

The latter formula satisfies `snorm (c • f) p μ = ‖c‖₊ * snorm f p μ`
but needs an extra multiplicative constant in the triangle inequality:
`snorm (f + g) p μ ≤ C p * (snorm f p μ + snorm g p μ)`.

We choose the former formula so that the `Lᵖ` space is a normed group for all `p`.
-/

noncomputable section

open TopologicalSpace MeasureTheory Filter Function ENNReal
open scoped NNReal BigOperators Topology MeasureTheory

variable {α E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

namespace MeasureTheory

section Definitions

/-- `ℒp` seminorm, equal to `0` for `p=0`, to `(∫ ‖f a‖^p ∂μ) ^ (1/p)` for `0 < p < ∞` and to
`essSup ‖f‖ μ` for `p = ∞`. -/
def snorm (f : α → F) (p : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = 0 then μ f.support
  else if p = ∞ then essSup (‖f ·‖₊ : α → ℝ≥0∞) μ
  else if p < 1 then ∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p.toReal ∂μ
  else (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal)
#align measure_theory.snorm MeasureTheory.snorm

#noalign measure_theory.snorm_eq_snorm'

@[simp] lemma snorm_exponent_zero (f : α → F) : snorm f 0 μ = μ f.support := if_pos rfl
#align measure_theory.snorm_exponent_zero MeasureTheory.snorm_exponent_zeroₓ

lemma snorm_exponent_top (f : α → F) : snorm f ∞ μ = essSup (‖f ·‖₊ : α → ℝ≥0∞) μ := rfl
#align measure_theory.snorm_exponent_top MeasureTheory.snorm_exponent_top

lemma snorm_of_one_le_ne_top (f : α → F) (hp_one_le : 1 ≤ p) (hp_ne_top : p ≠ ∞) (μ : Measure α) :
    snorm f p μ = (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
  simp [snorm, hp_ne_top, hp_one_le.not_lt, (one_pos.trans_le hp_one_le).ne']
#align measure_theory.snorm_eq_lintegral_rpow_nnnorm MeasureTheory.snorm_of_one_le_ne_top

lemma snorm_of_ne_zero_le_one (f : α → F) (hp_ne_zero : p ≠ 0) (hp_le_one : p ≤ 1)
    (μ : Measure α) : snorm f p μ = ∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p.toReal ∂μ := by
  rcases hp_le_one.eq_or_lt with rfl | _ <;>
    simp [*, snorm, ne_top_of_le_ne_top coe_ne_top hp_le_one]

lemma snorm_coe_of_one_le {p : ℝ≥0} (f : α → F) (hp : 1 ≤ p) (μ : Measure α) :
    snorm f p μ = (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) :=
  snorm_of_one_le_ne_top _ (coe_le_coe.2 hp) coe_ne_top _

lemma snorm_coe_of_ne_zero_le_one {p : ℝ≥0} (f : α → F) (hp0 : p ≠ 0) (hp1 : p ≤ 1)
    (μ : Measure α) : snorm f p μ = ∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ (p : ℝ) ∂μ :=
  snorm_of_ne_zero_le_one _ (coe_ne_zero.2 hp0) (coe_le_coe.2 hp1) _

@[simp]
lemma snorm_exponent_one (f : α → F) : snorm f 1 μ = ∫⁻ x, ‖f x‖₊ ∂μ := by
  simp [snorm_of_one_le_ne_top]
#align measure_theory.snorm_one_eq_lintegral_nnnorm MeasureTheory.snorm_exponent_one

/-- The property that `f:α→E` is ae strongly measurable and `(∫ ‖f a‖^p ∂μ)^(1/p)` is finite
if `p < ∞`, or `essSup f < ∞` if `p = ∞`. -/
def Memℒp {α} {_ : MeasurableSpace α} (f : α → E) (p : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : Prop :=
  AEStronglyMeasurable f μ ∧ snorm f p μ < ∞
#align measure_theory.mem_ℒp MeasureTheory.Memℒp

theorem Memℒp.aestronglyMeasurable {f : α → E} {p : ℝ≥0∞} (h : Memℒp f p μ) :
    AEStronglyMeasurable f μ :=
  h.1
#align measure_theory.mem_ℒp.ae_strongly_measurable MeasureTheory.Memℒp.aestronglyMeasurable

theorem lintegral_rpow_nnnorm_eq_rpow_snorm {f : α → F} (hq1_lt : 1 ≤ q) :
    (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ q ∂μ) = snorm f (.ofReal q) μ ^ q := by
  rw [snorm_of_one_le_ne_top, toReal_ofReal, ← ENNReal.rpow_mul, one_div_mul_cancel,
    ENNReal.rpow_one] <;> try { linarith } <;> simp [*]
#align measure_theory.lintegral_rpow_nnnorm_eq_rpow_snorm' MeasureTheory.lintegral_rpow_nnnorm_eq_rpow_snorm

theorem lintegral_rpow_nnnorm_eq_snorm {f : α → F} (hq_pos : 0 < q) (hq_le_1 : q ≤ 1) :
    (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ q ∂μ) = snorm f (.ofReal q) μ := by
  rw [snorm_of_ne_zero_le_one, ENNReal.toReal_ofReal] <;> try { linarith } <;> simp [*]

theorem Memℒp.snorm_lt_top {f : α → E} (hfp : Memℒp f p μ) : snorm f p μ < ∞ := hfp.2
#align measure_theory.mem_ℒp.snorm_lt_top MeasureTheory.Memℒp.snorm_lt_top

theorem Memℒp.snorm_ne_top {f : α → E} (hfp : Memℒp f p μ) : snorm f p μ ≠ ∞ := hfp.2.ne
#align measure_theory.mem_ℒp.snorm_ne_top MeasureTheory.Memℒp.snorm_ne_top

theorem snorm_lt_top_iff_lintegral {f : α → F} (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : snorm f p μ < ∞ ↔ (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) < ∞ := by
  cases le_total p 1 with
  | inl hp1 => rw [snorm_of_ne_zero_le_one _ hp_ne_zero hp1]
  | inr hp1 =>
    rw [snorm_of_one_le_ne_top _ hp1 hp_ne_top, ENNReal.rpow_lt_top_iff_of_pos]
    exact div_pos one_pos <| toReal_pos hp_ne_zero hp_ne_top
#align measure_theory.snorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top MeasureTheory.snorm_lt_top_iff_lintegral

lemma snorm_ofReal_lt_top_iff_lintegral {f : α → F} (hq_pos : 0 < q) :
    snorm f (.ofReal q) μ < ∞ ↔ ∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ q ∂μ < ∞ := by
  rw [snorm_lt_top_iff_lintegral, toReal_ofReal hq_pos.le] <;> simp [*]

#noalign measure_theory.lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top
#noalign measure_theory.lintegral_rpow_nnnorm_lt_top_of_snorm_lt_top

end Definitions

section ExponentTop

theorem ae_le_snorm_top {f : α → F} : ∀ᵐ y ∂μ, ‖f y‖₊ ≤ snorm f ∞ μ := ae_le_essSup
#align measure_theory.ae_le_snorm_ess_sup MeasureTheory.ae_le_snorm_top

theorem meas_snorm_top_lt {f : α → F} : μ { y | snorm f ∞ μ < ‖f y‖₊ } = 0 := meas_essSup_lt
#align measure_theory.meas_snorm_ess_sup_lt MeasureTheory.meas_snorm_top_lt

lemma snorm_top_le_iff {f : α → E} {C : ℝ≥0∞} : snorm f ∞ μ ≤ C ↔ ∀ᵐ x ∂μ, (‖f x‖₊ : ℝ≥0∞) ≤ C := by
  rw [snorm_exponent_top]
  exact ⟨fun h ↦ (ENNReal.ae_le_essSup (‖f ·‖₊)).mono fun x hx ↦ hx.trans h, essSup_le_of_ae_le C⟩

@[mono]
theorem snorm_top_mono_measure (f : α → F) (hμν : ν ≪ μ) : snorm f ∞ ν ≤ snorm f ∞ μ := by
  simp_rw [snorm_exponent_top]
  exact essSup_mono_measure hμν
#align measure_theory.snorm_ess_sup_mono_measure MeasureTheory.snorm_top_mono_measure
#noalign measure_theory.snorm'_mono_measure

@[simp]
theorem snorm_top_eq_zero_iff {f : α → F} : snorm f ∞ μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp [EventuallyEq, snorm]
#align measure_theory.snorm_ess_sup_eq_zero_iff MeasureTheory.snorm_top_eq_zero_iff

theorem snorm_top_le_coe {f : α → F} {C : ℝ≥0} : snorm f ∞ μ ≤ C ↔ ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C :=
  snorm_top_le_iff.trans <| by simp only [coe_le_coe]
#align measure_theory.snorm_ess_sup_le_of_ae_nnnorm_bound MeasureTheory.snorm_top_le_coe

theorem coe_nnnorm_ae_le_snorm_top (f : α → F) (μ : Measure α) :
    ∀ᵐ x ∂μ, (‖f x‖₊ : ℝ≥0∞) ≤ snorm f ∞ μ :=
  snorm_top_le_iff.1 le_rfl
#align measure_theory.coe_nnnorm_ae_le_snorm_ess_sup MeasureTheory.coe_nnnorm_ae_le_snorm_top

theorem snorm_top_le_ofReal_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    snorm f ∞ μ ≤ ENNReal.ofReal C :=
  snorm_top_le_coe.2 <| hfC.mono fun _x hx => hx.trans C.le_coe_toNNReal
#align measure_theory.snorm_ess_sup_le_of_ae_bound MeasureTheory.snorm_top_le_ofReal_of_ae_bound

theorem snorm_top_lt_top_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    snorm f ∞ μ < ∞ :=
  (snorm_top_le_coe.2 hfC).trans_lt coe_lt_top
#align measure_theory.snorm_ess_sup_lt_top_of_ae_nnnorm_bound MeasureTheory.snorm_top_lt_top_of_ae_nnnorm_bound

theorem snorm_top_lt_top_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    snorm f ∞ μ < ∞ :=
  (snorm_top_le_ofReal_of_ae_bound hfC).trans_lt ENNReal.ofReal_lt_top
#align measure_theory.snorm_ess_sup_lt_top_of_ae_bound MeasureTheory.snorm_top_lt_top_of_ae_bound

theorem memℒp_top_of_bound {f : α → E} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : Memℒp f ∞ μ :=
  ⟨hf, snorm_top_lt_top_of_ae_bound hfC⟩
#align measure_theory.mem_ℒp_top_of_bound MeasureTheory.memℒp_top_of_bound

lemma snorm_top_piecewise {s : Set α} (f g : α → E) [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) :
    snorm (Set.piecewise s f g) ∞ μ =
      max (snorm f ∞ (μ.restrict s)) (snorm g ∞ (μ.restrict sᶜ)) := by
  simp only [snorm_exponent_top, ← essSup_piecewise hs]
  congr with x
  by_cases hx : x ∈ s <;> simp [hx]

end ExponentTop

section Mono

#noalign measure_theory.snorm'_mono_nnnorm_ae
#noalign measure_theory.snorm'_mono_ae
#noalign measure_theory.snorm'_congr_nnnorm_ae
#noalign measure_theory.snorm'_congr_norm_ae
#noalign measure_theory.snorm'_congr_ae
#noalign measure_theory.snorm_ess_sup_congr_ae
#noalign measure_theory.snorm_ess_sup_mono_nnnorm_ae

theorem snorm_mono_nnnorm_ae {f : α → F} {g : α → G} (h : (‖f ·‖₊) ≤ᵐ[μ] (‖g ·‖₊)) :
    snorm f p μ ≤ snorm g p μ := by
  have : ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ ≤ ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ :=
    lintegral_mono_ae <| h.mono fun x hx ↦ ENNReal.rpow_le_rpow (coe_le_coe.2 hx) toReal_nonneg
  simp only [snorm]
  split_ifs
  · refine measure_mono_ae (h.mono fun x hx ↦ mt fun hg ↦ ?_)
    simpa [hg] using hx
  · exact essSup_mono_ae (h.mono fun x hx => ENNReal.coe_le_coe.mpr hx)
  · exact this
  · exact ENNReal.rpow_le_rpow this (by positivity)
#align measure_theory.snorm_mono_nnnorm_ae MeasureTheory.snorm_mono_nnnorm_ae

theorem snorm_mono_ae {f : α → F} {g : α → G} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    snorm f p μ ≤ snorm g p μ :=
  snorm_mono_nnnorm_ae h
#align measure_theory.snorm_mono_ae MeasureTheory.snorm_mono_ae

theorem snorm_mono_ae_real {f : α → F} {g : α → ℝ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) :
    snorm f p μ ≤ snorm g p μ :=
  snorm_mono_ae <| h.mono fun _x hx => hx.trans (le_abs_self _)
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

theorem Memℒp.of_le {f : α → E} {g : α → F} (hg : Memℒp g p μ) (hf : AEStronglyMeasurable f μ)
    (hfg : (‖f ·‖) ≤ᵐ[μ] (‖g ·‖)) : Memℒp f p μ :=
  ⟨hf, (snorm_mono_ae hfg).trans_lt hg.snorm_lt_top⟩
#align measure_theory.mem_ℒp.of_le MeasureTheory.Memℒp.of_le

alias Memℒp.mono := Memℒp.of_le
#align measure_theory.mem_ℒp.mono MeasureTheory.Memℒp.mono

theorem Memℒp.mono_real {f : α → E} {g : α → ℝ} (hg : Memℒp g p μ) (hf : AEStronglyMeasurable f μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : Memℒp f p μ :=
  hg.mono hf <| h.mono fun _x hx => le_trans hx (le_abs_self _)
#align measure_theory.mem_ℒp.mono' MeasureTheory.Memℒp.mono_real

@[mono]
theorem snorm_mono_measure (f : α → F) (hμν : ν ≤ μ) : snorm f p ν ≤ snorm f p μ := by
  rcases eq_or_ne p ∞ with rfl | hp_ne_top
  · exact snorm_top_le_iff.2 <| ae_mono hμν ae_le_snorm_top
  rcases eq_or_ne p 0 with rfl | hp0
  · simpa only [snorm_exponent_zero] using Measure.le_iff'.1 hμν _
  have : ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂ν ≤ ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ :=
    lintegral_mono' hμν le_rfl
  cases' le_total p 1 with hp1 hp1
  · simpa only [snorm_of_ne_zero_le_one _ hp0 hp1]
  · simp only [snorm_of_one_le_ne_top _ hp1 hp_ne_top]; gcongr
#align measure_theory.snorm_mono_measure MeasureTheory.snorm_mono_measure

theorem Memℒp.mono_measure {f : α → E} (hμν : ν ≤ μ) (hf : Memℒp f p μ) : Memℒp f p ν :=
  ⟨hf.1.mono_measure hμν, (snorm_mono_measure f hμν).trans_lt hf.2⟩
#align measure_theory.mem_ℒp.mono_measure MeasureTheory.Memℒp.mono_measure

lemma snorm_restrict_le (f : α → F) (p : ℝ≥0∞) (μ : Measure α) (s : Set α) :
    snorm f p (μ.restrict s) ≤ snorm f p μ :=
  snorm_mono_measure f Measure.restrict_le_self

theorem Memℒp.restrict (s : Set α) {f : α → E} (hf : Memℒp f p μ) : Memℒp f p (μ.restrict s) :=
  hf.mono_measure Measure.restrict_le_self
#align measure_theory.mem_ℒp.restrict MeasureTheory.Memℒp.restrict

end Mono

section Congr

theorem snorm_congr_nnnorm_ae {f : α → F} {g : α → G} (hfg : (‖f ·‖₊) =ᵐ[μ] (‖g ·‖₊)) :
    snorm f p μ = snorm g p μ :=
  (snorm_mono_nnnorm_ae hfg.le).antisymm (snorm_mono_nnnorm_ae hfg.symm.le)
#align measure_theory.snorm_congr_nnnorm_ae MeasureTheory.snorm_congr_nnnorm_ae

theorem snorm_congr_norm_ae {f : α → F} {g : α → G} (hfg : (‖f ·‖) =ᵐ[μ] (‖g ·‖)) :
    snorm f p μ = snorm g p μ :=
  snorm_congr_nnnorm_ae <| hfg.mono fun _x hx => NNReal.eq hx
#align measure_theory.snorm_congr_norm_ae MeasureTheory.snorm_congr_norm_ae

@[simp]
theorem snorm_norm (f : α → F) : snorm (fun x => ‖f x‖) p μ = snorm f p μ :=
  snorm_congr_norm_ae <| eventually_of_forall fun _ => norm_norm _
#align measure_theory.snorm_norm MeasureTheory.snorm_norm
#noalign measure_theory.snorm'_norm

theorem snorm_congr_ae {f g : α → F} (hfg : f =ᵐ[μ] g) : snorm f p μ = snorm g p μ :=
  snorm_congr_norm_ae <| hfg.fun_comp _
#align measure_theory.snorm_congr_ae MeasureTheory.snorm_congr_ae

theorem memℒp_congr_ae {f g : α → E} (hfg : f =ᵐ[μ] g) : Memℒp f p μ ↔ Memℒp g p μ := by
  simp only [Memℒp, snorm_congr_ae hfg, aestronglyMeasurable_congr hfg]
#align measure_theory.mem_ℒp_congr_ae MeasureTheory.memℒp_congr_ae

theorem Memℒp.ae_eq {f g : α → E} (hf_Lp : Memℒp f p μ) (hfg : f =ᵐ[μ] g) : Memℒp g p μ :=
  (memℒp_congr_ae hfg).1 hf_Lp
#align measure_theory.mem_ℒp.ae_eq MeasureTheory.Memℒp.ae_eq

theorem Memℒp.congr_norm {f : α → E} {g : α → F} (hf : Memℒp f p μ) (hg : AEStronglyMeasurable g μ)
    (h : (‖f ·‖) =ᵐ[μ] (‖g ·‖)) : Memℒp g p μ :=
  hf.mono hg <| EventuallyEq.le <| EventuallyEq.symm h
#align measure_theory.mem_ℒp.congr_norm MeasureTheory.Memℒp.congr_norm

theorem memℒp_congr_norm {f : α → E} {g : α → F} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (h : (‖f ·‖) =ᵐ[μ] (‖g ·‖)) : Memℒp f p μ ↔ Memℒp g p μ :=
  ⟨fun h2f => h2f.congr_norm hg h, fun h2g => h2g.congr_norm hf <| EventuallyEq.symm h⟩
#align measure_theory.mem_ℒp_congr_norm MeasureTheory.memℒp_congr_norm

theorem snorm_indicator_sub_indicator (s t : Set α) (f : α → E) :
    snorm (s.indicator f - t.indicator f) p μ = snorm ((s ∆ t).indicator f) p μ :=
  snorm_congr_norm_ae <| ae_of_all _ fun x ↦ by
    simp only [Pi.sub_apply, Set.apply_indicator_symmDiff norm_neg]

theorem Memℒp.norm {f : α → E} (h : Memℒp f p μ) : Memℒp (fun x => ‖f x‖) p μ :=
  h.of_le h.aestronglyMeasurable.norm (eventually_of_forall fun x => by simp)
#align measure_theory.mem_ℒp.norm MeasureTheory.Memℒp.norm

theorem memℒp_norm_iff {f : α → E} (hf : AEStronglyMeasurable f μ) :
    Memℒp (fun x => ‖f x‖) p μ ↔ Memℒp f p μ :=
  ⟨fun h => ⟨hf, by rw [← snorm_norm]; exact h.2⟩, fun h => h.norm⟩
#align measure_theory.mem_ℒp_norm_iff MeasureTheory.memℒp_norm_iff

end Congr

section Zero

theorem memℒp_zero_iff_aestronglyMeasurable {f : α → E} :
    Memℒp f 0 μ ↔ AEStronglyMeasurable f μ ∧ μ f.support < ∞ :=
  by rw [Memℒp, snorm_exponent_zero]
#align measure_theory.mem_ℒp_zero_iff_ae_strongly_measurable MeasureTheory.memℒp_zero_iff_aestronglyMeasurable

#noalign measure_theory.snorm'_zero
#noalign measure_theory.snorm'_zero'
#noalign measure_theory.snorm_ess_sup_zero

@[simp]
theorem snorm_zero' : snorm (fun _ : α => (0 : F)) p μ = 0 := by
  rcases eq_or_ne p 0 with rfl | hp0; · simp
  rcases eq_or_ne p ∞ with rfl | hp_top; · simp [snorm_exponent_top, Pi.zero_def, EventuallyEq.rfl]
  by_cases hlt : p < 1 <;> simp [snorm, toReal_pos, *]
#align measure_theory.snorm_zero' MeasureTheory.snorm_zero'

@[simp]
theorem snorm_zero : snorm (0 : α → F) p μ = 0 := snorm_zero'
#align measure_theory.snorm_zero MeasureTheory.snorm_zero

@[simp]
theorem snorm_measure_zero {f : α → F} : snorm f p (0 : Measure α) = 0 := by
  simp (config := {contextual := true}) [snorm, ENNReal.toReal_pos]
#align measure_theory.snorm_measure_zero MeasureTheory.snorm_measure_zero

theorem zero_memℒp : Memℒp (0 : α → E) p μ :=
  ⟨aestronglyMeasurable_zero, by rw [snorm_zero]; exact ENNReal.coe_lt_top⟩
#align measure_theory.zero_mem_ℒp MeasureTheory.zero_memℒp

theorem zero_mem_ℒp' : Memℒp (fun _ : α => (0 : E)) p μ := zero_memℒp (E := E)
#align measure_theory.zero_mem_ℒp' MeasureTheory.zero_mem_ℒp'

theorem snorm_eq_zero_iff {f : α → E} (hf : AEStronglyMeasurable f μ) :
    snorm f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  unfold snorm; split_ifs
  · rfl
  · simp [EventuallyEq]
  · simp [hf.ennnorm.pow_const p.toReal, EventuallyEq, ENNReal.toReal_pos, *]
  · simp [hf.ennnorm.pow_const p.toReal, EventuallyEq, ENNReal.toReal_pos,
      ENNReal.toReal_nonneg.not_lt, *]
#align measure_theory.snorm_eq_zero_iff MeasureTheory.snorm_eq_zero_iff

#noalign measure_theory.snorm'_measure_zero_of_pos
#noalign measure_theory.snorm'_measure_zero_of_exponent_zero
#noalign measure_theory.snorm'_measure_zero_of_neg
#noalign measure_theory.snorm_ess_sup_measure_zero

end Zero

section Neg

#noalign measure_theory.snorm'_neg

@[simp]
theorem snorm_neg {f : α → F} : snorm (-f) p μ = snorm f p μ := by simp [snorm]
#align measure_theory.snorm_neg MeasureTheory.snorm_neg

theorem Memℒp.neg {f : α → E} (hf : Memℒp f p μ) : Memℒp (-f) p μ :=
  ⟨AEStronglyMeasurable.neg hf.1, by simp [hf.right]⟩
#align measure_theory.mem_ℒp.neg MeasureTheory.Memℒp.neg

theorem memℒp_neg_iff {f : α → E} : Memℒp (-f) p μ ↔ Memℒp f p μ :=
  ⟨fun h => neg_neg f ▸ h.neg, Memℒp.neg⟩  
#align measure_theory.mem_ℒp_neg_iff MeasureTheory.memℒp_neg_iff

end Neg

section Const

@[simp]
lemma snorm_const_top [NeZero μ] (c : F) : snorm (fun _ ↦ c) ∞ μ = ‖c‖₊ := by
  simp [snorm_exponent_top]

lemma snorm_const_coe_of_one_le {p : ℝ≥0} (c : F) (hp : 1 ≤ p) :
    snorm (fun _ ↦ c) p μ = (‖c‖₊ : ℝ≥0∞) * μ Set.univ ^ (1 / (p : ℝ)) := by
  rw [snorm_coe_of_one_le _ hp, lintegral_const, mul_rpow_of_nonneg _ _ (by positivity),
    ← ENNReal.rpow_mul, mul_one_div, div_self, ENNReal.rpow_one]
  exact NNReal.coe_ne_zero.2 (one_pos.trans_le hp).ne'

lemma snorm_const_ofReal_of_one_le (c : F) (one_le_q : 1 ≤ q) :
    snorm (fun _ ↦ c) (.ofReal q) μ = (‖c‖₊ : ℝ≥0∞) * μ Set.univ ^ (1 / q) := by
  lift q to ℝ≥0 using zero_le_one.trans one_le_q
  rw [ENNReal.ofReal_coe_nnreal, snorm_const_coe_of_one_le c one_le_q]

lemma snorm_const_of_one_le_ne_top (c : F) (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) :
    snorm (fun _ ↦ c) p μ = (‖c‖₊ : ℝ≥0∞) * μ Set.univ ^ (1 / p.toReal) := by
  lift p to ℝ≥0 using hp_ne_top
  exact snorm_const_coe_of_one_le c (coe_le_coe.1 hp)
#align measure_theory.snorm_const' MeasureTheory.snorm_const_of_one_le_ne_top

lemma snorm_const_of_one_le [NeZero μ] (c : F) (hp : 1 ≤ p) :
    snorm (fun _ ↦ c) p μ = (‖c‖₊ : ℝ≥0∞) * μ Set.univ ^ (1 / p.toReal) := by
  rcases eq_or_ne p ∞ with rfl | hp'
  · simp
  · exact snorm_const_of_one_le_ne_top c hp hp'
#align measure_theory.snorm_const MeasureTheory.snorm_const_of_one_le

lemma snorm_const_eq_ennorm [IsProbabilityMeasure μ] (c : F) (hp : 1 ≤ p) :
    snorm (fun _ ↦ c) p μ = ‖c‖₊ := by
  simp [snorm_const_of_one_le c hp]

lemma snorm_const_coe_of_ne_zero_le_one {p : ℝ≥0} {c : F} (h0 : c ≠ 0 ∨ p ≠ 0) (hp1 : p ≤ 1) :
    snorm (fun _ ↦ c) p μ = (‖c‖₊ : ℝ≥0∞) ^ (p : ℝ) * μ Set.univ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · have hc0 : c ≠ 0 := h0.resolve_right fun h ↦ h rfl
    simp [hc0, Function.support_const]
  · rw [snorm_coe_of_ne_zero_le_one _ hp0 hp1, lintegral_const]

lemma snorm_const_ofReal_of_pos_le_one (c : F) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    snorm (fun _ ↦ c) (.ofReal q) μ = (‖c‖₊ : ℝ≥0∞) ^ q * μ Set.univ := by
  lift q to ℝ≥0 using hq0.le
  rw [NNReal.coe_pos] at hq0
  rw [ENNReal.ofReal_coe_nnreal, snorm_const_coe_of_ne_zero_le_one (.inr hq0.ne') hq1]

lemma snorm_const_of_ne_zero_le_one {c : F} (h0 : c ≠ 0 ∨ p ≠ 0) (hp1 : p ≤ 1) :
    snorm (fun _ ↦ c) p μ = (‖c‖₊ : ℝ≥0∞) ^ p.toReal * μ Set.univ := by
  lift p to ℝ≥0 using ne_top_of_le_ne_top one_ne_top hp1
  apply snorm_const_coe_of_ne_zero_le_one <;> assumption_mod_cast

#noalign measure_theory.snorm'_const
#noalign measure_theory.snorm'_const'
#noalign measure_theory.snorm_ess_sup_const
#noalign measure_theory.snorm'_const_of_is_probability_measure

theorem snorm_const_lt_top_iff {p : ℝ≥0∞} {c : F} :
    snorm (fun _ : α => c) p μ < ∞ ↔ c = 0 ∨ p = ∞ ∨ μ Set.univ < ∞ := by
  rcases eq_zero_or_neZero μ with rfl | hμ; · simp
  rcases eq_or_ne c 0 with rfl | hc; · simp
  rcases eq_or_ne p ∞ with rfl | hp; · simp
  simp only [*, false_or]
  lift p to ℝ≥0 using hp
  cases' le_total p 1 with hp1 hp1
  · simp [snorm_const_coe_of_ne_zero_le_one (.inl hc) hp1, lt_top_iff_ne_top, mul_eq_top, *]
  · have : p ≠ 0 := (one_pos.trans_le hp1).ne'
    simp [snorm_const_coe_of_one_le c hp1, lt_top_iff_ne_top, mul_eq_top, NeZero.ne, *]
#align measure_theory.snorm_const_lt_top_iff MeasureTheory.snorm_const_lt_top_iff

theorem memℒp_const_iff {p : ℝ≥0∞} {c : E} :
    Memℒp (fun _ : α => c) p μ ↔ c = 0 ∨ p = ∞ ∨ μ Set.univ < ∞ := by
  simp only [Memℒp, aestronglyMeasurable_const, true_and, snorm_const_lt_top_iff]
#align measure_theory.mem_ℒp_const_iff MeasureTheory.memℒp_const_iff

theorem memℒp_const (c : E) [IsFiniteMeasure μ] : Memℒp (fun _ : α => c) p μ :=
  memℒp_const_iff.2 <| .inr <| .inr <| measure_lt_top _ _
#align measure_theory.mem_ℒp_const MeasureTheory.memℒp_const

theorem memℒp_top_const (c : E) : Memℒp (fun _ : α => c) ∞ μ :=
  memℒp_const_iff.2 <| .inr <| .inl rfl
#align measure_theory.mem_ℒp_top_const MeasureTheory.memℒp_top_const

theorem Memℒp.of_bound [IsFiniteMeasure μ] {f : α → E} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : Memℒp f p μ :=
  (memℒp_const C).of_le hf (hfC.mono fun _x hx => le_trans hx (le_abs_self _))
#align measure_theory.mem_ℒp.of_bound MeasureTheory.Memℒp.of_bound

-- theorem snorm_le_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
--     snorm f p μ ≤ C • μ Set.univ ^ p.toReal⁻¹ := by
--   rcases eq_zero_or_neZero μ with rfl | hμ
--   · simp
--   by_cases hp : p = 0
--   · simp [hp]
--   have : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖(C : ℝ)‖₊ := hfC.mono fun x hx => hx.trans_eq C.nnnorm_eq.symm
--   refine' (snorm_mono_ae this).trans_eq _
--   rw [snorm_const _ hp (NeZero.ne μ), C.nnnorm_eq, one_div, ENNReal.smul_def, smul_eq_mul]
-- #align measure_theory.snorm_le_of_ae_nnnorm_bound MeasureTheory.snorm_le_of_ae_nnnorm_bound

-- theorem snorm_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
--     snorm f p μ ≤ μ Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal C := by
--   rw [← mul_comm]
--   exact snorm_le_of_ae_nnnorm_bound (hfC.mono fun x hx => hx.trans C.le_coe_toNNReal)
-- #align measure_theory.snorm_le_of_ae_bound MeasureTheory.snorm_le_of_ae_bound

end Const

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜}

protected lemma Memℒp.re (hf : Memℒp f p μ) : Memℒp (fun x => RCLike.re (f x)) p μ :=
  hf.of_le (RCLike.continuous_re.comp_aestronglyMeasurable hf.1) <| ae_of_all _ fun _ ↦
    RCLike.norm_re_le_norm _
#align measure_theory.mem_ℒp.re MeasureTheory.Memℒp.re

protected lemma Memℒp.im (hf : Memℒp f p μ) : Memℒp (fun x => RCLike.im (f x)) p μ :=
  hf.of_le (RCLike.continuous_im.comp_aestronglyMeasurable hf.1) <| ae_of_all _ fun _ ↦
    RCLike.norm_im_le_norm _
#align measure_theory.mem_ℒp.im MeasureTheory.Memℒp.im

end RCLike
