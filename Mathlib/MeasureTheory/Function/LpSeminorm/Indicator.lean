/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.Normed.Group.Indicator
public import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# ℒp seminorms and indicator functions
-/

public section
noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal Topology ComplexConjugate

variable {α ε ε' E F : Type*} {m0 : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [ENorm ε] [ENorm ε']

namespace MeasureTheory

section Lp

variable {f : α → F}

section Indicator

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {c : ε} {hf : AEStronglyMeasurable f μ} {s : Set α}
  {ε' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε']

lemma eLpNorm_indicator_eq_eLpNorm_restrict {f : α → ε} {s : Set α} (hs : MeasurableSet s) :
    eLpNorm (s.indicator f) p μ = eLpNorm f p (μ.restrict s) := by
  have A : AEStronglyMeasurable (s.indicator f) μ ↔ AEStronglyMeasurable f (μ.restrict s) :=
    aestronglyMeasurable_indicator_iff hs
  by_cases hfi : AEStronglyMeasurable (s.indicator f) μ; swap
  · have hfr : ¬ AEStronglyMeasurable f (μ.restrict s) := by
      simp [← A, hfi]
    simp [eLpNorm_of_not_aestronglyMeasurable, hfi, hfr]
  have hfr : AEStronglyMeasurable f (μ.restrict s) := A.1 hfi
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero hfi, eLpNorm_exponent_zero hfr]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, eLpNorm_exponent_top hfi, eLpNorm_exponent_top hfr,
      eLpNormEssSup_eq_essSup_enorm,
       enorm_indicator_eq_indicator_enorm, ENNReal.essSup_indicator_eq_essSup_restrict hs]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp_top hfi,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp_zero hp_top hfr]
  rw [← lintegral_indicator hs]
  congr
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [eq_comm, ← Function.comp_def (fun x : ℝ≥0∞ => x ^ p.toReal), Set.indicator_comp_of_zero,
    Function.comp_def]
  simp [ENNReal.toReal_pos hp_zero hp_top]

lemma eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict (hs : MeasurableSet s) :
    eLpNormEssSup (s.indicator f) μ = eLpNormEssSup f (μ.restrict s) := by
  simpa [eLpNormEssSup_eq_essSup_enorm, enorm_indicator_eq_indicator_enorm] using
    ENNReal.essSup_indicator_eq_essSup_restrict (f := fun x ↦ ‖f x‖ₑ) hs

lemma eLpNorm_restrict_le (f : α → ε') (p : ℝ≥0∞) (μ : Measure α) (s : Set α) :
    eLpNorm f p (μ.restrict s) ≤ eLpNorm f p μ :=
  eLpNorm_mono_measure f Measure.restrict_le_self

lemma eLpNorm_indicator_le (f : α → ε) (hs : MeasurableSet s) :
    eLpNorm (s.indicator f) p μ ≤ eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · apply eLpNorm_mono_enorm (hf.indicator hs)
    simp_rw [enorm_indicator_eq_indicator_enorm]
    exact s.indicator_le_self _
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]
    exact le_top

lemma eLpNormEssSup_indicator_le (s : Set α) (f : α → ε) :
    eLpNormEssSup (s.indicator f) μ ≤ eLpNormEssSup f μ := by
  refine essSup_mono_ae (.of_forall fun x => ?_)
  simp_rw [enorm_indicator_eq_indicator_enorm]
  exact Set.indicator_le_self s _ x

lemma eLpNormEssSup_indicator_const_le (s : Set α) (c : ε) :
    eLpNormEssSup (s.indicator fun _ : α => c) μ ≤ ‖c‖ₑ := by
  obtain rfl | hμ0 := eq_or_ne μ 0
  · simp
  · exact (eLpNormEssSup_indicator_le s fun _ => c).trans (eLpNormEssSup_const c hμ0).le

lemma eLpNormEssSup_indicator_const_eq (s : Set α) (c : ε) (hμs : μ s ≠ 0) :
    eLpNormEssSup (s.indicator fun _ : α => c) μ = ‖c‖ₑ := by
  refine le_antisymm (eLpNormEssSup_indicator_const_le s c) ?_
  by_contra! h
  have h' := ae_iff.mp (ae_lt_of_essSup_lt h)
  push Not at h'
  refine hμs (measure_mono_null (fun x hx_mem => ?_) h')
  rw [Set.mem_ofPred_eq, Set.indicator_of_mem hx_mem]

lemma eLpNorm_indicator_const₀ (hs : NullMeasurableSet s μ) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal) :=
  have hsc : AEStronglyMeasurable (s.indicator fun _ : α ↦ c) μ :=
    AEStronglyMeasurable.indicator₀ (by fun_prop) hs
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp hp_top
  calc
    eLpNorm (s.indicator fun _ => c) p μ
      = (∫⁻ x, (‖(s.indicator fun _ ↦ c) x‖ₑ ^ p.toReal) ∂μ) ^ (1 / p.toReal) :=
          eLpNorm_eq_lintegral_rpow_enorm_toReal hp hp_top hsc
    _ = (∫⁻ x, (s.indicator fun _ ↦ ‖c‖ₑ ^ p.toReal) x ∂μ) ^ (1 / p.toReal) := by
      congr 2
      refine (Set.comp_indicator_const c (fun x ↦ (‖x‖ₑ) ^ p.toReal) ?_)
      simp [hp_pos]
    _ = ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
      rw [lintegral_indicator_const₀ hs, ENNReal.mul_rpow_of_nonneg, ← ENNReal.rpow_mul,
        mul_one_div_cancel hp_pos.ne', ENNReal.rpow_one]
      positivity

lemma eLpNorm_indicator_const (hs : NullMeasurableSet s μ) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal) :=
  eLpNorm_indicator_const₀ hs hp hp_top

lemma eLpNorm_indicator_const' (hs : MeasurableSet s) (hμs : μ s ≠ 0) (hp : p ≠ 0) :
    eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
  have hsc : AEStronglyMeasurable (s.indicator fun _ : α ↦ c) μ :=
    AEStronglyMeasurable.indicator₀ (by fun_prop) hs.nullMeasurableSet
  by_cases hp_top : p = ∞
  · simp [hp_top, hsc, eLpNormEssSup_indicator_const_eq s c hμs]
  · exact eLpNorm_indicator_const hs.nullMeasurableSet hp hp_top

variable (c) in
lemma eLpNorm_indicator_const_le (p : ℝ≥0∞) (hs : NullMeasurableSet s μ) :
    eLpNorm (s.indicator fun _ => c) p μ ≤ ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
  have hsc : AEStronglyMeasurable (s.indicator fun _ : α ↦ c) μ :=
    AEStronglyMeasurable.indicator₀ (by fun_prop) hs
  have hc : AEStronglyMeasurable (fun _ : α ↦ c) μ := by fun_prop
  obtain rfl | hp := eq_or_ne p 0
  · simp [hsc]
  obtain rfl | h'p := eq_or_ne p ∞
  · simp only [eLpNorm_exponent_top hsc, ENNReal.toReal_top, _root_.div_zero, ENNReal.rpow_zero,
      mul_one]
    exact eLpNormEssSup_indicator_const_le _ _
  let t := toMeasurable μ s
  calc
    eLpNorm (s.indicator fun _ => c) p μ ≤ eLpNorm (t.indicator fun _ ↦ c) p μ :=
      eLpNorm_mono_enorm hsc (enorm_indicator_le_of_subset (subset_toMeasurable _ _) _)
    _ = ‖c‖ₑ * μ t ^ (1 / p.toReal) :=
      eLpNorm_indicator_const (measurableSet_toMeasurable ..).nullMeasurableSet hp h'p
    _ = ‖c‖ₑ * μ s ^ (1 / p.toReal) := by rw [measure_toMeasurable]

lemma MemLp.indicator {f : α → ε} (hs : MeasurableSet s) (hf : MemLp f p μ) :
    MemLp (s.indicator f) p μ :=
  lt_of_le_of_lt (eLpNorm_indicator_le f hs) hf

lemma memLp_indicator_iff_restrict {f : α → ε} (hs : MeasurableSet s) :
    MemLp (s.indicator f) p μ ↔ MemLp f p (μ.restrict s) := by
  simp_rw [memLp_iff, eLpNorm_indicator_eq_eLpNorm_restrict hs]

lemma memLp_indicator_const (p : ℝ≥0∞) (hs : MeasurableSet s) (c : E) (hμsc : c = 0 ∨ μ s ≠ ∞) :
    MemLp (s.indicator fun _ => c) p μ := by
  rw [memLp_indicator_iff_restrict hs]
  obtain rfl | hμ := hμsc
  · exact MemLp.zero
  · have := Fact.mk hμ.lt_top
    apply memLp_const

lemma eLpNormEssSup_piecewise (f g : α → ε) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    eLpNormEssSup (Set.piecewise s f g) μ
      = max (eLpNormEssSup f (μ.restrict s)) (eLpNormEssSup g (μ.restrict sᶜ)) := by
  simp only [eLpNormEssSup, ← ENNReal.essSup_piecewise hs]
  congr with x
  by_cases hx : x ∈ s <;> simp [hx]

lemma eLpNorm_top_piecewise (f g : α → ε) [DecidablePred (· ∈ s)] (hs : MeasurableSet s)
    (hf : AEStronglyMeasurable f (μ.restrict s)) (hg : AEStronglyMeasurable g (μ.restrict sᶜ)) :
    eLpNorm (Set.piecewise s f g) ∞ μ
      = max (eLpNorm f ∞ (μ.restrict s)) (eLpNorm g ∞ (μ.restrict sᶜ)) := by
  rw [eLpNorm_exponent_top (AEStronglyMeasurable.piecewise hs hf hg), eLpNorm_exponent_top hf,
    eLpNorm_exponent_top hg]
  exact eLpNormEssSup_piecewise f g hs

protected lemma MemLp.piecewise {f : α → ε} [DecidablePred (· ∈ s)] {g} (hs : MeasurableSet s)
    (hf : MemLp f p (μ.restrict s)) (hg : MemLp g p (μ.restrict sᶜ)) :
    MemLp (s.piecewise f g) p μ := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, memLp_zero_iff_aestronglyMeasurable]
    exact AEStronglyMeasurable.piecewise hs hf.aestronglyMeasurable hg.aestronglyMeasurable
  unfold MemLp
  obtain rfl | hp_top := eq_or_ne p ∞
  · rw [eLpNorm_top_piecewise f g hs hf.aestronglyMeasurable hg.aestronglyMeasurable]
    exact max_lt hf hg
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_zero hp_top
    (AEStronglyMeasurable.piecewise hs hf.aestronglyMeasurable hg.aestronglyMeasurable),
    ← lintegral_add_compl _ hs,
    ENNReal.add_lt_top]
  constructor
  · have h (x) (hx : x ∈ s) : ‖Set.piecewise s f g x‖ₑ ^ p.toReal = ‖f x‖ₑ ^ p.toReal := by
      simp [hx]
    rw [setLIntegral_congr_fun hs h]
    exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_zero hp_top hf
  · have h (x) (hx : x ∈ sᶜ) : ‖Set.piecewise s f g x‖ₑ ^ p.toReal = ‖g x‖ₑ ^ p.toReal := by
      have hx' : x ∉ s := hx
      simp [hx']
    rw [setLIntegral_congr_fun hs.compl h]
    exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_zero hp_top hg

theorem eLpNorm_indicator_sub_le_of_dist_bdd {β : Type*} [NormedAddCommGroup β]
    (μ : Measure α := by volume_tac) (hp' : p ≠ ∞) (hs : NullMeasurableSet s μ) {f g : α → β}
    {c : ℝ} (hc : 0 ≤ c) (hfgm : AEStronglyMeasurable (s.indicator (f - g)) μ)
    (hf : ∀ x ∈ s, dist (f x) (g x) ≤ c) :
    eLpNorm (s.indicator (f - g)) p μ ≤ ENNReal.ofReal c * μ s ^ (1 / p.toReal) := by
  have hcm : AEStronglyMeasurable (s.indicator fun _ : α ↦ c) μ :=
    AEStronglyMeasurable.indicator₀ (by fun_prop) hs
  by_cases hp : p = 0
  · simp [hp, hfgm]
  have : ∀ x, ‖s.indicator (f - g) x‖ ≤ ‖s.indicator (fun _ => c) x‖ := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Pi.sub_apply, ← dist_eq_norm,
        Real.norm_eq_abs, abs_of_nonneg hc]
      exact hf x hx
    · simp [Set.indicator_of_notMem hx]
  grw [eLpNorm_mono hfgm this, eLpNorm_indicator_const hs hp hp', ← ofReal_norm,
    Real.norm_eq_abs, abs_of_nonneg hc]

theorem eLpNorm_sub_le_of_dist_bdd {β : Type*} [NormedAddCommGroup β]
    (μ : Measure α := by volume_tac) (hp : p ≠ ⊤) (hs : NullMeasurableSet s μ) {c : ℝ} (hc : 0 ≤ c)
    {f g : α → β} (hfgm : AEStronglyMeasurable (f - g) μ)
    (h : ∀ x, dist (f x) (g x) ≤ c) (hs₁ : f.support ⊆ s) (hs₂ : g.support ⊆ s) :
    eLpNorm (f - g) p μ ≤ ENNReal.ofReal c * μ s ^ (1 / p.toReal) := by
  have hcm : AEStronglyMeasurable (s.indicator fun _ : α ↦ c) μ :=
    AEStronglyMeasurable.indicator₀ (by fun_prop) hs
  have hs₃ : s.indicator (f - g) = f - g := by
    rw [Set.indicator_eq_self]
    exact (Function.support_sub _ _).trans (Set.union_subset hs₁ hs₂)
  rw [← hs₃]
  exact eLpNorm_indicator_sub_le_of_dist_bdd μ hp hs hc (hfgm.indicator₀ hs) (fun x _ ↦ h x)

end Indicator

section UnifTight

/-- A single function that is `MemLp f p μ` is tight with respect to `μ`. -/
theorem MemLp.exists_eLpNorm_indicator_compl_lt {β : Type*} [NormedAddCommGroup β] (hp_top : p ≠ ∞)
    {f : α → β} (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : Set α, MeasurableSet s ∧ μ s < ∞ ∧ eLpNorm (sᶜ.indicator f) p μ < ε := by
  rcases eq_or_ne p 0 with rfl | hp₀
  · refine ⟨∅, by simp, by simp, ?_⟩ -- first take care of `p = 0`
    simpa [hf.aestronglyMeasurable] using (pos_iff_ne_zero.2 hε)
  · obtain ⟨s, hsm, hs, hε⟩ :
        ∃ s, MeasurableSet s ∧ μ s < ∞ ∧ ∫⁻ a in sᶜ, (‖f a‖ₑ) ^ p.toReal ∂μ < ε ^ p.toReal := by
      apply exists_setLIntegral_compl_lt
      · exact ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp₀ hp_top
          hf.aestronglyMeasurable).1 hf).ne
      · simp [*]
    refine ⟨s, hsm, hs, ?_⟩
    rwa [eLpNorm_indicator_eq_eLpNorm_restrict hsm.compl,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top hf.aestronglyMeasurable.restrict, one_div,
      ENNReal.rpow_inv_lt_iff]
    simp [ENNReal.toReal_pos, *]

end UnifTight
end Lp
end MeasureTheory
