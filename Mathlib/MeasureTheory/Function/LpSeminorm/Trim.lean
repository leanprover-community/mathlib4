import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Trim

open Filter ENNReal

namespace MeasureTheory

variable {α β E : Type*} {m m0 : MeasurableSpace α} [NormedAddCommGroup E]
   [ConditionallyCompleteLattice β] [TopologicalSpace β] [ClosedIicTopology β] [MeasurableSpace β]
   [OpensMeasurableSpace β] {μ : @Measure α m0} {p : ℝ≥0∞}

#noalign measure_theory.snorm'_trim

theorem limsup_trim (hm : m ≤ m0) {f : α → β} (hf : Measurable[m] f) :
    (μ.trim hm).ae.limsup f = μ.ae.limsup f := by
  have : ∀ a, μ.trim hm {x | ¬f x ≤ a} = μ {x | ¬f x ≤ a} := fun a ↦ trim_measurableSet_eq hm <|
    hf isClosed_Iic.measurableSet.compl
  simp only [limsup_eq, ae_iff, ← this]; rfl
#align measure_theory.limsup_trim MeasureTheory.limsup_trim

theorem essSup_trim (hm : m ≤ m0) {f : α → β} (hf : Measurable[m] f) :
    essSup f (μ.trim hm) = essSup f μ := limsup_trim hm hf
#align measure_theory.ess_sup_trim MeasureTheory.essSup_trim

#noalign measure_theory.snorm_ess_sup_trim

theorem snorm_trim (hm : m ≤ m0) {f : α → E} (hf : StronglyMeasurable[m] f) :
    snorm f p (μ.trim hm) = snorm f p μ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [snorm_exponent_zero, trim_measurableSet_eq hm hf.measurableSet_support]
  rcases eq_or_ne p ∞ with rfl | hp_top
  · simp only [snorm_exponent_top, essSup_trim hm hf.ennnorm]
  cases' le_total p 1 with hp1 hp1
  · simp only [snorm_of_ne_zero_le_one _ hp0 hp1]
    exact lintegral_trim _ <| hf.ennnorm.pow_const _
  · simp only [snorm_of_one_le_ne_top _ hp1 hp_top]
    rw [lintegral_trim hm (hf.ennnorm.pow_const _)]
#align measure_theory.snorm_trim MeasureTheory.snorm_trim

theorem snorm_trim_ae (hm : m ≤ m0) {f : α → E} (hf : AEStronglyMeasurable f (μ.trim hm)) :
    snorm f p (μ.trim hm) = snorm f p μ := by
  rw [snorm_congr_ae hf.ae_eq_mk, snorm_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk)]
  exact snorm_trim hm hf.stronglyMeasurable_mk
#align measure_theory.snorm_trim_ae MeasureTheory.snorm_trim_ae

theorem memℒp.of_trim (hm : m ≤ m0) {f : α → E} (hf : Memℒp f p (μ.trim hm)) : Memℒp f p μ :=
  ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim hm hf.1,
    (snorm_trim_ae hm hf.1).ge.trans_lt hf.2⟩
#align measure_theory.mem_ℒp_of_mem_ℒp_trim MeasureTheory.memℒp.of_trim

