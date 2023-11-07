import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open ENNReal MeasureTheory

variable {α E : Type*} [NormedAddCommGroup E] {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  {f : α → E}

namespace MeasureTheory

section SMulMeasure

variable {c : ℝ≥0∞}

#noalign measure_theory.snorm'_smul_measure

theorem snorm_top_smul_measure (hc : c ≠ 0) : snorm f ∞ (c • μ) = snorm f ∞ μ := by
  simp_rw [snorm_exponent_top, essSup_smul_measure hc]
#align measure_theory.snorm_ess_sup_smul_measure MeasureTheory.snorm_top_smul_measure

lemma snorm_smul_measure_of_one_le (hp1 : 1 ≤ p) (hcp : c ≠ 0 ∨ p ≠ ∞) :
    snorm f p (c • μ) = c ^ (1 / p).toReal * snorm f p μ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · simp [snorm_top_smul_measure (hcp.neg_resolve_right rfl)]
  simp only [snorm_of_one_le_ne_top _ hp1 hp, lintegral_smul_measure, one_div]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), toReal_inv]

lemma snorm_smul_measure_le_of_one_le (hp1 : 1 ≤ p) :
    snorm f p (c • μ) ≤ c ^ (1 / p).toReal * snorm f p μ := by
  rcases eq_or_ne c 0 with rfl | hc; · simp
  exact (snorm_smul_measure_of_one_le hp1 (.inl hc)).le

lemma snorm_smul_measure_of_le_one (hp1 : p ≤ 1) : snorm f p (c • μ) = c * snorm f p μ := by
  rcases eq_or_ne p 0 with rfl | hp0; · simp
  simp only [snorm_of_ne_zero_le_one _ hp0 hp1, lintegral_smul_measure]

#noalign measure_theory.snorm_smul_measure_of_ne_zero
#noalign measure_theory.snorm_smul_measure_of_ne_top

theorem snorm_one_smul_measure (c : ℝ≥0∞) : snorm f 1 (c • μ) = c * snorm f 1 μ :=
  snorm_smul_measure_of_le_one le_rfl
#align measure_theory.snorm_one_smul_measure MeasureTheory.snorm_one_smul_measure

lemma snorm_smul_measure_lt_top {f : α → E} {c : ℝ≥0∞} (hf : snorm f p μ < ∞) (hc : c ≠ ∞) :
    snorm f p (c • μ) < ∞ := by
  cases le_total p 1 with
  | inl hp1 => rw [snorm_smul_measure_of_le_one hp1]; exact mul_lt_top hc hf.ne
  | inr hp1 =>
    exact (snorm_smul_measure_le_of_one_le hp1).trans_lt <|
      mul_lt_top (rpow_ne_top_of_nonneg (by positivity) hc) hf.ne

theorem Memℒp.smul_measure {f : α → E} {c : ℝ≥0∞} (hf : Memℒp f p μ) (hc : c ≠ ∞) :
    Memℒp f p (c • μ) :=
  ⟨hf.1.mono' (Measure.absolutelyContinuous_of_le_smul le_rfl), snorm_smul_measure_lt_top hf.2 hc⟩
#align measure_theory.mem_ℒp.smul_measure MeasureTheory.Memℒp.smul_measure

theorem Memℒp.of_measure_le_smul {μ' : Measure α} (c : ℝ≥0∞) (hc : c ≠ ∞) (hμ'_le : μ' ≤ c • μ)
    {f : α → E} (hf : Memℒp f p μ) : Memℒp f p μ' :=
  (hf.smul_measure hc).mono_measure hμ'_le
#align measure_theory.mem_ℒp.of_measure_le_smul MeasureTheory.Memℒp.of_measure_le_smul

end SMulMeasure

section AddMeasure

@[simp]
theorem snorm_one_add_measure (f : α → E) (μ ν : Measure α) :
    snorm f 1 (μ + ν) = snorm f 1 μ + snorm f 1 ν := by
  simp only [snorm_exponent_one, lintegral_add_measure]
#align measure_theory.snorm_one_add_measure MeasureTheory.snorm_one_add_measure

theorem snorm_le_add_measure_right (f : α → E) (μ ν : Measure α) :
    snorm f p μ ≤ snorm f p (μ + ν) :=
  snorm_mono_measure f <| Measure.le_add_right <| le_refl _
#align measure_theory.snorm_le_add_measure_right MeasureTheory.snorm_le_add_measure_right

theorem snorm_le_add_measure_left (f : α → E) (μ ν : Measure α) :
    snorm f p ν ≤ snorm f p (μ + ν) :=
  snorm_mono_measure f <| Measure.le_add_left <| le_refl _
#align measure_theory.snorm_le_add_measure_left MeasureTheory.snorm_le_add_measure_left

theorem Memℒp.left_of_add_measure {ν} (h : Memℒp f p (μ + ν)) : Memℒp f p μ :=
  h.mono_measure <| Measure.le_add_right <| le_refl _
#align measure_theory.mem_ℒp.left_of_add_measure MeasureTheory.Memℒp.left_of_add_measure

theorem Memℒp.right_of_add_measure {ν} (h : Memℒp f p (μ + ν)) : Memℒp f p ν :=
  h.mono_measure <| Measure.le_add_left <| le_refl _
#align measure_theory.mem_ℒp.right_of_add_measure MeasureTheory.Memℒp.right_of_add_measure

end AddMeasure

#noalign measure_theory.snorm'_eq_zero_of_ae_zero
#noalign measure_theory.snorm'_eq_zero_of_ae_zero'
#noalign measure_theory.ae_eq_zero_of_snorm'_eq_zero
#noalign measure_theory.snorm'_eq_zero_iff

#noalign measure_theory.snorm'_add_le
#noalign measure_theory.snorm'_add_le_of_le_one

section MapMeasure

variable {β : Type*} {mβ : MeasurableSpace β} {f : α → β} {g : β → E}

#noalign measure_theory.snorm_ess_sup_map_measure

theorem snorm_map_measure (hg : AEStronglyMeasurable g (Measure.map f μ)) (hf : AEMeasurable f μ) :
    snorm g p (Measure.map f μ) = snorm (g ∘ f) p μ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [snorm_exponent_zero]
    rw [Measure.map_apply₀ hf hg.nullMeasurableSet_support]; rfl
  rcases eq_or_ne p ∞ with rfl | hp_top
  · simpa only [snorm_exponent_top] using essSup_map_measure hg.ennnorm hf
  cases' le_total p 1 with hp1 hp1
  · simp only [snorm_of_ne_zero_le_one _ hp0 hp1]
    rw [lintegral_map' (hg.ennnorm.pow_const _) hf]; rfl
  · simp only [snorm_of_one_le_ne_top _ hp1 hp_top]
    rw [lintegral_map' (hg.ennnorm.pow_const _) hf]; rfl
#align measure_theory.snorm_map_measure MeasureTheory.snorm_map_measure

theorem memℒp_map_measure_iff (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : Memℒp g p (Measure.map f μ) ↔ Memℒp (g ∘ f) p μ := by
  simp [Memℒp, snorm_map_measure hg hf, hg.comp_aemeasurable hf, hg]
#align measure_theory.mem_ℒp_map_measure_iff MeasureTheory.memℒp_map_measure_iff

theorem Memℒp.comp_of_map (hg : Memℒp g p (Measure.map f μ)) (hf : AEMeasurable f μ) :
    Memℒp (g ∘ f) p μ :=
  (memℒp_map_measure_iff hg.aestronglyMeasurable hf).1 hg

theorem snorm_comp_measurePreserving {ν} (hg : AEStronglyMeasurable g ν)
    (hf : MeasurePreserving f μ ν) : snorm (g ∘ f) p μ = snorm g p ν :=
  Eq.symm <| hf.map_eq ▸ snorm_map_measure (hf.map_eq ▸ hg) hf.aemeasurable

theorem Memℒp.comp_measurePreserving {ν} (hg : Memℒp g p ν) (hf : MeasurePreserving f μ ν) :
    Memℒp (g ∘ f) p μ :=
  .comp_of_map (hf.map_eq.symm ▸ hg) hf.aemeasurable

end MapMeasure

end MeasureTheory

namespace MeasurableEmbedding

variable {β : Type*} {mβ : MeasurableSpace β} {f : α → β} {g : β → E}

#noalign measurable_embedding.snorm_ess_sup_map_measure

theorem snorm_map_measure (hf : MeasurableEmbedding f) :
    snorm g p (Measure.map f μ) = snorm (g ∘ f) p μ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [snorm_exponent_zero, hf.map_apply]; rfl
  rcases eq_or_ne p ∞ with rfl | hp_top
  · simpa only [snorm_exponent_top] using hf.essSup_map_measure
  cases' le_total p 1 with hp1 hp1
  · simp only [snorm_of_ne_zero_le_one _ hp0 hp1, hf.lintegral_map]; rfl
  · simp only [snorm_of_one_le_ne_top _ hp1 hp_top, hf.lintegral_map]; rfl
#align measurable_embedding.snorm_map_measure MeasurableEmbedding.snorm_map_measure

theorem memℒp_map_measure_iff (hf : MeasurableEmbedding f) :
    Memℒp g p (Measure.map f μ) ↔ Memℒp (g ∘ f) p μ := by
  simp_rw [Memℒp, hf.aestronglyMeasurable_map_iff, hf.snorm_map_measure]
#align measurable_embedding.mem_ℒp_map_measure_iff MeasurableEmbedding.memℒp_map_measure_iff

theorem _root_.MeasurableEquiv.memℒp_map_measure_iff (f : α ≃ᵐ β) :
    Memℒp g p (Measure.map f μ) ↔ Memℒp (g ∘ f) p μ :=
  f.measurableEmbedding.memℒp_map_measure_iff
#align measurable_equiv.mem_ℒp_map_measure_iff MeasurableEquiv.memℒp_map_measure_iff

end MeasurableEmbedding
