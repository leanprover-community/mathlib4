/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Classes for probability measures

We introduce the following typeclasses for measures:

* `IsZeroOrProbabilityMeasure μ`: `μ univ = 0 ∨ μ univ = 1`;
* `IsProbabilityMeasure μ`: `μ univ = 1`.
-/

namespace MeasureTheory

open Set Measure Filter Function ENNReal

variable {α β : Type*} {m0 : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α} {s : Set α}

section IsZeroOrProbabilityMeasure

/-- A measure `μ` is zero or a probability measure if `μ univ = 0` or `μ univ = 1`. This class
of measures appears naturally when conditioning on events, and many results which are true for
probability measures hold more generally over this class. -/
class IsZeroOrProbabilityMeasure (μ : Measure α) : Prop where
  measure_univ : μ univ = 0 ∨ μ univ = 1

lemma isZeroOrProbabilityMeasure_iff : IsZeroOrProbabilityMeasure μ ↔ μ univ = 0 ∨ μ univ = 1 :=
  ⟨fun _ ↦ IsZeroOrProbabilityMeasure.measure_univ, IsZeroOrProbabilityMeasure.mk⟩

lemma prob_le_one {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α} : μ s ≤ 1 := by
  apply (measure_mono (subset_univ _)).trans
  rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with h | h <;> simp [h]

lemma measureReal_le_one {μ : Measure α} [IsZeroOrProbabilityMeasure μ] {s : Set α} :
    μ.real s ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (ENNReal.ofReal_one.symm ▸ prob_le_one)

@[simp]
theorem one_le_prob_iff {μ : Measure α} [IsZeroOrProbabilityMeasure μ] : 1 ≤ μ s ↔ μ s = 1 :=
  ⟨fun h => le_antisymm prob_le_one h, fun h => h ▸ le_refl _⟩

instance (priority := 100) IsZeroOrProbabilityMeasure.toIsFiniteMeasure (μ : Measure α)
    [IsZeroOrProbabilityMeasure μ] : IsFiniteMeasure μ :=
  ⟨prob_le_one.trans_lt one_lt_top⟩

instance : IsZeroOrProbabilityMeasure (0 : Measure α) :=
  ⟨Or.inl rfl⟩

end IsZeroOrProbabilityMeasure

section IsProbabilityMeasure

/-- A measure `μ` is called a probability measure if `μ univ = 1`. -/
class IsProbabilityMeasure (μ : Measure α) : Prop where
  measure_univ : μ univ = 1

export MeasureTheory.IsProbabilityMeasure (measure_univ)

attribute [simp] IsProbabilityMeasure.measure_univ

lemma isProbabilityMeasure_iff : IsProbabilityMeasure μ ↔ μ univ = 1 :=
  ⟨fun _ ↦ measure_univ, IsProbabilityMeasure.mk⟩

instance (priority := 100) (μ : Measure α) [IsProbabilityMeasure μ] :
    IsZeroOrProbabilityMeasure μ :=
  ⟨Or.inr measure_univ⟩

theorem IsProbabilityMeasure.ne_zero (μ : Measure α) [IsProbabilityMeasure μ] : μ ≠ 0 :=
  mt measure_univ_eq_zero.2 <| by simp [measure_univ]

instance (priority := 100) IsProbabilityMeasure.neZero (μ : Measure α) [IsProbabilityMeasure μ] :
    NeZero μ := ⟨IsProbabilityMeasure.ne_zero μ⟩

theorem IsProbabilityMeasure.ae_neBot [IsProbabilityMeasure μ] : NeBot (ae μ) := inferInstance

theorem prob_add_prob_compl [IsProbabilityMeasure μ] (h : MeasurableSet s) : μ s + μ sᶜ = 1 :=
  (measure_add_measure_compl h).trans measure_univ

instance isProbabilityMeasureSMul [IsFiniteMeasure μ] [NeZero μ] :
    IsProbabilityMeasure ((μ univ)⁻¹ • μ) :=
  ⟨ENNReal.inv_mul_cancel (NeZero.ne (μ univ)) (measure_ne_top _ _)⟩

variable [IsProbabilityMeasure μ] {p : α → Prop} {f : β → α}

theorem Measure.isProbabilityMeasure_map {f : α → β} (hf : AEMeasurable f μ) :
    IsProbabilityMeasure (map f μ) :=
  ⟨by simp [map_apply_of_aemeasurable, hf]⟩

theorem Measure.isProbabilityMeasure_of_map {μ : Measure α} {f : α → β}
    (hf : AEMeasurable f μ) [IsProbabilityMeasure (μ.map f)] : IsProbabilityMeasure μ where
  measure_univ := by
    rw [← Set.preimage_univ (f := f), ← map_apply_of_aemeasurable hf .univ]
    exact IsProbabilityMeasure.measure_univ

theorem Measure.isProbabilityMeasure_map_iff {μ : Measure α} {f : α → β}
    (hf : AEMeasurable f μ) : IsProbabilityMeasure (μ.map f) ↔ IsProbabilityMeasure μ :=
  ⟨fun _ ↦ isProbabilityMeasure_of_map hf, fun _ ↦ isProbabilityMeasure_map hf⟩

instance IsProbabilityMeasure_comap_equiv (f : β ≃ᵐ α) : IsProbabilityMeasure (μ.comap f) := by
  rw [← MeasurableEquiv.map_symm]; exact isProbabilityMeasure_map f.symm.measurable.aemeasurable

/-- Note that this is not quite as useful as it looks because the measure takes values in `ℝ≥0∞`.
Thus the subtraction appearing is the truncated subtraction of `ℝ≥0∞`, rather than the
better-behaved subtraction of `ℝ`. -/
lemma prob_compl_eq_one_sub₀ (h : NullMeasurableSet s μ) : μ sᶜ = 1 - μ s := by
  rw [measure_compl₀ h (measure_ne_top _ _), measure_univ]

/-- Note that this is not quite as useful as it looks because the measure takes values in `ℝ≥0∞`.
Thus the subtraction appearing is the truncated subtraction of `ℝ≥0∞`, rather than the
better-behaved subtraction of `ℝ`. -/
theorem prob_compl_eq_one_sub (hs : MeasurableSet s) : μ sᶜ = 1 - μ s :=
  prob_compl_eq_one_sub₀ hs.nullMeasurableSet

@[simp] lemma prob_compl_eq_zero_iff₀ (hs : NullMeasurableSet s μ) : μ sᶜ = 0 ↔ μ s = 1 := by
  rw [prob_compl_eq_one_sub₀ hs, tsub_eq_zero_iff_le, one_le_prob_iff]

lemma prob_compl_eq_zero_iff (hs : MeasurableSet s) : μ sᶜ = 0 ↔ μ s = 1 := by
  simp [hs]

@[simp] lemma prob_compl_eq_one_iff₀ (hs : NullMeasurableSet s μ) : μ sᶜ = 1 ↔ μ s = 0 := by
  rw [← prob_compl_eq_zero_iff₀ hs.compl, compl_compl]

lemma prob_compl_eq_one_iff (hs : MeasurableSet s) : μ sᶜ = 1 ↔ μ s = 0 := by
  simp [hs]

lemma mem_ae_iff_prob_eq_one₀ (hs : NullMeasurableSet s μ) : s ∈ ae μ ↔ μ s = 1 :=
  mem_ae_iff.trans <| prob_compl_eq_zero_iff₀ hs

lemma mem_ae_iff_prob_eq_one (hs : MeasurableSet s) : s ∈ ae μ ↔ μ s = 1 :=
  mem_ae_iff.trans <| prob_compl_eq_zero_iff hs

lemma ae_iff_prob_eq_one (hp : Measurable p) : (∀ᵐ a ∂μ, p a) ↔ μ {a | p a} = 1 :=
  mem_ae_iff_prob_eq_one hp.setOf

lemma isProbabilityMeasure_comap (hf : Injective f) (hf' : ∀ᵐ a ∂μ, a ∈ range f)
    (hf'' : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) :
    IsProbabilityMeasure (μ.comap f) where
  measure_univ := by
    rw [comap_apply _ hf hf'' _ MeasurableSet.univ,
      ← mem_ae_iff_prob_eq_one (hf'' _ MeasurableSet.univ)]
    simpa

protected lemma _root_.MeasurableEmbedding.isProbabilityMeasure_comap (hf : MeasurableEmbedding f)
    (hf' : ∀ᵐ a ∂μ, a ∈ range f) : IsProbabilityMeasure (μ.comap f) :=
  isProbabilityMeasure_comap hf.injective hf' hf.measurableSet_image'

instance isProbabilityMeasure_map_up :
    IsProbabilityMeasure (μ.map ULift.up) := isProbabilityMeasure_map measurable_up.aemeasurable

instance isProbabilityMeasure_comap_down : IsProbabilityMeasure (μ.comap ULift.down) :=
  MeasurableEquiv.ulift.measurableEmbedding.isProbabilityMeasure_comap <| ae_of_all _ <| by
    simp [Function.Surjective.range_eq <| EquivLike.surjective _]

lemma Measure.eq_of_le_of_isProbabilityMeasure {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≤ ν) : μ = ν :=
  eq_of_le_of_measure_univ_eq hμν (by simp)

end IsProbabilityMeasure

section IsZeroOrProbabilityMeasure

instance isZeroOrProbabilityMeasureSMul :
    IsZeroOrProbabilityMeasure ((μ univ)⁻¹ • μ) := by
  rcases eq_zero_or_neZero μ with rfl | h
  · simp; infer_instance
  rcases eq_top_or_lt_top (μ univ) with h | h
  · simp [h]; infer_instance
  have : IsFiniteMeasure μ := ⟨h⟩
  infer_instance

variable [IsZeroOrProbabilityMeasure μ] {p : α → Prop} {f : β → α}

variable (μ) in
lemma eq_zero_or_isProbabilityMeasure : μ = 0 ∨ IsProbabilityMeasure μ := by
  rcases IsZeroOrProbabilityMeasure.measure_univ (μ := μ) with h | h
  · apply Or.inl (measure_univ_eq_zero.mp h)
  · exact Or.inr ⟨h⟩

instance {f : α → β} : IsZeroOrProbabilityMeasure (map f μ) := by
  by_cases hf : AEMeasurable f μ
  · simpa [isZeroOrProbabilityMeasure_iff, hf] using IsZeroOrProbabilityMeasure.measure_univ
  · simp [isZeroOrProbabilityMeasure_iff, hf]

lemma prob_compl_lt_one_sub_of_lt_prob {p : ℝ≥0∞} (hμs : p < μ s) (s_mble : MeasurableSet s) :
    μ sᶜ < 1 - p := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp at hμs
  · rw [prob_compl_eq_one_sub s_mble]
    apply ENNReal.sub_lt_of_sub_lt prob_le_one (Or.inl one_ne_top)
    convert hμs
    exact ENNReal.sub_sub_cancel one_ne_top (lt_of_lt_of_le hμs prob_le_one).le

lemma prob_compl_le_one_sub_of_le_prob {p : ℝ≥0∞} (hμs : p ≤ μ s) (s_mble : MeasurableSet s) :
    μ sᶜ ≤ 1 - p := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | h
  · simp
  · simpa [prob_compl_eq_one_sub s_mble] using tsub_le_tsub_left hμs 1

@[simp]
lemma inv_measure_univ_smul_eq_self : (μ univ)⁻¹ • μ = μ := by
  rcases eq_zero_or_isProbabilityMeasure μ with h | h <;> simp [h]

end IsZeroOrProbabilityMeasure

end MeasureTheory
