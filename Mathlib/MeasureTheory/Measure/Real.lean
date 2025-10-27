/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Measures as real-valued functions

Given a measure `μ`, we have defined `μ.real` as the function sending a set `s` to `(μ s).toReal`.
In this file, we develop a basic API around this notion.

We essentially copy relevant lemmas from the files `MeasureSpaceDef.lean`, `NullMeasurable.lean` and
`MeasureSpace.lean`, and adapt them by replacing in their name `measure` with `measureReal`.

Many lemmas require an assumption that some set has finite measure. These assumptions are written
in the form `(h : μ s ≠ ∞ := by finiteness)`, where `finiteness` is a tactic for goals of
the form `≠ ∞`.

There are certainly many missing lemmas. The missing ones should be added as they are needed.

There are no lemmas on infinite sums, as summability issues are really
more painful with reals than nonnegative extended reals. They should probably be added in the long
run.
-/

open MeasureTheory Measure Set
open scoped ENNReal NNReal Function symmDiff

namespace MeasureTheory

variable {α β ι : Type*} {_ : MeasurableSpace α} {μ : Measure α} {s s₁ s₂ s₃ t t₁ t₂ u : Set α}

theorem measureReal_eq_zero_iff (h : μ s ≠ ∞ := by finiteness) :
    μ.real s = 0 ↔ μ s = 0 := by
  rw [Measure.real, ENNReal.toReal_eq_zero_iff]
  exact or_iff_left h

theorem measureReal_ne_zero_iff (h : μ s ≠ ∞ := by finiteness) :
    μ.real s ≠ 0 ↔ μ s ≠ 0 := by
  simp [measureReal_eq_zero_iff, h]

@[simp] theorem measureReal_zero : (0 : Measure α).real = 0 := rfl

theorem measureReal_zero_apply (s : Set α) : (0 : Measure α).real s = 0 := rfl

@[simp] theorem measureReal_nonneg : 0 ≤ μ.real s := ENNReal.toReal_nonneg

@[simp] theorem measureReal_empty : μ.real ∅ = 0 := by simp [Measure.real]

@[simp] theorem measureReal_univ_eq_one [IsProbabilityMeasure μ] :
    μ.real Set.univ = 1 := by
  simp [Measure.real]

@[simp]
theorem measureReal_univ_pos [IsFiniteMeasure μ] [NeZero μ] : 0 < μ.real Set.univ :=
  ENNReal.toReal_pos (NeZero.ne (μ Set.univ)) (measure_ne_top μ univ)

theorem measureReal_univ_ne_zero [IsFiniteMeasure μ] [NeZero μ] : μ.real Set.univ ≠ 0 :=
  measureReal_univ_pos.ne'

@[simp]
theorem ofReal_measureReal (h : μ s ≠ ∞ := by finiteness) : ENNReal.ofReal (μ.real s) = μ s := by
  simp [measureReal_def, h]

theorem nonempty_of_measureReal_ne_zero (h : μ.real s ≠ 0) : s.Nonempty :=
  nonempty_iff_ne_empty.2 fun h' ↦ h <| h'.symm ▸ measureReal_empty

@[simp] theorem measureReal_ennreal_smul_apply (c : ℝ≥0∞) :
    (c • μ).real s = c.toReal * μ.real s := by
  simp [Measure.real]

@[simp] theorem measureReal_nnreal_smul_apply (c : ℝ≥0) :
    (c • μ).real s = c * μ.real s := by
  simp [measureReal_def]

theorem map_measureReal_apply [MeasurableSpace β] {f : α → β} (hf : Measurable f)
    {s : Set β} (hs : MeasurableSet s) : (μ.map f).real s = μ.real (f ⁻¹' s) := by
  simp_rw [measureReal_def, map_apply hf hs]

@[gcongr] theorem measureReal_mono (h : s₁ ⊆ s₂) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real s₁ ≤ μ.real s₂ :=
  ENNReal.toReal_mono h₂ (measure_mono h)

theorem measureReal_eq_measureReal_iff {m : MeasurableSpace β} {ν : Measure β} {t : Set β}
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : ν t ≠ ∞ := by finiteness) :
    μ.real s = ν.real t ↔ μ s = ν t := by
  simp [measureReal_def, ENNReal.toReal_eq_toReal_iff' h₁ h₂]

theorem measureReal_restrict_apply₀ (ht : NullMeasurableSet t (μ.restrict s)) :
    (μ.restrict s).real t = μ.real (t ∩ s) := by
  simp only [measureReal_def, restrict_apply₀ ht]

@[simp]
theorem measureReal_restrict_apply (ht : MeasurableSet t) :
    (μ.restrict s).real t = μ.real (t ∩ s) := by
  simp only [measureReal_def, restrict_apply ht]

theorem measureReal_restrict_apply_univ (s : Set α) : (μ.restrict s).real univ = μ.real s := by
  simp

@[simp]
theorem measureReal_restrict_apply' (hs : MeasurableSet s) :
    (μ.restrict s).real t = μ.real (t ∩ s) := by
  simp only [measureReal_def, restrict_apply' hs]

theorem measureReal_restrict_apply₀' (hs : NullMeasurableSet s μ) : μ.restrict s t = μ (t ∩ s) := by
  simp only [restrict_apply₀' hs]

@[simp]
theorem measureReal_restrict_apply_self (s : Set α) : (μ.restrict s).real s = μ.real s := by
  simp [measureReal_def]

theorem measureReal_mono_null (h : s₁ ⊆ s₂) (h₂ : μ.real s₂ = 0) (h'₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real s₁ = 0 := by
  rw [measureReal_eq_zero_iff h'₂] at h₂
  simp [Measure.real, measure_mono_null h h₂]

theorem measureReal_le_measureReal_union_left (h : μ t ≠ ∞ := by finiteness) :
    μ.real s ≤ μ.real (s ∪ t) := by
  rcases eq_top_or_lt_top (μ s) with hs | hs
  · simp [Measure.real, hs]
  · exact measureReal_mono subset_union_left (measure_union_lt_top hs h.lt_top).ne

theorem measureReal_le_measureReal_union_right (h : μ s ≠ ∞ := by finiteness) :
    μ.real t ≤ μ.real (s ∪ t) := by
  rw [union_comm]
  exact measureReal_le_measureReal_union_left h

theorem measureReal_union_le (s₁ s₂ : Set α) : μ.real (s₁ ∪ s₂) ≤ μ.real s₁ + μ.real s₂ := by
  rcases eq_top_or_lt_top (μ (s₁ ∪ s₂)) with h | h
  · simp only [Measure.real, h, ENNReal.toReal_top]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · have A : μ s₁ ≠ ∞ := measure_ne_top_of_subset subset_union_left h.ne
    have B : μ s₂ ≠ ∞ := measure_ne_top_of_subset subset_union_right h.ne
    simp only [Measure.real, ← ENNReal.toReal_add A B]
    exact ENNReal.toReal_mono (by simp [A, B]) (measure_union_le _ _)

theorem measureReal_biUnion_finset_le (s : Finset β) (f : β → Set α) :
    μ.real (⋃ b ∈ s, f b) ≤ ∑ p ∈ s, μ.real (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert _ _ hx IH =>
    simp only [hx, Finset.mem_insert, iUnion_iUnion_eq_or_left, not_false_eq_true,
      Finset.sum_insert]
    exact (measureReal_union_le _ _).trans (by gcongr)

theorem measureReal_iUnion_fintype_le [Fintype β] (f : β → Set α) :
    μ.real (⋃ b, f b) ≤ ∑ p, μ.real (f p) := by
  convert measureReal_biUnion_finset_le Finset.univ f
  simp

theorem measureReal_iUnion_fintype [Fintype β] {f : β → Set α} (hn : Pairwise (Disjoint on f))
    (h : ∀ i, MeasurableSet (f i)) (h' : ∀ i, μ (f i) ≠ ∞ := by finiteness) :
    μ.real (⋃ b, f b) = ∑ p, μ.real (f p) := by
  simp_rw [measureReal_def, measure_iUnion hn h, tsum_fintype,
    ENNReal.toReal_sum (fun i _hi ↦ h' i)]

theorem measureReal_union_null (h₁ : μ.real s₁ = 0) (h₂ : μ.real s₂ = 0) :
    μ.real (s₁ ∪ s₂) = 0 :=
  le_antisymm ((measureReal_union_le s₁ s₂).trans (by simp [h₁, h₂])) measureReal_nonneg

@[simp]
theorem measureReal_union_null_iff
    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ s₂) = 0 ↔ μ.real s₁ = 0 ∧ μ.real s₂ = 0 :=
  ⟨fun h ↦ ⟨measureReal_mono_null subset_union_left h (by finiteness),
      measureReal_mono_null subset_union_right h (by finiteness)⟩,
  fun h ↦ measureReal_union_null h.1 h.2⟩

/-- If two sets are equal modulo a set of measure zero, then `μ.real s = μ.real t`. -/
theorem measureReal_congr (H : s =ᵐ[μ] t) : μ.real s = μ.real t := by
  simp [Measure.real, measure_congr H]

theorem measureReal_inter_add_diff₀ (ht : NullMeasurableSet t μ)
    (h : μ s ≠ ∞ := by finiteness) :
    μ.real (s ∩ t) + μ.real (s \ t) = μ.real s := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_add, measure_inter_add_diff₀ s ht]
  · exact measure_ne_top_of_subset inter_subset_left h
  · exact measure_ne_top_of_subset diff_subset h

theorem measureReal_union_add_inter₀ (ht : NullMeasurableSet t μ)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t := by
  have : μ (s ∪ t) ≠ ∞ :=
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨h₁.lt_top, h₂.lt_top⟩ )).ne
  rw [← measureReal_inter_add_diff₀ ht this, Set.union_inter_cancel_right, union_diff_right,
    ← measureReal_inter_add_diff₀ ht h₁]
  ac_rfl

theorem measureReal_union_add_inter₀' (hs : NullMeasurableSet s μ)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t := by
  rw [union_comm, inter_comm, measureReal_union_add_inter₀ hs h₂ h₁, add_comm]

theorem measureReal_union₀ (ht : NullMeasurableSet t μ) (hd : AEDisjoint μ s t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) = μ.real s + μ.real t := by
  simp only [Measure.real]
  rw [measure_union₀ ht hd, ENNReal.toReal_add h₁ h₂]

theorem measureReal_union₀' (hs : NullMeasurableSet s μ) (hd : AEDisjoint μ s t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) = μ.real s + μ.real t := by
  rw [union_comm, measureReal_union₀ hs (AEDisjoint.symm hd) h₂ h₁, add_comm]

theorem measureReal_add_measureReal_compl₀ [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ) :
    μ.real s + μ.real sᶜ = μ.real univ := by
  rw [← measureReal_union₀' hs aedisjoint_compl_right, union_compl_self]

theorem measureReal_add_measureReal_compl [IsFiniteMeasure μ] (h : MeasurableSet s) :
    μ.real s + μ.real sᶜ = μ.real univ :=
  measureReal_add_measureReal_compl₀ h.nullMeasurableSet

theorem measureReal_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂)
    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ s₂) = μ.real s₁ + μ.real s₂ :=
  measureReal_union₀ h.nullMeasurableSet hd.aedisjoint h₁ h₂

theorem measureReal_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁)
    (h₁ : μ s₁ ≠ ∞ := by finiteness) (h₂ : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ s₂) = μ.real s₁ + μ.real s₂ :=
  measureReal_union₀' h.nullMeasurableSet hd.aedisjoint h₁ h₂

theorem measureReal_inter_add_diff (ht : MeasurableSet t)
    (h : μ s ≠ ∞ := by finiteness) :
    μ.real (s ∩ t) + μ.real (s \ t) = μ.real s := by
  simp only [Measure.real]
  rw [← ENNReal.toReal_add, measure_inter_add_diff _ ht]
  · exact measure_ne_top_of_subset inter_subset_left h
  · exact measure_ne_top_of_subset diff_subset h

theorem measureReal_diff_add_inter (ht : MeasurableSet t)
    (h : μ s ≠ ∞ := by finiteness) :
    μ.real (s \ t) + μ.real (s ∩ t) = μ.real s :=
  (add_comm _ _).trans (measureReal_inter_add_diff ht h)

theorem measureReal_union_add_inter (ht : MeasurableSet t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t :=
  measureReal_union_add_inter₀ ht.nullMeasurableSet h₁ h₂

theorem measureReal_union_add_inter' (hs : MeasurableSet s)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∪ t) + μ.real (s ∩ t) = μ.real s + μ.real t :=
  measureReal_union_add_inter₀' hs.nullMeasurableSet h₁ h₂

lemma measureReal_symmDiff_eq (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∆ t) = μ.real (s \ t) + μ.real (t \ s) := by
  simp only [Measure.real]
  rw [← ENNReal.toReal_add, measure_symmDiff_eq hs.nullMeasurableSet ht.nullMeasurableSet]
  · exact measure_ne_top_of_subset diff_subset h₁
  · exact measure_ne_top_of_subset diff_subset h₂

lemma measureReal_symmDiff_le (u : Set α)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s ∆ u) ≤ μ.real (s ∆ t) + μ.real (t ∆ u) := by
  rcases eq_top_or_lt_top (μ u) with hu | hu
  · simp only [measureReal_def, measure_symmDiff_eq_top h₁ hu, ENNReal.toReal_top]
    exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · exact le_trans (measureReal_mono (symmDiff_triangle s t u)
        (measure_union_ne_top (by finiteness) (by finiteness)))
      (measureReal_union_le (s ∆ t) (t ∆ u))

theorem measureReal_biUnion_finset₀ {s : Finset ι} {f : ι → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : ∀ b ∈ s, NullMeasurableSet (f b) μ)
    (h : ∀ b ∈ s, μ (f b) ≠ ∞ := by finiteness) :
    μ.real (⋃ b ∈ s, f b) = ∑ p ∈ s, μ.real (f p) := by
  simp only [measureReal_def, measure_biUnion_finset₀ hd hm, ENNReal.toReal_sum h]

theorem measureReal_biUnion_finset {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : ∀ b ∈ s, MeasurableSet (f b)) (h : ∀ b ∈ s, μ (f b) ≠ ∞ := by finiteness) :
    μ.real (⋃ b ∈ s, f b) = ∑ p ∈ s, μ.real (f p) :=
  measureReal_biUnion_finset₀ hd.aedisjoint (fun b hb ↦ (hm b hb).nullMeasurableSet) h

/-- If `s` is a `Finset`, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem sum_measureReal_preimage_singleton (s : Finset β) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) (h : ∀ a ∈ s, μ (f ⁻¹' {a}) ≠ ∞ := by finiteness) :
    (∑ b ∈ s, μ.real (f ⁻¹' {b})) = μ.real (f ⁻¹' s) := by
  simp only [measureReal_def, ← sum_measure_preimage_singleton s hf, ENNReal.toReal_sum h]

/-- If `s` is a `Finset`, then the sums of the real measures of the singletons in the set is the
real measure of the set. -/
@[simp] theorem sum_measureReal_singleton [MeasurableSingletonClass α] [SigmaFinite μ]
    (s : Finset α) :
    (∑ b ∈ s, μ.real {b}) = μ.real s := by
  simp [measureReal_def, ← ENNReal.toReal_sum (fun _ _ ↦ ne_of_lt measure_singleton_lt_top)]

theorem measureReal_diff_null' (h : μ.real (s₁ ∩ s₂) = 0) (h' : μ s₁ ≠ ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ := by
  simp only [measureReal_def]
  rw [measure_diff_null']
  exact (measureReal_eq_zero_iff (measure_ne_top_of_subset inter_subset_left h')).1 h

theorem measureReal_diff_null (h : μ.real s₂ = 0) (h' : μ s₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ := by
  rcases eq_top_or_lt_top (μ s₁) with H | H
  · simp [measureReal_def, H, measure_diff_eq_top H h']
  · exact measureReal_diff_null' (measureReal_mono_null inter_subset_right h h') H.ne

theorem measureReal_add_diff (hs : MeasurableSet s)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real s + μ.real (t \ s) = μ.real (s ∪ t) := by
  rw [← measureReal_union' (@disjoint_sdiff_right _ s t) hs h₁
    (measure_ne_top_of_subset diff_subset h₂), union_diff_self]

theorem measureReal_diff' (hm : MeasurableSet t)
    (h₁ : μ s ≠ ∞ := by finiteness) (h₂ : μ t ≠ ∞ := by finiteness) :
    μ.real (s \ t) = μ.real (s ∪ t) - μ.real t := by
  rw [union_comm, ← measureReal_add_diff hm h₂ h₁]
  ring

theorem measureReal_diff (h : s₂ ⊆ s₁) (h₂ : MeasurableSet s₂) (h₁ : μ s₁ ≠ ∞ := by finiteness) :
    μ.real (s₁ \ s₂) = μ.real s₁ - μ.real s₂ := by
  rw [measureReal_diff' h₂ h₁ (measure_ne_top_of_subset h h₁), union_eq_self_of_subset_right h]

theorem le_measureReal_diff (h : μ s₂ ≠ ∞ := by finiteness) :
    μ.real s₁ - μ.real s₂ ≤ μ.real (s₁ \ s₂) := by
  simp only [tsub_le_iff_left]
  calc
    μ.real s₁ ≤ μ.real (s₂ ∪ s₁) := measureReal_le_measureReal_union_right h
    _ = μ.real (s₂ ∪ s₁ \ s₂) := congr_arg μ.real union_diff_self.symm
    _ ≤ μ.real s₂ + μ.real (s₁ \ s₂) := measureReal_union_le _ _

theorem measureReal_diff_lt_of_lt_add (hs : MeasurableSet s) (hst : s ⊆ t) (ε : ℝ)
    (h : μ.real t < μ.real s + ε) (ht' : μ t ≠ ∞ := by finiteness) :
    μ.real (t \ s) < ε := by
  rw [measureReal_diff hst hs ht']; linarith

theorem measureReal_diff_le_iff_le_add (hs : MeasurableSet s) (hst : s ⊆ t) (ε : ℝ)
    (ht' : μ t ≠ ∞ := by finiteness) :
    μ.real (t \ s) ≤ ε ↔ μ.real t ≤ μ.real s + ε := by
  rw [measureReal_diff hst hs ht', tsub_le_iff_left]

theorem measureReal_eq_measureReal_of_null_diff (hst : s ⊆ t)
    (h_nulldiff : μ.real (t \ s) = 0) (h : μ (t \ s) ≠ ∞ := by finiteness) :
    μ.real s = μ.real t := by
  rw [measureReal_eq_zero_iff h] at h_nulldiff
  simp [measureReal_def, measure_eq_measure_of_null_diff hst h_nulldiff]

theorem measureReal_eq_measureReal_of_between_null_diff
    (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0)
    (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
    μ.real s₁ = μ.real s₂ ∧ μ.real s₂ = μ.real s₃ := by
  have A : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ :=
    measure_eq_measure_of_between_null_diff h12 h23 ((measureReal_eq_zero_iff h').1 h_nulldiff)
  simp [measureReal_def, A.1, A.2]

theorem measureReal_eq_measureReal_smaller_of_between_null_diff (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0)
    (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
    μ.real s₁ = μ.real s₂ :=
  (measureReal_eq_measureReal_of_between_null_diff h12 h23 h_nulldiff h').1

theorem measureReal_eq_measureReal_larger_of_between_null_diff (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nulldiff : μ.real (s₃ \ s₁) = 0) (h' : μ (s₃ \ s₁) ≠ ∞ := by finiteness) :
    μ.real s₂ = μ.real s₃ :=
  (measureReal_eq_measureReal_of_between_null_diff h12 h23 h_nulldiff h').2

theorem measureReal_compl [IsFiniteMeasure μ] (h₁ : MeasurableSet s) :
    μ.real sᶜ = μ.real univ - μ.real s := by
  rw [compl_eq_univ_diff]
  exact measureReal_diff (subset_univ s) h₁

theorem measureReal_union_congr_of_subset (hs : s₁ ⊆ s₂)
    (hsμ : μ.real s₂ ≤ μ.real s₁) (ht : t₁ ⊆ t₂) (htμ : μ.real t₂ ≤ μ.real t₁)
    (h₁ : μ s₂ ≠ ∞ := by finiteness) (h₂ : μ t₂ ≠ ∞ := by finiteness) :
    μ.real (s₁ ∪ t₁) = μ.real (s₂ ∪ t₂) := by
  simp only [measureReal_def]
  rw [measure_union_congr_of_subset hs _ ht]
  · exact (ENNReal.toReal_le_toReal h₂ (measure_ne_top_of_subset ht h₂)).1 htμ
  · exact (ENNReal.toReal_le_toReal h₁ (measure_ne_top_of_subset hs h₁)).1 hsμ

theorem sum_measureReal_le_measureReal_univ [IsFiniteMeasure μ] {s : Finset ι} {t : ι → Set α}
    (h : ∀ i ∈ s, MeasurableSet (t i)) (H : Set.PairwiseDisjoint (↑s) t) :
    (∑ i ∈ s, μ.real (t i)) ≤ μ.real univ := by
  simp only [measureReal_def]
  rw [← ENNReal.toReal_sum (by finiteness)]
  apply ENNReal.toReal_mono (by finiteness)
  exact sum_measure_le_measure_univ (fun i mi ↦ (h i mi).nullMeasurableSet) H.aedisjoint

theorem measureReal_add_apply {μ₁ μ₂ : Measure α} (h₁ : μ₁ s ≠ ∞ := by finiteness)
    (h₂ : μ₂ s ≠ ∞ := by finiteness) :
    (μ₁ + μ₂).real s = μ₁.real s + μ₂.real s := by
  simp only [measureReal_def, add_apply, ENNReal.toReal_add h₁ h₂]

/-- Pigeonhole principle for measure spaces: if `s` is a `Finset` and
`∑ i ∈ s, μ.real (t i) > μ.real univ`, then one of the intersections `t i ∩ t j` is not empty. -/
theorem exists_nonempty_inter_of_measureReal_univ_lt_sum_measureReal [IsFiniteMeasure μ]
    {s : Finset ι} {t : ι → Set α} (h : ∀ i ∈ s, MeasurableSet (t i))
    (H : μ.real univ < ∑ i ∈ s, μ.real (t i)) :
    ∃ i ∈ s, ∃ j ∈ s, ∃ _h : i ≠ j, (t i ∩ t j).Nonempty := by
  apply exists_nonempty_inter_of_measure_univ_lt_sum_measure μ
    (fun i mi ↦ (h i mi).nullMeasurableSet)
  simp only [Measure.real] at H
  apply (ENNReal.toReal_lt_toReal (by finiteness) _).1
  · convert H
    rw [ENNReal.toReal_sum (by finiteness)]
  · exact (ENNReal.sum_lt_top.mpr (fun i hi ↦ measure_lt_top ..)).ne

/-- If two sets `s` and `t` are included in a set `u` of finite measure,
and `μ.real s + μ.real t > μ.real u`, then `s` intersects `t`.
Version assuming that `t` is measurable. -/
theorem nonempty_inter_of_measureReal_lt_add
    (ht : MeasurableSet t) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ.real u < μ.real s + μ.real t)
    (hu : μ u ≠ ∞ := by finiteness) :
    (s ∩ t).Nonempty := by
  apply nonempty_inter_of_measure_lt_add μ ht h's h't ?_
  apply (ENNReal.toReal_lt_toReal hu _).1
  · rw [ENNReal.toReal_add (measure_ne_top_of_subset h's hu) (measure_ne_top_of_subset h't hu)]
    exact h
  · exact ENNReal.add_ne_top.2 ⟨measure_ne_top_of_subset h's hu, measure_ne_top_of_subset h't hu⟩

/-- If two sets `s` and `t` are included in a set `u` of finite measure,
and `μ.real s + μ.real t > μ.real u`, then `s` intersects `t`.
Version assuming that `s` is measurable. -/
theorem nonempty_inter_of_measureReal_lt_add'
    (hs : MeasurableSet s) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ.real u < μ.real s + μ.real t)
    (hu : μ u ≠ ∞ := by finiteness) :
    (s ∩ t).Nonempty := by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measureReal_lt_add hs h't h's h hu

end MeasureTheory

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: applications of `μ.real` are nonnegative. -/
@[positivity MeasureTheory.Measure.real _ _]
def evalMeasureReal : PositivityExt where eval {_ _} _zα _pα e := do
  let .app (.app _ a) b ← whnfR e | throwError "not measureReal"
  let p ← mkAppOptM ``MeasureTheory.measureReal_nonneg #[none, none, a, b]
  pure (.nonnegative p)

end Mathlib.Meta.Positivity
