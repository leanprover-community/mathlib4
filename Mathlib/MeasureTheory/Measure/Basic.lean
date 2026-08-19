/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.NullMeasurable

/-!
# Measure spaces

The definition of a measure and a measure space are in `MeasureTheory.MeasureSpaceDef`, with
only a few basic properties. This file provides many more properties of these objects related to
set operations.
This separation allows the measurability tactic to import only the file `MeasureSpaceDef`, and to
be available in `MeasureSpace` (through `MeasurableSpace`).

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the measure of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, an outer measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

## Implementation notes

Given `μ : Measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

You often don't want to define a measure via its constructor.
Two ways that are sometimes more convenient:
* `Measure.ofMeasurable` is a way to define a measure by only giving its value on measurable sets
  and proving the properties (1) and (2) mentioned above.
* `OuterMeasure.toMeasure` is a way of obtaining a measure from an outer measure by showing that
  all measurable sets in the measurable space are Carathéodory measurable.

To prove that two measures are equal, there are multiple options:
* `ext`: two measures are equal if they are equal on all measurable sets.
* `ext_of_generateFrom_of_iUnion`: two measures are equal if they are equal on a π-system generating
  the measurable sets, if the π-system contains a spanning increasing sequence of sets where the
  measures take finite value (in particular the measures are σ-finite). This is a special case of
  the more general `ext_of_generateFrom_of_cover`
* `ext_of_generate_finite`: two finite measures are equal if they are equal on a π-system
  generating the measurable sets. This is a special case of `ext_of_generateFrom_of_iUnion` using
  `C ∪ {univ}`, but is easier to work with.

A `MeasureSpace` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space
-/

public section

open Set Function Filter ENNReal
open scoped symmDiff

namespace MeasureTheory

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} {s s₁ s₂ s₃ t u : Set α}

theorem measure_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂) : μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
  measure_union₀ h.nullMeasurableSet hd.aedisjoint

theorem measure_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁) : μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
  measure_union₀' h.nullMeasurableSet hd.aedisjoint

theorem measure_inter_add_sdiff (s : Set α) (ht : MeasurableSet t) : μ (s ∩ t) + μ (s \ t) = μ s :=
  measure_inter_add_sdiff₀ _ ht.nullMeasurableSet

@[deprecated (since := "2026-06-03")] alias measure_inter_add_diff := measure_inter_add_sdiff

theorem measure_sdiff_add_inter (s : Set α) (ht : MeasurableSet t) : μ (s \ t) + μ (s ∩ t) = μ s :=
  (add_comm _ _).trans (measure_inter_add_sdiff s ht)

@[deprecated (since := "2026-06-03")] alias measure_diff_add_inter := measure_sdiff_add_inter

theorem measure_sdiff_eq_top (hs : μ s = ∞) (ht : μ t ≠ ∞) : μ (s \ t) = ∞ := by
  contrapose! hs
  exact ((measure_mono (subset_sdiff_union s t)).trans_lt
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs.lt_top, ht.lt_top⟩))).ne

@[deprecated (since := "2026-06-03")] alias measure_diff_eq_top := measure_sdiff_eq_top

theorem measure_union_add_inter (s : Set α) (ht : MeasurableSet t) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [← measure_inter_add_sdiff (s ∪ t) ht, Set.union_inter_cancel_right, union_sdiff_right, ←
    measure_inter_add_sdiff s ht]
  ac_rfl

theorem measure_union_add_inter' (hs : MeasurableSet s) (t : Set α) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [union_comm, inter_comm, measure_union_add_inter t hs, add_comm]

lemma measure_symmDiff_eq (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    μ (s ∆ t) = μ (s \ t) + μ (t \ s) := by
  simpa only [symmDiff_def, sup_eq_union]
    using measure_union₀ (ht.diff hs) disjoint_sdiff_sdiff.aedisjoint

lemma measure_symmDiff_le (s t u : Set α) :
    μ (s ∆ u) ≤ μ (s ∆ t) + μ (t ∆ u) :=
  le_trans (μ.mono <| symmDiff_triangle s t u) (measure_union_le (s ∆ t) (t ∆ u))

theorem measure_symmDiff_eq_top (hs : μ s ≠ ∞) (ht : μ t = ∞) : μ (s ∆ t) = ∞ :=
  measure_mono_top subset_union_right (measure_sdiff_eq_top ht hs)

theorem measure_add_measure_compl (h : MeasurableSet s) : μ s + μ sᶜ = μ univ :=
  measure_add_measure_compl₀ h.nullMeasurableSet

theorem measure_biUnion₀ {s : Set β} {f : β → Set α} (hs : s.Countable)
    (hd : s.Pairwise (AEDisjoint μ on f)) (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
    μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) := by
  have := hs.toEncodable
  rw [biUnion_eq_iUnion]
  exact measure_iUnion₀ (hd.on_injective Subtype.coe_injective fun x => x.2) fun x => h x x.2

theorem measure_biUnion {s : Set β} {f : β → Set α} (hs : s.Countable) (hd : s.PairwiseDisjoint f)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) :=
  measure_biUnion₀ hs hd.aedisjoint fun b hb => (h b hb).nullMeasurableSet

theorem measure_sUnion₀ {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise (AEDisjoint μ))
    (h : ∀ s ∈ S, NullMeasurableSet s μ) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_biUnion, measure_biUnion₀ hs hd h]

theorem measure_sUnion {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise Disjoint)
    (h : ∀ s ∈ S, MeasurableSet s) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_biUnion, measure_biUnion hs hd h]

theorem measure_biUnion_finset₀ {s : Finset ι} {f : ι → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
    μ (⋃ b ∈ s, f b) = ∑ p ∈ s, μ (f p) := by
  rw [← Finset.sum_attach, Finset.attach_eq_univ, ← tsum_fintype (L := .unconditional s)]
  exact measure_biUnion₀ s.countable_toSet hd hm

theorem measure_biUnion_finset {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑ p ∈ s, μ (f p) :=
  measure_biUnion_finset₀ hd.aedisjoint fun b hb => (hm b hb).nullMeasurableSet

/-- The measure of an a.e. disjoint union (even uncountable) of null-measurable sets is at least
the sum of the measures of the sets. -/
theorem tsum_meas_le_meas_iUnion_of_disjoint₀ (μ : Measure α)
    {As : ι → Set α} (As_mble : ∀ i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) := by
  rw [ENNReal.tsum_eq_iSup_sum, iSup_le_iff]
  intro s
  simp only [← measure_biUnion_finset₀ (fun _i _hi _j _hj hij => As_disj hij) fun i _ => As_mble i]
  gcongr
  exact iUnion_subset fun _ ↦ Subset.rfl

/-- The measure of a disjoint union (even uncountable) of measurable sets is at least the sum of
the measures of the sets. -/
theorem tsum_meas_le_meas_iUnion_of_disjoint (μ : Measure α)
    {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) :=
  tsum_meas_le_meas_iUnion_of_disjoint₀ μ (fun i ↦ (As_mble i).nullMeasurableSet)
    (fun _ _ h ↦ Disjoint.aedisjoint (As_disj h))

/-- If `s` is a countable set, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem tsum_measure_preimage_singleton {s : Set β} (hs : s.Countable) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑' b : s, μ (f ⁻¹' {↑b})) = μ (f ⁻¹' s) := by
  rw [← Set.biUnion_preimage_singleton, measure_biUnion hs (pairwiseDisjoint_fiber f s) hf]

lemma measure_preimage_eq_zero_iff_of_countable {s : Set β} {f : α → β} (hs : s.Countable) :
    μ (f ⁻¹' s) = 0 ↔ ∀ x ∈ s, μ (f ⁻¹' {x}) = 0 := by
  rw [← biUnion_preimage_singleton, measure_biUnion_null_iff hs]

/-- If `s` is a `Finset`, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem sum_measure_preimage_singleton (s : Finset β) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑ b ∈ s, μ (f ⁻¹' {b})) = μ (f ⁻¹' ↑s) := by
  simp only [← measure_biUnion_finset (pairwiseDisjoint_fiber f s) hf,
    Finset.set_biUnion_preimage_singleton]

@[simp] lemma sum_measure_singleton {s : Finset α} [MeasurableSingletonClass α] :
    ∑ x ∈ s, μ {x} = μ s := by
  trans ∑ x ∈ s, μ (id ⁻¹' {x})
  · simp
  rw [sum_measure_preimage_singleton]
  · simp
  · simp

theorem measure_sdiff_null' (h : μ (s₁ ∩ s₂) = 0) : μ (s₁ \ s₂) = μ s₁ :=
  measure_congr <| sdiff_ae_eq_self.2 h

@[deprecated (since := "2026-06-03")] alias measure_diff_null' := measure_sdiff_null'

theorem measure_add_sdiff (hs : NullMeasurableSet s μ) (t : Set α) :
    μ s + μ (t \ s) = μ (s ∪ t) := by
  rw [← measure_union₀' hs disjoint_sdiff_right.aedisjoint, union_sdiff_self]

@[deprecated (since := "2026-06-03")] alias measure_add_diff := measure_add_sdiff

theorem measure_sdiff' (s : Set α) (hm : NullMeasurableSet t μ) (h_fin : μ t ≠ ∞) :
    μ (s \ t) = μ (s ∪ t) - μ t :=
  ENNReal.eq_sub_of_add_eq h_fin <| by rw [add_comm, measure_add_sdiff hm, union_comm]

@[deprecated (since := "2026-06-03")] alias measure_diff' := measure_sdiff'

theorem measure_sdiff (h : s₂ ⊆ s₁) (h₂ : NullMeasurableSet s₂ μ) (h_fin : μ s₂ ≠ ∞) :
    μ (s₁ \ s₂) = μ s₁ - μ s₂ := by rw [measure_sdiff' _ h₂ h_fin, union_eq_self_of_subset_right h]

@[deprecated (since := "2026-06-03")] alias measure_diff := measure_sdiff

theorem le_measure_sdiff : μ s₁ - μ s₂ ≤ μ (s₁ \ s₂) :=
  tsub_le_iff_left.2 <| (measure_le_inter_add_sdiff μ s₁ s₂).trans <| by
    gcongr; apply inter_subset_right

@[deprecated (since := "2026-06-03")] alias le_measure_diff := le_measure_sdiff

theorem le_measure_symmDiff : μ s₁ - μ s₂ ≤ μ (s₁ ∆ s₂) :=
  le_trans le_measure_sdiff (measure_mono <| by simp [symmDiff_def])

/-- If the measure of the symmetric difference of two sets is finite,
then one has infinite measure if and only if the other one does. -/
theorem measure_eq_top_iff_of_symmDiff (hμst : μ (s ∆ t) ≠ ∞) : μ s = ∞ ↔ μ t = ∞ := by
  suffices h : ∀ u v, μ (u ∆ v) ≠ ∞ → μ u = ∞ → μ v = ∞
    from ⟨h s t hμst, h t s (symmDiff_comm s t ▸ hμst)⟩
  intro u v hμuv hμu
  by_contra! hμv
  apply hμuv
  rw [Set.symmDiff_def, eq_top_iff]
  calc
    ∞ = μ u - μ v := by rw [ENNReal.sub_eq_top_iff.2 ⟨hμu, hμv⟩]
    _ ≤ μ (u \ v) := le_measure_sdiff
    _ ≤ μ (u \ v ∪ v \ u) := measure_mono subset_union_left

/-- If the measure of the symmetric difference of two sets is finite,
then one has finite measure if and only if the other one does. -/
theorem measure_ne_top_iff_of_symmDiff (hμst : μ (s ∆ t) ≠ ∞) : μ s ≠ ∞ ↔ μ t ≠ ∞ :=
    (measure_eq_top_iff_of_symmDiff hμst).ne

theorem measure_sdiff_lt_of_lt_add (hs : NullMeasurableSet s μ) (hst : s ⊆ t) (hs' : μ s ≠ ∞)
    {ε : ℝ≥0∞} (h : μ t < μ s + ε) : μ (t \ s) < ε := by
  rw [measure_sdiff hst hs hs']; rw [add_comm] at h
  exact ENNReal.sub_lt_of_lt_add (measure_mono hst) h

@[deprecated (since := "2026-06-03")] alias measure_diff_lt_of_lt_add := measure_sdiff_lt_of_lt_add

theorem measure_sdiff_le_iff_le_add (hs : NullMeasurableSet s μ) (hst : s ⊆ t) (hs' : μ s ≠ ∞)
    {ε : ℝ≥0∞} : μ (t \ s) ≤ ε ↔ μ t ≤ μ s + ε := by
  rw [measure_sdiff hst hs hs', tsub_le_iff_left]

@[deprecated (since := "2026-06-03")]
alias measure_diff_le_iff_le_add := measure_sdiff_le_iff_le_add

theorem measure_eq_measure_of_null_sdiff (hst : s ⊆ t) (h_nullsdiff : μ (t \ s) = 0) :
    μ s = μ t := measure_congr <|
      EventuallyLE.antisymm (LE.le.eventuallyLE hst) (ae_le_set.mpr h_nullsdiff)

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_of_null_diff := measure_eq_measure_of_null_sdiff

theorem measure_eq_measure_of_between_null_sdiff (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃)
    (h_nullsdiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ := by
  have le12 : μ s₁ ≤ μ s₂ := measure_mono h12
  have le23 : μ s₂ ≤ μ s₃ := measure_mono h23
  have key : μ s₃ ≤ μ s₁ :=
    calc
      μ s₃ = μ (s₃ \ s₁ ∪ s₁) := by rw [sdiff_union_of_subset (h12.trans h23)]
      _ ≤ μ (s₃ \ s₁) + μ s₁ := measure_union_le _ _
      _ = μ s₁ := by simp only [h_nullsdiff, zero_add]
  exact ⟨le12.antisymm (le23.trans key), le23.antisymm (key.trans le12)⟩

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_of_between_null_diff := measure_eq_measure_of_between_null_sdiff

theorem measure_eq_measure_smaller_of_between_null_sdiff (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nullsdiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ :=
  (measure_eq_measure_of_between_null_sdiff h12 h23 h_nullsdiff).1

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_smaller_of_between_null_diff :=
  measure_eq_measure_smaller_of_between_null_sdiff

theorem measure_eq_measure_larger_of_between_null_sdiff (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nullsdiff : μ (s₃ \ s₁) = 0) : μ s₂ = μ s₃ :=
  (measure_eq_measure_of_between_null_sdiff h12 h23 h_nullsdiff).2

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_larger_of_between_null_diff :=
  measure_eq_measure_larger_of_between_null_sdiff

lemma measure_compl₀ (h : NullMeasurableSet s μ) (hs : μ s ≠ ∞) :
    μ sᶜ = μ Set.univ - μ s := by
  rw [← measure_add_measure_compl₀ h, ENNReal.add_sub_cancel_left hs]

theorem measure_compl (h₁ : MeasurableSet s) (h_fin : μ s ≠ ∞) : μ sᶜ = μ univ - μ s :=
  measure_compl₀ h₁.nullMeasurableSet h_fin

lemma measure_inter_conull' (ht : μ (s \ t) = 0) : μ (s ∩ t) = μ s := by
  rw [← sdiff_compl, measure_sdiff_null']; rwa [← sdiff_eq]

lemma measure_inter_conull (ht : μ tᶜ = 0) : μ (s ∩ t) = μ s := by
  rw [← sdiff_compl, measure_sdiff_null ht]

@[simp]
theorem union_ae_eq_left_iff_ae_subset : (s ∪ t : Set α) =ᵐ[μ] s ↔ t ≤ᵐ[μ] s := by
  rw [ae_le_set]
  refine
    ⟨fun h => by simpa only [union_sdiff_left] using (ae_eq_set.mp h).1, fun h =>
      eventuallyLE_antisymm_iff.mpr
        ⟨by rwa [ae_le_set, union_sdiff_left],
          LE.le.eventuallyLE subset_union_left⟩⟩

@[simp]
theorem union_ae_eq_right_iff_ae_subset : (s ∪ t : Set α) =ᵐ[μ] t ↔ s ≤ᵐ[μ] t := by
  rw [union_comm, union_ae_eq_left_iff_ae_subset]

theorem ae_eq_of_ae_subset_of_measure_ge (h₁ : s ≤ᵐ[μ] t) (h₂ : μ t ≤ μ s)
    (hsm : NullMeasurableSet s μ) (ht : μ t ≠ ∞) : s =ᵐ[μ] t := by
  refine eventuallyLE_antisymm_iff.mpr ⟨h₁, ae_le_set.mpr ?_⟩
  replace h₂ : μ t = μ s := h₂.antisymm (measure_mono_ae h₁)
  replace ht : μ s ≠ ∞ := h₂ ▸ ht
  rw [measure_sdiff' t hsm ht, measure_congr (union_ae_eq_left_iff_ae_subset.mpr h₁), h₂, tsub_self]

/-- If `s ⊆ t`, `μ t ≤ μ s`, `μ t ≠ ∞`, and `s` is measurable, then `s =ᵐ[μ] t`. -/
theorem ae_eq_of_subset_of_measure_ge (h₁ : s ⊆ t) (h₂ : μ t ≤ μ s) (hsm : NullMeasurableSet s μ)
    (ht : μ t ≠ ∞) : s =ᵐ[μ] t :=
  ae_eq_of_ae_subset_of_measure_ge h₁.eventuallyLE h₂ hsm ht

theorem measure_iUnion_congr_of_subset {ι : Sort*} [Countable ι] {s : ι → Set α} {t : ι → Set α}
    (hsub : ∀ i, s i ⊆ t i) (h_le : ∀ i, μ (t i) ≤ μ (s i)) : μ (⋃ i, s i) = μ (⋃ i, t i) := by
  refine le_antisymm (by gcongr; apply hsub) ?_
  by_cases! htop : ∃ i, μ (t i) = ∞
  · rcases htop with ⟨i, hi⟩
    calc
      μ (⋃ i, t i) ≤ ∞ := le_top
      _ ≤ μ (s i) := hi ▸ h_le i
      _ ≤ μ (⋃ i, s i) := measure_mono <| subset_iUnion _ _
  set M := toMeasurable μ
  have H : ∀ b, (M (t b) ∩ M (⋃ b, s b) : Set α) =ᵐ[μ] M (t b) := by
    refine fun b => ae_eq_of_subset_of_measure_ge inter_subset_left ?_ ?_ ?_
    · calc
        μ (M (t b)) = μ (t b) := measure_toMeasurable _
        _ ≤ μ (s b) := h_le b
        _ ≤ μ (M (t b) ∩ M (⋃ b, s b)) :=
          measure_mono <|
            subset_inter ((hsub b).trans <| subset_toMeasurable _ _)
              ((subset_iUnion _ _).trans <| subset_toMeasurable _ _)
    · measurability
    · rw [measure_toMeasurable]
      exact htop b
  calc
    μ (⋃ b, t b) ≤ μ (⋃ b, M (t b)) := measure_mono (iUnion_mono fun b => subset_toMeasurable _ _)
    _ = μ (⋃ b, M (t b) ∩ M (⋃ b, s b)) :=
      measure_congr (Filter.EventuallyEq.countable_iUnion H).symm
    _ ≤ μ (M (⋃ b, s b)) := measure_mono (iUnion_subset fun b => inter_subset_right)
    _ = μ (⋃ b, s b) := measure_toMeasurable _

theorem measure_union_congr_of_subset {t₁ t₂ : Set α} (hs : s₁ ⊆ s₂) (hsμ : μ s₂ ≤ μ s₁)
    (ht : t₁ ⊆ t₂) (htμ : μ t₂ ≤ μ t₁) : μ (s₁ ∪ t₁) = μ (s₂ ∪ t₂) := by
  rw [union_eq_iUnion, union_eq_iUnion]
  exact measure_iUnion_congr_of_subset (Bool.forall_bool.2 ⟨ht, hs⟩) (Bool.forall_bool.2 ⟨htμ, hsμ⟩)

@[simp]
theorem measure_iUnion_toMeasurable {ι : Sort*} [Countable ι] (s : ι → Set α) :
    μ (⋃ i, toMeasurable μ (s i)) = μ (⋃ i, s i) :=
  Eq.symm <| measure_iUnion_congr_of_subset (fun _i => subset_toMeasurable _ _) fun _i ↦
    (measure_toMeasurable _).le

theorem measure_biUnion_toMeasurable {I : Set β} (hc : I.Countable) (s : β → Set α) :
    μ (⋃ b ∈ I, toMeasurable μ (s b)) = μ (⋃ b ∈ I, s b) := by
  have := hc.toEncodable
  simp only [biUnion_eq_iUnion, measure_iUnion_toMeasurable]

@[simp]
theorem measure_toMeasurable_union : μ (toMeasurable μ s ∪ t) = μ (s ∪ t) :=
  Eq.symm <|
    measure_union_congr_of_subset (subset_toMeasurable _ _) (measure_toMeasurable _).le Subset.rfl
      le_rfl

@[simp]
theorem measure_union_toMeasurable : μ (s ∪ toMeasurable μ t) = μ (s ∪ t) :=
  Eq.symm <|
    measure_union_congr_of_subset Subset.rfl le_rfl (subset_toMeasurable _ _)
      (measure_toMeasurable _).le

theorem sum_measure_le_measure_univ {s : Finset ι} {t : ι → Set α}
    (h : ∀ i ∈ s, NullMeasurableSet (t i) μ) (H : Set.Pairwise s (AEDisjoint μ on t)) :
    (∑ i ∈ s, μ (t i)) ≤ μ (univ : Set α) := by
  rw [← measure_biUnion_finset₀ H h]
  exact measure_mono (subset_univ _)

theorem tsum_measure_le_measure_univ {s : ι → Set α} (hs : ∀ i, NullMeasurableSet (s i) μ)
    (H : Pairwise (AEDisjoint μ on s)) : ∑' i, μ (s i) ≤ μ (univ : Set α) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun s =>
    sum_measure_le_measure_univ (fun i _hi => hs i) fun i _hi j _hj hij => H hij

/-- Pigeonhole principle for measure spaces: if `∑' i, μ (s i) > μ univ`, then
one of the intersections `s i ∩ s j` is not empty. -/
theorem exists_nonempty_inter_of_measure_univ_lt_tsum_measure
    (μ : Measure α) {s : ι → Set α} (hs : ∀ i, NullMeasurableSet (s i) μ)
    (H : μ (univ : Set α) < ∑' i, μ (s i)) : ∃ i j, i ≠ j ∧ (s i ∩ s j).Nonempty := by
  contrapose! H
  apply tsum_measure_le_measure_univ hs
  intro i j hij
  exact (disjoint_iff_inter_eq_empty.mpr (H i j hij)).aedisjoint

/-- Pigeonhole principle for measure spaces: if `s` is a `Finset` and
`∑ i ∈ s, μ (t i) > μ univ`, then one of the intersections `t i ∩ t j` is not empty. -/
theorem exists_nonempty_inter_of_measure_univ_lt_sum_measure (μ : Measure α)
    {s : Finset ι} {t : ι → Set α} (h : ∀ i ∈ s, NullMeasurableSet (t i) μ)
    (H : μ (univ : Set α) < ∑ i ∈ s, μ (t i)) :
    ∃ i ∈ s, ∃ j ∈ s, ∃ _h : i ≠ j, (t i ∩ t j).Nonempty := by
  contrapose! H
  apply sum_measure_le_measure_univ h
  intro i hi j hj hij
  exact (disjoint_iff_inter_eq_empty.mpr (H i hi j hj hij)).aedisjoint

/-- If two sets `s` and `t` are included in a set `u`, and `μ s + μ t > μ u`,
then `s` intersects `t`. Version assuming that `t` is measurable. -/
theorem nonempty_inter_of_measure_lt_add (μ : Measure α)
    (ht : MeasurableSet t) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ u < μ s + μ t) :
    (s ∩ t).Nonempty := by
  rw [← Set.not_disjoint_iff_nonempty_inter]
  contrapose! h
  calc
    μ s + μ t = μ (s ∪ t) := (measure_union h ht).symm
    _ ≤ μ u := measure_mono (union_subset h's h't)

/-- If two sets `s` and `t` are included in a set `u`, and `μ s + μ t > μ u`,
then `s` intersects `t`. Version assuming that `s` is measurable. -/
theorem nonempty_inter_of_measure_lt_add' (μ : Measure α)
    (hs : MeasurableSet s) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ u < μ s + μ t) :
    (s ∩ t).Nonempty := by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measure_lt_add μ hs h't h's h

/-- If `u` is a superset of `t` with the same (finite) measure (both sets possibly non-measurable),
then for any measurable set `s` one also has `μ (t ∩ s) = μ (u ∩ s)`. -/
theorem Measure.measure_inter_eq_of_measure_eq (hs : MeasurableSet s) (h : μ t = μ u)
    (htu : t ⊆ u) (ht_ne_top : μ t ≠ ∞) : μ (t ∩ s) = μ (u ∩ s) := by
  rw [h] at ht_ne_top
  refine le_antisymm (by gcongr) ?_
  have A : μ (u ∩ s) + μ (u \ s) ≤ μ (t ∩ s) + μ (u \ s) :=
    calc
      μ (u ∩ s) + μ (u \ s) = μ u := measure_inter_add_sdiff _ hs
      _ = μ t := h.symm
      _ = μ (t ∩ s) + μ (t \ s) := (measure_inter_add_sdiff _ hs).symm
      _ ≤ μ (t ∩ s) + μ (u \ s) := by gcongr
  have B : μ (u \ s) ≠ ∞ := (lt_of_le_of_lt (measure_mono sdiff_subset) ht_ne_top.lt_top).ne
  exact ENNReal.le_of_add_le_add_right B A

lemma Measure.measure_inter_eq_of_ae (h : ∀ᵐ a ∂μ, a ∈ t) :
    μ (t ∩ s) = μ s := by
  refine le_antisymm (measure_mono inter_subset_right) ?_
  apply EventuallyLE.measure_le
  filter_upwards [h] with x hx h'x using ⟨hx, h'x⟩

/-- The measurable superset `toMeasurable μ t` of `t` (which has the same measure as `t`)
satisfies, for any measurable set `s`, the equality `μ (toMeasurable μ t ∩ s) = μ (u ∩ s)`.
Here, we require that the measure of `t` is finite. The conclusion holds without this assumption
when the measure is s-finite (for example when it is σ-finite),
see `measure_toMeasurable_inter_of_sFinite`. -/
theorem Measure.measure_toMeasurable_inter (hs : MeasurableSet s) (ht : μ t ≠ ∞) :
    μ (toMeasurable μ t ∩ s) = μ (t ∩ s) :=
  (measure_inter_eq_of_measure_eq hs (measure_toMeasurable t).symm (subset_toMeasurable μ t)
      ht).symm

theorem measure_if {x : β} {t : Set β} [Decidable (x ∈ t)] :
    μ (if x ∈ t then s else ∅) = indicator t (fun _ => μ s) x := by split_ifs with h <;> simp [h]

/-- On a countable space, two measures are equal if they agree on measurable atoms. -/
lemma ext_of_measurableAtoms [Countable α] {ν : Measure α}
    (h : ∀ x, μ (measurableAtom x) = ν (measurableAtom x)) : μ = ν := by
  ext s hs
  have h1 : s = ⋃ x ∈ s, measurableAtom x := by
    ext y
    simp only [mem_iUnion, exists_prop]
    refine ⟨fun hy ↦ ?_, fun ⟨x, hx, hy⟩ ↦ ?_⟩
    · exact ⟨y, hy, mem_measurableAtom_self y⟩
    · exact mem_of_mem_measurableAtom hy hs hx
  rw [← sUnion_image] at h1
  rw [h1]
  have h_count : (measurableAtom '' s).Countable := s.to_countable.image _
  have h_disj : (measurableAtom '' s).Pairwise Disjoint := by
    intro t ht t' ht' h_eq
    obtain ⟨y, hys, hy⟩ := ht
    obtain ⟨y', hy's, hy'⟩ := ht'
    rw [← hy, ← hy'] at h_eq ⊢
    refine disjoint_measurableAtom_of_notMem fun hyy' ↦ h_eq ?_
    exact measurableAtom_eq_of_mem hyy'
  have h_meas (t) (ht : t ∈ measurableAtom '' s) : MeasurableSet t := by
    obtain ⟨x, hxs, hx⟩ := ht
    rw [← hx]
    exact MeasurableSet.measurableAtom_of_countable x
  rw [measure_sUnion h_count h_disj h_meas, measure_sUnion h_count h_disj h_meas]
  congr with s'
  have hs' := s'.2
  obtain ⟨x, hxs, hx⟩ := hs'
  rw [← hx]
  exact h x

end MeasureTheory
