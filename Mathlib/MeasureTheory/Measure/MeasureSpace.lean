/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

#align_import measure_theory.measure.measure_space from "leanprover-community/mathlib"@"343e80208d29d2d15f8050b929aa50fe4ce71b55"

/-!
# Measure spaces

The definition of a measure and a measure space are in `MeasureTheory.MeasureSpaceDef`, with
only a few basic properties. This file provides many more properties of these objects.
This separation allows the measurability tactic to import only the file `MeasureSpaceDef`, and to
be available in `MeasureSpace` (through `MeasurableSpace`).

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the measure of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, a measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ℝ≥0∞`.

Given a measure, the null sets are the sets where `μ s = 0`, where `μ` denotes the corresponding
outer measure (so `s` might not be measurable). We can then define the completion of `μ` as the
measure on the least `σ`-algebra that also contains all null sets, by defining the measure to be `0`
on the null sets.

## Main statements

* `completion` is the completion of a measure to all null measurable sets.
* `Measure.ofMeasurable` and `OuterMeasure.toMeasure` are two important ways to define a measure.

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
* <https://en.wikipedia.org/wiki/Complete_measure>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space, completion, null set, null measurable set
-/

noncomputable section

open Set

open Filter hiding map

open Function MeasurableSpace
open scoped Classical symmDiff
open Topology Filter ENNReal NNReal Interval MeasureTheory

variable {α β γ δ ι R R' : Type*}

namespace MeasureTheory

section

variable {m : MeasurableSpace α} {μ μ₁ μ₂ : Measure α} {s s₁ s₂ t : Set α}

instance ae_isMeasurablyGenerated : IsMeasurablyGenerated (ae μ) :=
  ⟨fun _s hs =>
    let ⟨t, hst, htm, htμ⟩ := exists_measurable_superset_of_null hs
    ⟨tᶜ, compl_mem_ae_iff.2 htμ, htm.compl, compl_subset_comm.1 hst⟩⟩
#align measure_theory.ae_is_measurably_generated MeasureTheory.ae_isMeasurablyGenerated

/-- See also `MeasureTheory.ae_restrict_uIoc_iff`. -/
theorem ae_uIoc_iff [LinearOrder α] {a b : α} {P : α → Prop} :
    (∀ᵐ x ∂μ, x ∈ Ι a b → P x) ↔ (∀ᵐ x ∂μ, x ∈ Ioc a b → P x) ∧ ∀ᵐ x ∂μ, x ∈ Ioc b a → P x := by
  simp only [uIoc_eq_union, mem_union, or_imp, eventually_and]
#align measure_theory.ae_uIoc_iff MeasureTheory.ae_uIoc_iff

theorem measure_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂) : μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
  measure_union₀ h.nullMeasurableSet hd.aedisjoint
#align measure_theory.measure_union MeasureTheory.measure_union

theorem measure_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁) : μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
  measure_union₀' h.nullMeasurableSet hd.aedisjoint
#align measure_theory.measure_union' MeasureTheory.measure_union'

theorem measure_inter_add_diff (s : Set α) (ht : MeasurableSet t) : μ (s ∩ t) + μ (s \ t) = μ s :=
  measure_inter_add_diff₀ _ ht.nullMeasurableSet
#align measure_theory.measure_inter_add_diff MeasureTheory.measure_inter_add_diff

theorem measure_diff_add_inter (s : Set α) (ht : MeasurableSet t) : μ (s \ t) + μ (s ∩ t) = μ s :=
  (add_comm _ _).trans (measure_inter_add_diff s ht)
#align measure_theory.measure_diff_add_inter MeasureTheory.measure_diff_add_inter

theorem measure_union_add_inter (s : Set α) (ht : MeasurableSet t) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [← measure_inter_add_diff (s ∪ t) ht, Set.union_inter_cancel_right, union_diff_right, ←
    measure_inter_add_diff s ht]
  ac_rfl
#align measure_theory.measure_union_add_inter MeasureTheory.measure_union_add_inter

theorem measure_union_add_inter' (hs : MeasurableSet s) (t : Set α) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [union_comm, inter_comm, measure_union_add_inter t hs, add_comm]
#align measure_theory.measure_union_add_inter' MeasureTheory.measure_union_add_inter'

lemma measure_symmDiff_eq (hs : MeasurableSet s) (ht : MeasurableSet t) :
    μ (s ∆ t) = μ (s \ t) + μ (t \ s) := by
  simpa only [symmDiff_def, sup_eq_union] using measure_union disjoint_sdiff_sdiff (ht.diff hs)

lemma measure_symmDiff_le (s t u : Set α) :
    μ (s ∆ u) ≤ μ (s ∆ t) + μ (t ∆ u) :=
  le_trans (μ.mono <| symmDiff_triangle s t u) (measure_union_le (s ∆ t) (t ∆ u))

theorem measure_add_measure_compl (h : MeasurableSet s) : μ s + μ sᶜ = μ univ :=
  measure_add_measure_compl₀ h.nullMeasurableSet
#align measure_theory.measure_add_measure_compl MeasureTheory.measure_add_measure_compl

theorem measure_biUnion₀ {s : Set β} {f : β → Set α} (hs : s.Countable)
    (hd : s.Pairwise (AEDisjoint μ on f)) (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
    μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) := by
  haveI := hs.toEncodable
  rw [biUnion_eq_iUnion]
  exact measure_iUnion₀ (hd.on_injective Subtype.coe_injective fun x => x.2) fun x => h x x.2
#align measure_theory.measure_bUnion₀ MeasureTheory.measure_biUnion₀

theorem measure_biUnion {s : Set β} {f : β → Set α} (hs : s.Countable) (hd : s.PairwiseDisjoint f)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) :=
  measure_biUnion₀ hs hd.aedisjoint fun b hb => (h b hb).nullMeasurableSet
#align measure_theory.measure_bUnion MeasureTheory.measure_biUnion

theorem measure_sUnion₀ {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise (AEDisjoint μ))
    (h : ∀ s ∈ S, NullMeasurableSet s μ) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_biUnion, measure_biUnion₀ hs hd h]
#align measure_theory.measure_sUnion₀ MeasureTheory.measure_sUnion₀

theorem measure_sUnion {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise Disjoint)
    (h : ∀ s ∈ S, MeasurableSet s) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_biUnion, measure_biUnion hs hd h]
#align measure_theory.measure_sUnion MeasureTheory.measure_sUnion

theorem measure_biUnion_finset₀ {s : Finset ι} {f : ι → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
    μ (⋃ b ∈ s, f b) = ∑ p ∈ s, μ (f p) := by
  rw [← Finset.sum_attach, Finset.attach_eq_univ, ← tsum_fintype]
  exact measure_biUnion₀ s.countable_toSet hd hm
#align measure_theory.measure_bUnion_finset₀ MeasureTheory.measure_biUnion_finset₀

theorem measure_biUnion_finset {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑ p ∈ s, μ (f p) :=
  measure_biUnion_finset₀ hd.aedisjoint fun b hb => (hm b hb).nullMeasurableSet
#align measure_theory.measure_bUnion_finset MeasureTheory.measure_biUnion_finset

/-- The measure of an a.e. disjoint union (even uncountable) of null-measurable sets is at least
the sum of the measures of the sets. -/
theorem tsum_meas_le_meas_iUnion_of_disjoint₀ {ι : Type*} [MeasurableSpace α] (μ : Measure α)
    {As : ι → Set α} (As_mble : ∀ i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) := by
  rw [ENNReal.tsum_eq_iSup_sum, iSup_le_iff]
  intro s
  simp only [← measure_biUnion_finset₀ (fun _i _hi _j _hj hij => As_disj hij) fun i _ => As_mble i]
  gcongr
  exact iUnion_subset fun _ ↦ Subset.rfl

/-- The measure of a disjoint union (even uncountable) of measurable sets is at least the sum of
the measures of the sets. -/
theorem tsum_meas_le_meas_iUnion_of_disjoint {ι : Type*} [MeasurableSpace α] (μ : Measure α)
    {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) :=
  tsum_meas_le_meas_iUnion_of_disjoint₀ μ (fun i ↦ (As_mble i).nullMeasurableSet)
    (fun _ _ h ↦ Disjoint.aedisjoint (As_disj h))
#align measure_theory.tsum_meas_le_meas_Union_of_disjoint MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint

/-- If `s` is a countable set, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem tsum_measure_preimage_singleton {s : Set β} (hs : s.Countable) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑' b : s, μ (f ⁻¹' {↑b})) = μ (f ⁻¹' s) := by
  rw [← Set.biUnion_preimage_singleton, measure_biUnion hs (pairwiseDisjoint_fiber f s) hf]
#align measure_theory.tsum_measure_preimage_singleton MeasureTheory.tsum_measure_preimage_singleton

lemma measure_preimage_eq_zero_iff_of_countable {s : Set β} {f : α → β} (hs : s.Countable) :
    μ (f ⁻¹' s) = 0 ↔ ∀ x ∈ s, μ (f ⁻¹' {x}) = 0 := by
  rw [← biUnion_preimage_singleton, measure_biUnion_null_iff hs]

/-- If `s` is a `Finset`, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem sum_measure_preimage_singleton (s : Finset β) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑ b ∈ s, μ (f ⁻¹' {b})) = μ (f ⁻¹' ↑s) := by
  simp only [← measure_biUnion_finset (pairwiseDisjoint_fiber f s) hf,
    Finset.set_biUnion_preimage_singleton]
#align measure_theory.sum_measure_preimage_singleton MeasureTheory.sum_measure_preimage_singleton

theorem measure_diff_null' (h : μ (s₁ ∩ s₂) = 0) : μ (s₁ \ s₂) = μ s₁ :=
  measure_congr <| diff_ae_eq_self.2 h
#align measure_theory.measure_diff_null' MeasureTheory.measure_diff_null'

theorem measure_add_diff (hs : MeasurableSet s) (t : Set α) : μ s + μ (t \ s) = μ (s ∪ t) := by
  rw [← measure_union' disjoint_sdiff_right hs, union_diff_self]
#align measure_theory.measure_add_diff MeasureTheory.measure_add_diff

theorem measure_diff' (s : Set α) (hm : MeasurableSet t) (h_fin : μ t ≠ ∞) :
    μ (s \ t) = μ (s ∪ t) - μ t :=
  Eq.symm <| ENNReal.sub_eq_of_add_eq h_fin <| by rw [add_comm, measure_add_diff hm, union_comm]
#align measure_theory.measure_diff' MeasureTheory.measure_diff'

theorem measure_diff (h : s₂ ⊆ s₁) (h₂ : MeasurableSet s₂) (h_fin : μ s₂ ≠ ∞) :
    μ (s₁ \ s₂) = μ s₁ - μ s₂ := by rw [measure_diff' _ h₂ h_fin, union_eq_self_of_subset_right h]
#align measure_theory.measure_diff MeasureTheory.measure_diff

theorem le_measure_diff : μ s₁ - μ s₂ ≤ μ (s₁ \ s₂) :=
  tsub_le_iff_left.2 <| (measure_le_inter_add_diff μ s₁ s₂).trans <| by
    gcongr; apply inter_subset_right
#align measure_theory.le_measure_diff MeasureTheory.le_measure_diff

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
    ∞ = μ u - μ v := (WithTop.sub_eq_top_iff.2 ⟨hμu, hμv⟩).symm
    _ ≤ μ (u \ v) := le_measure_diff
    _ ≤ μ (u \ v ∪ v \ u) := measure_mono subset_union_left

/-- If the measure of the symmetric difference of two sets is finite,
then one has finite measure if and only if the other one does. -/
theorem measure_ne_top_iff_of_symmDiff (hμst : μ (s ∆ t) ≠ ∞) : μ s ≠ ∞ ↔ μ t ≠ ∞ :=
    (measure_eq_top_iff_of_symmDiff hμst).ne

theorem measure_diff_lt_of_lt_add (hs : MeasurableSet s) (hst : s ⊆ t) (hs' : μ s ≠ ∞) {ε : ℝ≥0∞}
    (h : μ t < μ s + ε) : μ (t \ s) < ε := by
  rw [measure_diff hst hs hs']; rw [add_comm] at h
  exact ENNReal.sub_lt_of_lt_add (measure_mono hst) h
#align measure_theory.measure_diff_lt_of_lt_add MeasureTheory.measure_diff_lt_of_lt_add

theorem measure_diff_le_iff_le_add (hs : MeasurableSet s) (hst : s ⊆ t) (hs' : μ s ≠ ∞) {ε : ℝ≥0∞} :
    μ (t \ s) ≤ ε ↔ μ t ≤ μ s + ε := by rw [measure_diff hst hs hs', tsub_le_iff_left]
#align measure_theory.measure_diff_le_iff_le_add MeasureTheory.measure_diff_le_iff_le_add

theorem measure_eq_measure_of_null_diff {s t : Set α} (hst : s ⊆ t) (h_nulldiff : μ (t \ s) = 0) :
    μ s = μ t := measure_congr <|
      EventuallyLE.antisymm (HasSubset.Subset.eventuallyLE hst) (ae_le_set.mpr h_nulldiff)
#align measure_theory.measure_eq_measure_of_null_diff MeasureTheory.measure_eq_measure_of_null_diff

theorem measure_eq_measure_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃)
    (h_nulldiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ := by
  have le12 : μ s₁ ≤ μ s₂ := measure_mono h12
  have le23 : μ s₂ ≤ μ s₃ := measure_mono h23
  have key : μ s₃ ≤ μ s₁ :=
    calc
      μ s₃ = μ (s₃ \ s₁ ∪ s₁) := by rw [diff_union_of_subset (h12.trans h23)]
      _ ≤ μ (s₃ \ s₁) + μ s₁ := measure_union_le _ _
      _ = μ s₁ := by simp only [h_nulldiff, zero_add]
  exact ⟨le12.antisymm (le23.trans key), le23.antisymm (key.trans le12)⟩
#align measure_theory.measure_eq_measure_of_between_null_diff MeasureTheory.measure_eq_measure_of_between_null_diff

theorem measure_eq_measure_smaller_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nulldiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ :=
  (measure_eq_measure_of_between_null_diff h12 h23 h_nulldiff).1
#align measure_theory.measure_eq_measure_smaller_of_between_null_diff MeasureTheory.measure_eq_measure_smaller_of_between_null_diff

theorem measure_eq_measure_larger_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nulldiff : μ (s₃ \ s₁) = 0) : μ s₂ = μ s₃ :=
  (measure_eq_measure_of_between_null_diff h12 h23 h_nulldiff).2
#align measure_theory.measure_eq_measure_larger_of_between_null_diff MeasureTheory.measure_eq_measure_larger_of_between_null_diff

lemma measure_compl₀ (h : NullMeasurableSet s μ) (hs : μ s ≠ ∞) :
    μ sᶜ = μ Set.univ - μ s := by
  rw [← measure_add_measure_compl₀ h, ENNReal.add_sub_cancel_left hs]

theorem measure_compl (h₁ : MeasurableSet s) (h_fin : μ s ≠ ∞) : μ sᶜ = μ univ - μ s :=
  measure_compl₀ h₁.nullMeasurableSet h_fin
#align measure_theory.measure_compl MeasureTheory.measure_compl

lemma measure_inter_conull' (ht : μ (s \ t) = 0) : μ (s ∩ t) = μ s := by
  rw [← diff_compl, measure_diff_null']; rwa [← diff_eq]

lemma measure_inter_conull (ht : μ tᶜ = 0) : μ (s ∩ t) = μ s := by
  rw [← diff_compl, measure_diff_null ht]

@[simp]
theorem union_ae_eq_left_iff_ae_subset : (s ∪ t : Set α) =ᵐ[μ] s ↔ t ≤ᵐ[μ] s := by
  rw [ae_le_set]
  refine
    ⟨fun h => by simpa only [union_diff_left] using (ae_eq_set.mp h).1, fun h =>
      eventuallyLE_antisymm_iff.mpr
        ⟨by rwa [ae_le_set, union_diff_left],
          HasSubset.Subset.eventuallyLE subset_union_left⟩⟩
#align measure_theory.union_ae_eq_left_iff_ae_subset MeasureTheory.union_ae_eq_left_iff_ae_subset

@[simp]
theorem union_ae_eq_right_iff_ae_subset : (s ∪ t : Set α) =ᵐ[μ] t ↔ s ≤ᵐ[μ] t := by
  rw [union_comm, union_ae_eq_left_iff_ae_subset]
#align measure_theory.union_ae_eq_right_iff_ae_subset MeasureTheory.union_ae_eq_right_iff_ae_subset

theorem ae_eq_of_ae_subset_of_measure_ge (h₁ : s ≤ᵐ[μ] t) (h₂ : μ t ≤ μ s) (hsm : MeasurableSet s)
    (ht : μ t ≠ ∞) : s =ᵐ[μ] t := by
  refine eventuallyLE_antisymm_iff.mpr ⟨h₁, ae_le_set.mpr ?_⟩
  replace h₂ : μ t = μ s := h₂.antisymm (measure_mono_ae h₁)
  replace ht : μ s ≠ ∞ := h₂ ▸ ht
  rw [measure_diff' t hsm ht, measure_congr (union_ae_eq_left_iff_ae_subset.mpr h₁), h₂, tsub_self]
#align measure_theory.ae_eq_of_ae_subset_of_measure_ge MeasureTheory.ae_eq_of_ae_subset_of_measure_ge

/-- If `s ⊆ t`, `μ t ≤ μ s`, `μ t ≠ ∞`, and `s` is measurable, then `s =ᵐ[μ] t`. -/
theorem ae_eq_of_subset_of_measure_ge (h₁ : s ⊆ t) (h₂ : μ t ≤ μ s) (hsm : MeasurableSet s)
    (ht : μ t ≠ ∞) : s =ᵐ[μ] t :=
  ae_eq_of_ae_subset_of_measure_ge (HasSubset.Subset.eventuallyLE h₁) h₂ hsm ht
#align measure_theory.ae_eq_of_subset_of_measure_ge MeasureTheory.ae_eq_of_subset_of_measure_ge

theorem measure_iUnion_congr_of_subset [Countable β] {s : β → Set α} {t : β → Set α}
    (hsub : ∀ b, s b ⊆ t b) (h_le : ∀ b, μ (t b) ≤ μ (s b)) : μ (⋃ b, s b) = μ (⋃ b, t b) := by
  rcases Classical.em (∃ b, μ (t b) = ∞) with (⟨b, hb⟩ | htop)
  · calc
      μ (⋃ b, s b) = ∞ := top_unique (hb ▸ (h_le b).trans <| measure_mono <| subset_iUnion _ _)
      _ = μ (⋃ b, t b) := Eq.symm <| top_unique <| hb ▸ measure_mono (subset_iUnion _ _)
  push_neg at htop
  refine le_antisymm (measure_mono (iUnion_mono hsub)) ?_
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
    · exact (measurableSet_toMeasurable _ _).inter (measurableSet_toMeasurable _ _)
    · rw [measure_toMeasurable]
      exact htop b
  calc
    μ (⋃ b, t b) ≤ μ (⋃ b, M (t b)) := measure_mono (iUnion_mono fun b => subset_toMeasurable _ _)
    _ = μ (⋃ b, M (t b) ∩ M (⋃ b, s b)) := measure_congr (EventuallyEq.countable_iUnion H).symm
    _ ≤ μ (M (⋃ b, s b)) := measure_mono (iUnion_subset fun b => inter_subset_right)
    _ = μ (⋃ b, s b) := measure_toMeasurable _
#align measure_theory.measure_Union_congr_of_subset MeasureTheory.measure_iUnion_congr_of_subset

theorem measure_union_congr_of_subset {t₁ t₂ : Set α} (hs : s₁ ⊆ s₂) (hsμ : μ s₂ ≤ μ s₁)
    (ht : t₁ ⊆ t₂) (htμ : μ t₂ ≤ μ t₁) : μ (s₁ ∪ t₁) = μ (s₂ ∪ t₂) := by
  rw [union_eq_iUnion, union_eq_iUnion]
  exact measure_iUnion_congr_of_subset (Bool.forall_bool.2 ⟨ht, hs⟩) (Bool.forall_bool.2 ⟨htμ, hsμ⟩)
#align measure_theory.measure_union_congr_of_subset MeasureTheory.measure_union_congr_of_subset

@[simp]
theorem measure_iUnion_toMeasurable [Countable β] (s : β → Set α) :
    μ (⋃ b, toMeasurable μ (s b)) = μ (⋃ b, s b) :=
  Eq.symm <|
    measure_iUnion_congr_of_subset (fun _b => subset_toMeasurable _ _) fun _b =>
      (measure_toMeasurable _).le
#align measure_theory.measure_Union_to_measurable MeasureTheory.measure_iUnion_toMeasurable

theorem measure_biUnion_toMeasurable {I : Set β} (hc : I.Countable) (s : β → Set α) :
    μ (⋃ b ∈ I, toMeasurable μ (s b)) = μ (⋃ b ∈ I, s b) := by
  haveI := hc.toEncodable
  simp only [biUnion_eq_iUnion, measure_iUnion_toMeasurable]
#align measure_theory.measure_bUnion_to_measurable MeasureTheory.measure_biUnion_toMeasurable

@[simp]
theorem measure_toMeasurable_union : μ (toMeasurable μ s ∪ t) = μ (s ∪ t) :=
  Eq.symm <|
    measure_union_congr_of_subset (subset_toMeasurable _ _) (measure_toMeasurable _).le Subset.rfl
      le_rfl
#align measure_theory.measure_to_measurable_union MeasureTheory.measure_toMeasurable_union

@[simp]
theorem measure_union_toMeasurable : μ (s ∪ toMeasurable μ t) = μ (s ∪ t) :=
  Eq.symm <|
    measure_union_congr_of_subset Subset.rfl le_rfl (subset_toMeasurable _ _)
      (measure_toMeasurable _).le
#align measure_theory.measure_union_to_measurable MeasureTheory.measure_union_toMeasurable

theorem sum_measure_le_measure_univ {s : Finset ι} {t : ι → Set α}
    (h : ∀ i ∈ s, MeasurableSet (t i)) (H : Set.PairwiseDisjoint (↑s) t) :
    (∑ i ∈ s, μ (t i)) ≤ μ (univ : Set α) := by
  rw [← measure_biUnion_finset H h]
  exact measure_mono (subset_univ _)
#align measure_theory.sum_measure_le_measure_univ MeasureTheory.sum_measure_le_measure_univ

theorem tsum_measure_le_measure_univ {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i))
    (H : Pairwise (Disjoint on s)) : (∑' i, μ (s i)) ≤ μ (univ : Set α) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun s =>
    sum_measure_le_measure_univ (fun i _hi => hs i) fun i _hi j _hj hij => H hij
#align measure_theory.tsum_measure_le_measure_univ MeasureTheory.tsum_measure_le_measure_univ

/-- Pigeonhole principle for measure spaces: if `∑' i, μ (s i) > μ univ`, then
one of the intersections `s i ∩ s j` is not empty. -/
theorem exists_nonempty_inter_of_measure_univ_lt_tsum_measure {m : MeasurableSpace α}
    (μ : Measure α) {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i))
    (H : μ (univ : Set α) < ∑' i, μ (s i)) : ∃ i j, i ≠ j ∧ (s i ∩ s j).Nonempty := by
  contrapose! H
  apply tsum_measure_le_measure_univ hs
  intro i j hij
  exact disjoint_iff_inter_eq_empty.mpr (H i j hij)
#align measure_theory.exists_nonempty_inter_of_measure_univ_lt_tsum_measure MeasureTheory.exists_nonempty_inter_of_measure_univ_lt_tsum_measure

/-- Pigeonhole principle for measure spaces: if `s` is a `Finset` and
`∑ i ∈ s, μ (t i) > μ univ`, then one of the intersections `t i ∩ t j` is not empty. -/
theorem exists_nonempty_inter_of_measure_univ_lt_sum_measure {m : MeasurableSpace α} (μ : Measure α)
    {s : Finset ι} {t : ι → Set α} (h : ∀ i ∈ s, MeasurableSet (t i))
    (H : μ (univ : Set α) < ∑ i ∈ s, μ (t i)) :
    ∃ i ∈ s, ∃ j ∈ s, ∃ _h : i ≠ j, (t i ∩ t j).Nonempty := by
  contrapose! H
  apply sum_measure_le_measure_univ h
  intro i hi j hj hij
  exact disjoint_iff_inter_eq_empty.mpr (H i hi j hj hij)
#align measure_theory.exists_nonempty_inter_of_measure_univ_lt_sum_measure MeasureTheory.exists_nonempty_inter_of_measure_univ_lt_sum_measure

/-- If two sets `s` and `t` are included in a set `u`, and `μ s + μ t > μ u`,
then `s` intersects `t`. Version assuming that `t` is measurable. -/
theorem nonempty_inter_of_measure_lt_add {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (ht : MeasurableSet t) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ u < μ s + μ t) :
    (s ∩ t).Nonempty := by
  rw [← Set.not_disjoint_iff_nonempty_inter]
  contrapose! h
  calc
    μ s + μ t = μ (s ∪ t) := (measure_union h ht).symm
    _ ≤ μ u := measure_mono (union_subset h's h't)
#align measure_theory.nonempty_inter_of_measure_lt_add MeasureTheory.nonempty_inter_of_measure_lt_add

/-- If two sets `s` and `t` are included in a set `u`, and `μ s + μ t > μ u`,
then `s` intersects `t`. Version assuming that `s` is measurable. -/
theorem nonempty_inter_of_measure_lt_add' {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (hs : MeasurableSet s) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ u < μ s + μ t) :
    (s ∩ t).Nonempty := by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measure_lt_add μ hs h't h's h
#align measure_theory.nonempty_inter_of_measure_lt_add' MeasureTheory.nonempty_inter_of_measure_lt_add'

/-- Continuity from below: the measure of the union of a directed sequence of (not necessarily
-measurable) sets is the supremum of the measures. -/
theorem measure_iUnion_eq_iSup [Countable ι] {s : ι → Set α} (hd : Directed (· ⊆ ·) s) :
    μ (⋃ i, s i) = ⨆ i, μ (s i) := by
  cases nonempty_encodable ι
  -- WLOG, `ι = ℕ`
  generalize ht : Function.extend Encodable.encode s ⊥ = t
  replace hd : Directed (· ⊆ ·) t := ht ▸ hd.extend_bot Encodable.encode_injective
  suffices μ (⋃ n, t n) = ⨆ n, μ (t n) by
    simp only [← ht, Function.apply_extend μ, ← iSup_eq_iUnion,
      iSup_extend_bot Encodable.encode_injective, (· ∘ ·), Pi.bot_apply, bot_eq_empty,
      measure_empty] at this
    exact this.trans (iSup_extend_bot Encodable.encode_injective _)
  clear! ι
  -- The `≥` inequality is trivial
  refine le_antisymm ?_ (iSup_le fun i => measure_mono <| subset_iUnion _ _)
  -- Choose `T n ⊇ t n` of the same measure, put `Td n = disjointed T`
  set T : ℕ → Set α := fun n => toMeasurable μ (t n)
  set Td : ℕ → Set α := disjointed T
  have hm : ∀ n, MeasurableSet (Td n) :=
    MeasurableSet.disjointed fun n => measurableSet_toMeasurable _ _
  calc
    μ (⋃ n, t n) ≤ μ (⋃ n, T n) := measure_mono (iUnion_mono fun i => subset_toMeasurable _ _)
    _ = μ (⋃ n, Td n) := by rw [iUnion_disjointed]
    _ ≤ ∑' n, μ (Td n) := measure_iUnion_le _
    _ = ⨆ I : Finset ℕ, ∑ n ∈ I, μ (Td n) := ENNReal.tsum_eq_iSup_sum
    _ ≤ ⨆ n, μ (t n) := iSup_le fun I => by
      rcases hd.finset_le I with ⟨N, hN⟩
      calc
        (∑ n ∈ I, μ (Td n)) = μ (⋃ n ∈ I, Td n) :=
          (measure_biUnion_finset ((disjoint_disjointed T).set_pairwise I) fun n _ => hm n).symm
        _ ≤ μ (⋃ n ∈ I, T n) := measure_mono (iUnion₂_mono fun n _hn => disjointed_subset _ _)
        _ = μ (⋃ n ∈ I, t n) := measure_biUnion_toMeasurable I.countable_toSet _
        _ ≤ μ (t N) := measure_mono (iUnion₂_subset hN)
        _ ≤ ⨆ n, μ (t n) := le_iSup (μ ∘ t) N
#align measure_theory.measure_Union_eq_supr MeasureTheory.measure_iUnion_eq_iSup

/-- Continuity from below: the measure of the union of a sequence of
(not necessarily measurable) sets is the supremum of the measures of the partial unions. -/
theorem measure_iUnion_eq_iSup' {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [Countable ι] [Preorder ι] [IsDirected ι (· ≤ ·)]
    {f : ι → Set α} : μ (⋃ i, f i) = ⨆ i, μ (Accumulate f i) := by
  have hd : Directed (· ⊆ ·) (Accumulate f) := by
    intro i j
    rcases directed_of (· ≤ ·) i j with ⟨k, rik, rjk⟩
    exact ⟨k, biUnion_subset_biUnion_left fun l rli ↦ le_trans rli rik,
      biUnion_subset_biUnion_left fun l rlj ↦ le_trans rlj rjk⟩
  rw [← iUnion_accumulate]
  exact measure_iUnion_eq_iSup hd

theorem measure_biUnion_eq_iSup {s : ι → Set α} {t : Set ι} (ht : t.Countable)
    (hd : DirectedOn ((· ⊆ ·) on s) t) : μ (⋃ i ∈ t, s i) = ⨆ i ∈ t, μ (s i) := by
  haveI := ht.toEncodable
  rw [biUnion_eq_iUnion, measure_iUnion_eq_iSup hd.directed_val, ← iSup_subtype'']
#align measure_theory.measure_bUnion_eq_supr MeasureTheory.measure_biUnion_eq_iSup

/-- Continuity from above: the measure of the intersection of a decreasing sequence of measurable
sets is the infimum of the measures. -/
theorem measure_iInter_eq_iInf [Countable ι] {s : ι → Set α} (h : ∀ i, MeasurableSet (s i))
    (hd : Directed (· ⊇ ·) s) (hfin : ∃ i, μ (s i) ≠ ∞) : μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  rcases hfin with ⟨k, hk⟩
  have : ∀ t ⊆ s k, μ t ≠ ∞ := fun t ht => ne_top_of_le_ne_top hk (measure_mono ht)
  rw [← ENNReal.sub_sub_cancel hk (iInf_le _ k), ENNReal.sub_iInf, ←
    ENNReal.sub_sub_cancel hk (measure_mono (iInter_subset _ k)), ←
    measure_diff (iInter_subset _ k) (MeasurableSet.iInter h) (this _ (iInter_subset _ k)),
    diff_iInter, measure_iUnion_eq_iSup]
  · congr 1
    refine le_antisymm (iSup_mono' fun i => ?_) (iSup_mono fun i => ?_)
    · rcases hd i k with ⟨j, hji, hjk⟩
      use j
      rw [← measure_diff hjk (h _) (this _ hjk)]
      gcongr
    · rw [tsub_le_iff_right, ← measure_union, Set.union_comm]
      · exact measure_mono (diff_subset_iff.1 Subset.rfl)
      · apply disjoint_sdiff_left
      · apply h i
  · exact hd.mono_comp _ fun _ _ => diff_subset_diff_right
#align measure_theory.measure_Inter_eq_infi MeasureTheory.measure_iInter_eq_iInf

/-- Continuity from above: the measure of the intersection of a sequence of
measurable sets is the infimum of the measures of the partial intersections. -/
theorem measure_iInter_eq_iInf' {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    [Countable ι] [Preorder ι] [IsDirected ι (· ≤ ·)]
    {f : ι → Set α} (h : ∀ i, MeasurableSet (f i)) (hfin : ∃ i, μ (f i) ≠ ∞) :
    μ (⋂ i, f i) = ⨅ i, μ (⋂ j ≤ i, f j) := by
  let s := fun i ↦ ⋂ j ≤ i, f j
  have iInter_eq : ⋂ i, f i = ⋂ i, s i := by
    ext x; simp [s]; constructor
    · exact fun h _ j _ ↦ h j
    · intro h i
      rcases directed_of (· ≤ ·) i i with ⟨j, rij, -⟩
      exact h j i rij
  have ms : ∀ i, MeasurableSet (s i) :=
    fun i ↦ MeasurableSet.biInter (countable_univ.mono <| subset_univ _) fun i _ ↦ h i
  have hd : Directed (· ⊇ ·) s := by
    intro i j
    rcases directed_of (· ≤ ·) i j with ⟨k, rik, rjk⟩
    exact ⟨k, biInter_subset_biInter_left fun j rji ↦ le_trans rji rik,
      biInter_subset_biInter_left fun i rij ↦ le_trans rij rjk⟩
  have hfin' : ∃ i, μ (s i) ≠ ∞ := by
    rcases hfin with ⟨i, hi⟩
    rcases directed_of (· ≤ ·) i i with ⟨j, rij, -⟩
    exact ⟨j, ne_top_of_le_ne_top hi <| measure_mono <| biInter_subset_of_mem rij⟩
  exact iInter_eq ▸ measure_iInter_eq_iInf ms hd hfin'

/-- Continuity from below: the measure of the union of an increasing sequence of (not necessarily
measurable) sets is the limit of the measures. -/
theorem tendsto_measure_iUnion [Preorder ι] [IsDirected ι (· ≤ ·)] [Countable ι]
    {s : ι → Set α} (hm : Monotone s) : Tendsto (μ ∘ s) atTop (𝓝 (μ (⋃ n, s n))) := by
  rw [measure_iUnion_eq_iSup hm.directed_le]
  exact tendsto_atTop_iSup fun n m hnm => measure_mono <| hm hnm
#align measure_theory.tendsto_measure_Union MeasureTheory.tendsto_measure_iUnion

/-- Continuity from below: the measure of the union of a sequence of (not necessarily measurable)
sets is the limit of the measures of the partial unions. -/
theorem tendsto_measure_iUnion' {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    [Preorder ι] [IsDirected ι (· ≤ ·)] {f : ι → Set α} :
    Tendsto (fun i ↦ μ (Accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  rw [measure_iUnion_eq_iSup']
  exact tendsto_atTop_iSup fun i j hij ↦ by gcongr

/-- Continuity from above: the measure of the intersection of a decreasing sequence of measurable
sets is the limit of the measures. -/
theorem tendsto_measure_iInter [Countable ι] [Preorder ι] [IsDirected ι (· ≤ ·)] {s : ι → Set α}
    (hs : ∀ n, MeasurableSet (s n)) (hm : Antitone s) (hf : ∃ i, μ (s i) ≠ ∞) :
    Tendsto (μ ∘ s) atTop (𝓝 (μ (⋂ n, s n))) := by
  rw [measure_iInter_eq_iInf hs hm.directed_ge hf]
  exact tendsto_atTop_iInf fun n m hnm => measure_mono <| hm hnm
#align measure_theory.tendsto_measure_Inter MeasureTheory.tendsto_measure_iInter

/-- Continuity from above: the measure of the intersection of a sequence of measurable
sets such that one has finite measure is the limit of the measures of the partial intersections. -/
theorem tendsto_measure_iInter' {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι]
    [Preorder ι] [IsDirected ι (· ≤ ·)] {f : ι → Set α} (hm : ∀ i, MeasurableSet (f i))
    (hf : ∃ i, μ (f i) ≠ ∞) :
    Tendsto (fun i ↦ μ (⋂ j ∈ {j | j ≤ i}, f j)) atTop (𝓝 (μ (⋂ i, f i))) := by
  rw [measure_iInter_eq_iInf' hm hf]
  exact tendsto_atTop_iInf
    fun i j hij ↦ measure_mono <| biInter_subset_biInter_left fun k hki ↦ le_trans hki hij

/-- The measure of the intersection of a decreasing sequence of measurable
sets indexed by a linear order with first countable topology is the limit of the measures. -/
theorem tendsto_measure_biInter_gt {ι : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [DenselyOrdered ι] [FirstCountableTopology ι] {s : ι → Set α}
    {a : ι} (hs : ∀ r > a, MeasurableSet (s r)) (hm : ∀ i j, a < i → i ≤ j → s i ⊆ s j)
    (hf : ∃ r > a, μ (s r) ≠ ∞) : Tendsto (μ ∘ s) (𝓝[Ioi a] a) (𝓝 (μ (⋂ r > a, s r))) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun L hL => ?_⟩
  · filter_upwards [self_mem_nhdsWithin (s := Ioi a)] with r hr using hl.trans_le
        (measure_mono (biInter_subset_of_mem hr))
  obtain ⟨u, u_anti, u_pos, u_lim⟩ :
    ∃ u : ℕ → ι, StrictAnti u ∧ (∀ n : ℕ, a < u n) ∧ Tendsto u atTop (𝓝 a) := by
    rcases hf with ⟨r, ar, _⟩
    rcases exists_seq_strictAnti_tendsto' ar with ⟨w, w_anti, w_mem, w_lim⟩
    exact ⟨w, w_anti, fun n => (w_mem n).1, w_lim⟩
  have A : Tendsto (μ ∘ s ∘ u) atTop (𝓝 (μ (⋂ n, s (u n)))) := by
    refine tendsto_measure_iInter (fun n => hs _ (u_pos n)) ?_ ?_
    · intro m n hmn
      exact hm _ _ (u_pos n) (u_anti.antitone hmn)
    · rcases hf with ⟨r, rpos, hr⟩
      obtain ⟨n, hn⟩ : ∃ n : ℕ, u n < r := ((tendsto_order.1 u_lim).2 r rpos).exists
      refine ⟨n, ne_of_lt (lt_of_le_of_lt ?_ hr.lt_top)⟩
      exact measure_mono (hm _ _ (u_pos n) hn.le)
  have B : ⋂ n, s (u n) = ⋂ r > a, s r := by
    apply Subset.antisymm
    · simp only [subset_iInter_iff, gt_iff_lt]
      intro r rpos
      obtain ⟨n, hn⟩ : ∃ n, u n < r := ((tendsto_order.1 u_lim).2 _ rpos).exists
      exact Subset.trans (iInter_subset _ n) (hm (u n) r (u_pos n) hn.le)
    · simp only [subset_iInter_iff, gt_iff_lt]
      intro n
      apply biInter_subset_of_mem
      exact u_pos n
  rw [B] at A
  obtain ⟨n, hn⟩ : ∃ n, μ (s (u n)) < L := ((tendsto_order.1 A).2 _ hL).exists
  have : Ioc a (u n) ∈ 𝓝[>] a := Ioc_mem_nhdsWithin_Ioi ⟨le_rfl, u_pos n⟩
  filter_upwards [this] with r hr using lt_of_le_of_lt (measure_mono (hm _ _ hr.1 hr.2)) hn
#align measure_theory.tendsto_measure_bInter_gt MeasureTheory.tendsto_measure_biInter_gt

/-- One direction of the **Borel-Cantelli lemma** (sometimes called the "*first* Borel-Cantelli
lemma"): if (sᵢ) is a sequence of sets such that `∑ μ sᵢ` is finite, then the limit superior of the
`sᵢ` is a null set.

Note: for the *second* Borel-Cantelli lemma (applying to independent sets in a probability space),
see `ProbabilityTheory.measure_limsup_eq_one`. -/
theorem measure_limsup_eq_zero {s : ℕ → Set α} (hs : (∑' i, μ (s i)) ≠ ∞) :
    μ (limsup s atTop) = 0 := by
  -- First we replace the sequence `sₙ` with a sequence of measurable sets `tₙ ⊇ sₙ` of the same
  -- measure.
  set t : ℕ → Set α := fun n => toMeasurable μ (s n)
  have ht : (∑' i, μ (t i)) ≠ ∞ := by simpa only [t, measure_toMeasurable] using hs
  suffices μ (limsup t atTop) = 0 by
    have A : s ≤ t := fun n => subset_toMeasurable μ (s n)
    -- TODO default args fail
    exact measure_mono_null (limsup_le_limsup (eventually_of_forall (Pi.le_def.mp A))) this
  -- Next we unfold `limsup` for sets and replace equality with an inequality
  simp only [limsup_eq_iInf_iSup_of_nat', Set.iInf_eq_iInter, Set.iSup_eq_iUnion, ←
    nonpos_iff_eq_zero]
  -- Finally, we estimate `μ (⋃ i, t (i + n))` by `∑ i', μ (t (i + n))`
  refine
    le_of_tendsto_of_tendsto'
      (tendsto_measure_iInter
        (fun i => MeasurableSet.iUnion fun b => measurableSet_toMeasurable _ _) ?_
        ⟨0, ne_top_of_le_ne_top ht (measure_iUnion_le t)⟩)
      (ENNReal.tendsto_sum_nat_add (μ ∘ t) ht) fun n => measure_iUnion_le _
  intro n m hnm x
  simp only [Set.mem_iUnion]
  exact fun ⟨i, hi⟩ => ⟨i + (m - n), by simpa only [add_assoc, tsub_add_cancel_of_le hnm] using hi⟩
#align measure_theory.measure_limsup_eq_zero MeasureTheory.measure_limsup_eq_zero

theorem measure_liminf_eq_zero {s : ℕ → Set α} (h : (∑' i, μ (s i)) ≠ ∞) :
    μ (liminf s atTop) = 0 := by
  rw [← le_zero_iff]
  have : liminf s atTop ≤ limsup s atTop := liminf_le_limsup
  exact (μ.mono this).trans (by simp [measure_limsup_eq_zero h])
#align measure_theory.measure_liminf_eq_zero MeasureTheory.measure_liminf_eq_zero

-- Need to specify `α := Set α` below because of diamond; see #19041
theorem limsup_ae_eq_of_forall_ae_eq (s : ℕ → Set α) {t : Set α}
    (h : ∀ n, s n =ᵐ[μ] t) : limsup (α := Set α) s atTop =ᵐ[μ] t := by
  simp_rw [ae_eq_set] at h ⊢
  constructor
  · rw [atTop.limsup_sdiff s t]
    apply measure_limsup_eq_zero
    simp [h]
  · rw [atTop.sdiff_limsup s t]
    apply measure_liminf_eq_zero
    simp [h]
#align measure_theory.limsup_ae_eq_of_forall_ae_eq MeasureTheory.limsup_ae_eq_of_forall_ae_eq

-- Need to specify `α := Set α` above because of diamond; see #19041
theorem liminf_ae_eq_of_forall_ae_eq (s : ℕ → Set α) {t : Set α}
    (h : ∀ n, s n =ᵐ[μ] t) : liminf (α := Set α) s atTop =ᵐ[μ] t := by
  simp_rw [ae_eq_set] at h ⊢
  constructor
  · rw [atTop.liminf_sdiff s t]
    apply measure_liminf_eq_zero
    simp [h]
  · rw [atTop.sdiff_liminf s t]
    apply measure_limsup_eq_zero
    simp [h]
#align measure_theory.liminf_ae_eq_of_forall_ae_eq MeasureTheory.liminf_ae_eq_of_forall_ae_eq

theorem measure_if {x : β} {t : Set β} {s : Set α} :
    μ (if x ∈ t then s else ∅) = indicator t (fun _ => μ s) x := by split_ifs with h <;> simp [h]
#align measure_theory.measure_if MeasureTheory.measure_if

end

section OuterMeasure

variable [ms : MeasurableSpace α] {s t : Set α}

/-- Obtain a measure by giving an outer measure where all sets in the σ-algebra are
  Carathéodory measurable. -/
def OuterMeasure.toMeasure (m : OuterMeasure α) (h : ms ≤ m.caratheodory) : Measure α :=
  Measure.ofMeasurable (fun s _ => m s) m.empty fun _f hf hd =>
    m.iUnion_eq_of_caratheodory (fun i => h _ (hf i)) hd
#align measure_theory.outer_measure.to_measure MeasureTheory.OuterMeasure.toMeasure

theorem le_toOuterMeasure_caratheodory (μ : Measure α) : ms ≤ μ.toOuterMeasure.caratheodory :=
  fun _s hs _t => (measure_inter_add_diff _ hs).symm
#align measure_theory.le_to_outer_measure_caratheodory MeasureTheory.le_toOuterMeasure_caratheodory

@[simp]
theorem toMeasure_toOuterMeasure (m : OuterMeasure α) (h : ms ≤ m.caratheodory) :
    (m.toMeasure h).toOuterMeasure = m.trim :=
  rfl
#align measure_theory.to_measure_to_outer_measure MeasureTheory.toMeasure_toOuterMeasure

@[simp]
theorem toMeasure_apply (m : OuterMeasure α) (h : ms ≤ m.caratheodory) {s : Set α}
    (hs : MeasurableSet s) : m.toMeasure h s = m s :=
  m.trim_eq hs
#align measure_theory.to_measure_apply MeasureTheory.toMeasure_apply

theorem le_toMeasure_apply (m : OuterMeasure α) (h : ms ≤ m.caratheodory) (s : Set α) :
    m s ≤ m.toMeasure h s :=
  m.le_trim s
#align measure_theory.le_to_measure_apply MeasureTheory.le_toMeasure_apply

theorem toMeasure_apply₀ (m : OuterMeasure α) (h : ms ≤ m.caratheodory) {s : Set α}
    (hs : NullMeasurableSet s (m.toMeasure h)) : m.toMeasure h s = m s := by
  refine le_antisymm ?_ (le_toMeasure_apply _ _ _)
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, hts, htm, heq⟩
  calc
    m.toMeasure h s = m.toMeasure h t := measure_congr heq.symm
    _ = m t := toMeasure_apply m h htm
    _ ≤ m s := m.mono hts
#align measure_theory.to_measure_apply₀ MeasureTheory.toMeasure_apply₀

@[simp]
theorem toOuterMeasure_toMeasure {μ : Measure α} :
    μ.toOuterMeasure.toMeasure (le_toOuterMeasure_caratheodory _) = μ :=
  Measure.ext fun _s => μ.toOuterMeasure.trim_eq
#align measure_theory.to_outer_measure_to_measure MeasureTheory.toOuterMeasure_toMeasure

@[simp]
theorem boundedBy_measure (μ : Measure α) : OuterMeasure.boundedBy μ = μ.toOuterMeasure :=
  μ.toOuterMeasure.boundedBy_eq_self
#align measure_theory.bounded_by_measure MeasureTheory.boundedBy_measure

end OuterMeasure

section

/- Porting note: These variables are wrapped by an anonymous section because they interrupt
synthesizing instances in `MeasureSpace` section. -/

variable {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]
variable {μ μ₁ μ₂ μ₃ ν ν' ν₁ ν₂ : Measure α} {s s' t : Set α}
namespace Measure

/-- If `u` is a superset of `t` with the same (finite) measure (both sets possibly non-measurable),
then for any measurable set `s` one also has `μ (t ∩ s) = μ (u ∩ s)`. -/
theorem measure_inter_eq_of_measure_eq {s t u : Set α} (hs : MeasurableSet s) (h : μ t = μ u)
    (htu : t ⊆ u) (ht_ne_top : μ t ≠ ∞) : μ (t ∩ s) = μ (u ∩ s) := by
  rw [h] at ht_ne_top
  refine le_antisymm (by gcongr) ?_
  have A : μ (u ∩ s) + μ (u \ s) ≤ μ (t ∩ s) + μ (u \ s) :=
    calc
      μ (u ∩ s) + μ (u \ s) = μ u := measure_inter_add_diff _ hs
      _ = μ t := h.symm
      _ = μ (t ∩ s) + μ (t \ s) := (measure_inter_add_diff _ hs).symm
      _ ≤ μ (t ∩ s) + μ (u \ s) := by gcongr
  have B : μ (u \ s) ≠ ∞ := (lt_of_le_of_lt (measure_mono diff_subset) ht_ne_top.lt_top).ne
  exact ENNReal.le_of_add_le_add_right B A
#align measure_theory.measure.measure_inter_eq_of_measure_eq MeasureTheory.Measure.measure_inter_eq_of_measure_eq

/-- The measurable superset `toMeasurable μ t` of `t` (which has the same measure as `t`)
satisfies, for any measurable set `s`, the equality `μ (toMeasurable μ t ∩ s) = μ (u ∩ s)`.
Here, we require that the measure of `t` is finite. The conclusion holds without this assumption
when the measure is s-finite (for example when it is σ-finite),
see `measure_toMeasurable_inter_of_sFinite`. -/
theorem measure_toMeasurable_inter {s t : Set α} (hs : MeasurableSet s) (ht : μ t ≠ ∞) :
    μ (toMeasurable μ t ∩ s) = μ (t ∩ s) :=
  (measure_inter_eq_of_measure_eq hs (measure_toMeasurable t).symm (subset_toMeasurable μ t)
      ht).symm
#align measure_theory.measure.measure_to_measurable_inter MeasureTheory.Measure.measure_toMeasurable_inter

/-! ### The `ℝ≥0∞`-module of measures -/

instance instZero [MeasurableSpace α] : Zero (Measure α) :=
  ⟨{  toOuterMeasure := 0
      m_iUnion := fun _f _hf _hd => tsum_zero.symm
      trim_le := OuterMeasure.trim_zero.le }⟩
#align measure_theory.measure.has_zero MeasureTheory.Measure.instZero

@[simp]
theorem zero_toOuterMeasure {_m : MeasurableSpace α} : (0 : Measure α).toOuterMeasure = 0 :=
  rfl
#align measure_theory.measure.zero_to_outer_measure MeasureTheory.Measure.zero_toOuterMeasure

@[simp, norm_cast]
theorem coe_zero {_m : MeasurableSpace α} : ⇑(0 : Measure α) = 0 :=
  rfl
#align measure_theory.measure.coe_zero MeasureTheory.Measure.coe_zero

@[nontriviality]
lemma apply_eq_zero_of_isEmpty [IsEmpty α] {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) :
    μ s = 0 := by
  rw [eq_empty_of_isEmpty s, measure_empty]

instance instSubsingleton [IsEmpty α] {m : MeasurableSpace α} : Subsingleton (Measure α) :=
  ⟨fun μ ν => by ext1 s _; rw [apply_eq_zero_of_isEmpty, apply_eq_zero_of_isEmpty]⟩
#align measure_theory.measure.subsingleton MeasureTheory.Measure.instSubsingleton

theorem eq_zero_of_isEmpty [IsEmpty α] {_m : MeasurableSpace α} (μ : Measure α) : μ = 0 :=
  Subsingleton.elim μ 0
#align measure_theory.measure.eq_zero_of_is_empty MeasureTheory.Measure.eq_zero_of_isEmpty

instance instInhabited [MeasurableSpace α] : Inhabited (Measure α) :=
  ⟨0⟩
#align measure_theory.measure.inhabited MeasureTheory.Measure.instInhabited

instance instAdd [MeasurableSpace α] : Add (Measure α) :=
  ⟨fun μ₁ μ₂ =>
    { toOuterMeasure := μ₁.toOuterMeasure + μ₂.toOuterMeasure
      m_iUnion := fun s hs hd =>
        show μ₁ (⋃ i, s i) + μ₂ (⋃ i, s i) = ∑' i, (μ₁ (s i) + μ₂ (s i)) by
          rw [ENNReal.tsum_add, measure_iUnion hd hs, measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_add, μ₁.trimmed, μ₂.trimmed] }⟩
#align measure_theory.measure.has_add MeasureTheory.Measure.instAdd

@[simp]
theorem add_toOuterMeasure {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) :
    (μ₁ + μ₂).toOuterMeasure = μ₁.toOuterMeasure + μ₂.toOuterMeasure :=
  rfl
#align measure_theory.measure.add_to_outer_measure MeasureTheory.Measure.add_toOuterMeasure

@[simp, norm_cast]
theorem coe_add {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) : ⇑(μ₁ + μ₂) = μ₁ + μ₂ :=
  rfl
#align measure_theory.measure.coe_add MeasureTheory.Measure.coe_add

theorem add_apply {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) (s : Set α) :
    (μ₁ + μ₂) s = μ₁ s + μ₂ s :=
  rfl
#align measure_theory.measure.add_apply MeasureTheory.Measure.add_apply

section SMul

variable [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
variable [SMul R' ℝ≥0∞] [IsScalarTower R' ℝ≥0∞ ℝ≥0∞]

instance instSMul [MeasurableSpace α] : SMul R (Measure α) :=
  ⟨fun c μ =>
    { toOuterMeasure := c • μ.toOuterMeasure
      m_iUnion := fun s hs hd => by
        simp only [OuterMeasure.smul_apply, coe_toOuterMeasure, ENNReal.tsum_const_smul,
          measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_smul, μ.trimmed] }⟩
#align measure_theory.measure.has_smul MeasureTheory.Measure.instSMul

@[simp]
theorem smul_toOuterMeasure {_m : MeasurableSpace α} (c : R) (μ : Measure α) :
    (c • μ).toOuterMeasure = c • μ.toOuterMeasure :=
  rfl
#align measure_theory.measure.smul_to_outer_measure MeasureTheory.Measure.smul_toOuterMeasure

@[simp, norm_cast]
theorem coe_smul {_m : MeasurableSpace α} (c : R) (μ : Measure α) : ⇑(c • μ) = c • ⇑μ :=
  rfl
#align measure_theory.measure.coe_smul MeasureTheory.Measure.coe_smul

@[simp]
theorem smul_apply {_m : MeasurableSpace α} (c : R) (μ : Measure α) (s : Set α) :
    (c • μ) s = c • μ s :=
  rfl
#align measure_theory.measure.smul_apply MeasureTheory.Measure.smul_apply

instance instSMulCommClass [SMulCommClass R R' ℝ≥0∞] [MeasurableSpace α] :
    SMulCommClass R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_comm _ _ _⟩
#align measure_theory.measure.smul_comm_class MeasureTheory.Measure.instSMulCommClass

instance instIsScalarTower [SMul R R'] [IsScalarTower R R' ℝ≥0∞] [MeasurableSpace α] :
    IsScalarTower R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_assoc _ _ _⟩
#align measure_theory.measure.is_scalar_tower MeasureTheory.Measure.instIsScalarTower

instance instIsCentralScalar [SMul Rᵐᵒᵖ ℝ≥0∞] [IsCentralScalar R ℝ≥0∞] [MeasurableSpace α] :
    IsCentralScalar R (Measure α) :=
  ⟨fun _ _ => ext fun _ _ => op_smul_eq_smul _ _⟩
#align measure_theory.measure.is_central_scalar MeasureTheory.Measure.instIsCentralScalar

end SMul

instance instNoZeroSMulDivisors [Zero R] [SMulWithZero R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [NoZeroSMulDivisors R ℝ≥0∞] : NoZeroSMulDivisors R (Measure α) where
  eq_zero_or_eq_zero_of_smul_eq_zero h := by simpa [Ne, ext_iff', forall_or_left] using h

instance instMulAction [Monoid R] [MulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [MeasurableSpace α] : MulAction R (Measure α) :=
  Injective.mulAction _ toOuterMeasure_injective smul_toOuterMeasure
#align measure_theory.measure.mul_action MeasureTheory.Measure.instMulAction

instance instAddCommMonoid [MeasurableSpace α] : AddCommMonoid (Measure α) :=
  toOuterMeasure_injective.addCommMonoid toOuterMeasure zero_toOuterMeasure add_toOuterMeasure
    fun _ _ => smul_toOuterMeasure _ _
#align measure_theory.measure.add_comm_monoid MeasureTheory.Measure.instAddCommMonoid

/-- Coercion to function as an additive monoid homomorphism. -/
def coeAddHom {_ : MeasurableSpace α} : Measure α →+ Set α → ℝ≥0∞ where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add
#align measure_theory.measure.coe_add_hom MeasureTheory.Measure.coeAddHom

@[simp]
theorem coe_finset_sum {_m : MeasurableSpace α} (I : Finset ι) (μ : ι → Measure α) :
    ⇑(∑ i ∈ I, μ i) = ∑ i ∈ I, ⇑(μ i) := map_sum coeAddHom μ I
#align measure_theory.measure.coe_finset_sum MeasureTheory.Measure.coe_finset_sum

theorem finset_sum_apply {m : MeasurableSpace α} (I : Finset ι) (μ : ι → Measure α) (s : Set α) :
    (∑ i ∈ I, μ i) s = ∑ i ∈ I, μ i s := by rw [coe_finset_sum, Finset.sum_apply]
#align measure_theory.measure.finset_sum_apply MeasureTheory.Measure.finset_sum_apply

instance instDistribMulAction [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [MeasurableSpace α] : DistribMulAction R (Measure α) :=
  Injective.distribMulAction ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure
#align measure_theory.measure.distrib_mul_action MeasureTheory.Measure.instDistribMulAction

instance instModule [Semiring R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [MeasurableSpace α] :
    Module R (Measure α) :=
  Injective.module R ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure
#align measure_theory.measure.module MeasureTheory.Measure.instModule

@[simp]
theorem coe_nnreal_smul_apply {_m : MeasurableSpace α} (c : ℝ≥0) (μ : Measure α) (s : Set α) :
    (c • μ) s = c * μ s :=
  rfl
#align measure_theory.measure.coe_nnreal_smul_apply MeasureTheory.Measure.coe_nnreal_smul_apply

@[simp]
theorem nnreal_smul_coe_apply {_m : MeasurableSpace α} (c : ℝ≥0) (μ : Measure α) (s : Set α) :
    c • μ s = c * μ s := by
  rfl

theorem ae_smul_measure_iff {p : α → Prop} {c : ℝ≥0∞} (hc : c ≠ 0) :
    (∀ᵐ x ∂c • μ, p x) ↔ ∀ᵐ x ∂μ, p x := by
    simp only [ae_iff, Algebra.id.smul_eq_mul, smul_apply, or_iff_right_iff_imp, mul_eq_zero]
    simp only [IsEmpty.forall_iff, hc]
#align measure_theory.measure.ae_smul_measure_iff MeasureTheory.Measure.ae_smul_measure_iff

theorem measure_eq_left_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t)
    (h'' : (μ + ν) s = (μ + ν) t) : μ s = μ t := by
  refine le_antisymm (measure_mono h') ?_
  have : μ t + ν t ≤ μ s + ν t :=
    calc
      μ t + ν t = μ s + ν s := h''.symm
      _ ≤ μ s + ν t := by gcongr
  apply ENNReal.le_of_add_le_add_right _ this
  exact ne_top_of_le_ne_top h (le_add_left le_rfl)
#align measure_theory.measure.measure_eq_left_of_subset_of_measure_add_eq MeasureTheory.Measure.measure_eq_left_of_subset_of_measure_add_eq

theorem measure_eq_right_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t)
    (h'' : (μ + ν) s = (μ + ν) t) : ν s = ν t := by
  rw [add_comm] at h'' h
  exact measure_eq_left_of_subset_of_measure_add_eq h h' h''
#align measure_theory.measure.measure_eq_right_of_subset_of_measure_add_eq MeasureTheory.Measure.measure_eq_right_of_subset_of_measure_add_eq

theorem measure_toMeasurable_add_inter_left {s t : Set α} (hs : MeasurableSet s)
    (ht : (μ + ν) t ≠ ∞) : μ (toMeasurable (μ + ν) t ∩ s) = μ (t ∩ s) := by
  refine (measure_inter_eq_of_measure_eq hs ?_ (subset_toMeasurable _ _) ?_).symm
  · refine
      measure_eq_left_of_subset_of_measure_add_eq ?_ (subset_toMeasurable _ _)
        (measure_toMeasurable t).symm
    rwa [measure_toMeasurable t]
  · simp only [not_or, ENNReal.add_eq_top, Pi.add_apply, Ne, coe_add] at ht
    exact ht.1
#align measure_theory.measure.measure_to_measurable_add_inter_left MeasureTheory.Measure.measure_toMeasurable_add_inter_left

theorem measure_toMeasurable_add_inter_right {s t : Set α} (hs : MeasurableSet s)
    (ht : (μ + ν) t ≠ ∞) : ν (toMeasurable (μ + ν) t ∩ s) = ν (t ∩ s) := by
  rw [add_comm] at ht ⊢
  exact measure_toMeasurable_add_inter_left hs ht
#align measure_theory.measure.measure_to_measurable_add_inter_right MeasureTheory.Measure.measure_toMeasurable_add_inter_right

/-! ### The complete lattice of measures -/


/-- Measures are partially ordered. -/
instance instPartialOrder [MeasurableSpace α] : PartialOrder (Measure α) where
  le m₁ m₂ := ∀ s, m₁ s ≤ m₂ s
  le_refl m s := le_rfl
  le_trans m₁ m₂ m₃ h₁ h₂ s := le_trans (h₁ s) (h₂ s)
  le_antisymm m₁ m₂ h₁ h₂ := ext fun s _ => le_antisymm (h₁ s) (h₂ s)
#align measure_theory.measure.partial_order MeasureTheory.Measure.instPartialOrder

theorem toOuterMeasure_le : μ₁.toOuterMeasure ≤ μ₂.toOuterMeasure ↔ μ₁ ≤ μ₂ := .rfl
#align measure_theory.measure.to_outer_measure_le MeasureTheory.Measure.toOuterMeasure_le

theorem le_iff : μ₁ ≤ μ₂ ↔ ∀ s, MeasurableSet s → μ₁ s ≤ μ₂ s := outerMeasure_le_iff
#align measure_theory.measure.le_iff MeasureTheory.Measure.le_iff

theorem le_intro (h : ∀ s, MeasurableSet s → s.Nonempty → μ₁ s ≤ μ₂ s) : μ₁ ≤ μ₂ :=
  le_iff.2 fun s hs ↦ s.eq_empty_or_nonempty.elim (by rintro rfl; simp) (h s hs)

theorem le_iff' : μ₁ ≤ μ₂ ↔ ∀ s, μ₁ s ≤ μ₂ s := .rfl
#align measure_theory.measure.le_iff' MeasureTheory.Measure.le_iff'

theorem lt_iff : μ < ν ↔ μ ≤ ν ∧ ∃ s, MeasurableSet s ∧ μ s < ν s :=
  lt_iff_le_not_le.trans <|
    and_congr Iff.rfl <| by simp only [le_iff, not_forall, not_le, exists_prop]
#align measure_theory.measure.lt_iff MeasureTheory.Measure.lt_iff

theorem lt_iff' : μ < ν ↔ μ ≤ ν ∧ ∃ s, μ s < ν s :=
  lt_iff_le_not_le.trans <| and_congr Iff.rfl <| by simp only [le_iff', not_forall, not_le]
#align measure_theory.measure.lt_iff' MeasureTheory.Measure.lt_iff'

instance covariantAddLE [MeasurableSpace α] :
    CovariantClass (Measure α) (Measure α) (· + ·) (· ≤ ·) :=
  ⟨fun _ν _μ₁ _μ₂ hμ s => add_le_add_left (hμ s) _⟩
#align measure_theory.measure.covariant_add_le MeasureTheory.Measure.covariantAddLE

protected theorem le_add_left (h : μ ≤ ν) : μ ≤ ν' + ν := fun s => le_add_left (h s)
#align measure_theory.measure.le_add_left MeasureTheory.Measure.le_add_left

protected theorem le_add_right (h : μ ≤ ν) : μ ≤ ν + ν' := fun s => le_add_right (h s)
#align measure_theory.measure.le_add_right MeasureTheory.Measure.le_add_right

section sInf

variable {m : Set (Measure α)}

theorem sInf_caratheodory (s : Set α) (hs : MeasurableSet s) :
    MeasurableSet[(sInf (toOuterMeasure '' m)).caratheodory] s := by
  rw [OuterMeasure.sInf_eq_boundedBy_sInfGen]
  refine OuterMeasure.boundedBy_caratheodory fun t => ?_
  simp only [OuterMeasure.sInfGen, le_iInf_iff, forall_mem_image, measure_eq_iInf t,
    coe_toOuterMeasure]
  intro μ hμ u htu _hu
  have hm : ∀ {s t}, s ⊆ t → OuterMeasure.sInfGen (toOuterMeasure '' m) s ≤ μ t := by
    intro s t hst
    rw [OuterMeasure.sInfGen_def, iInf_image]
    exact iInf₂_le_of_le μ hμ <| measure_mono hst
  rw [← measure_inter_add_diff u hs]
  exact add_le_add (hm <| inter_subset_inter_left _ htu) (hm <| diff_subset_diff_left htu)
#align measure_theory.measure.Inf_caratheodory MeasureTheory.Measure.sInf_caratheodory

instance [MeasurableSpace α] : InfSet (Measure α) :=
  ⟨fun m => (sInf (toOuterMeasure '' m)).toMeasure <| sInf_caratheodory⟩

theorem sInf_apply (hs : MeasurableSet s) : sInf m s = sInf (toOuterMeasure '' m) s :=
  toMeasure_apply _ _ hs
#align measure_theory.measure.Inf_apply MeasureTheory.Measure.sInf_apply

private theorem measure_sInf_le (h : μ ∈ m) : sInf m ≤ μ :=
  have : sInf (toOuterMeasure '' m) ≤ μ.toOuterMeasure := sInf_le (mem_image_of_mem _ h)
  le_iff.2 fun s hs => by rw [sInf_apply hs]; exact this s

private theorem measure_le_sInf (h : ∀ μ' ∈ m, μ ≤ μ') : μ ≤ sInf m :=
  have : μ.toOuterMeasure ≤ sInf (toOuterMeasure '' m) :=
    le_sInf <| forall_mem_image.2 fun μ hμ ↦ toOuterMeasure_le.2 <| h _ hμ
  le_iff.2 fun s hs => by rw [sInf_apply hs]; exact this s

instance instCompleteSemilatticeInf [MeasurableSpace α] : CompleteSemilatticeInf (Measure α) :=
  { (by infer_instance : PartialOrder (Measure α)),
    (by infer_instance : InfSet (Measure α)) with
    sInf_le := fun _s _a => measure_sInf_le
    le_sInf := fun _s _a => measure_le_sInf }
#align measure_theory.measure.complete_semilattice_Inf MeasureTheory.Measure.instCompleteSemilatticeInf

instance instCompleteLattice [MeasurableSpace α] : CompleteLattice (Measure α) :=
  { completeLatticeOfCompleteSemilatticeInf (Measure α) with
    top :=
      { toOuterMeasure := ⊤,
        m_iUnion := by
          intro f _ _
          refine (measure_iUnion_le _).antisymm ?_
          if hne : (⋃ i, f i).Nonempty then
            rw [OuterMeasure.top_apply hne]
            exact le_top
          else
            simp_all [Set.not_nonempty_iff_eq_empty]
        trim_le := le_top },
    le_top := fun μ => toOuterMeasure_le.mp le_top
    bot := 0
    bot_le := fun _a _s => bot_le }
#align measure_theory.measure.complete_lattice MeasureTheory.Measure.instCompleteLattice

end sInf

@[simp]
theorem _root_.MeasureTheory.OuterMeasure.toMeasure_top :
    (⊤ : OuterMeasure α).toMeasure (by rw [OuterMeasure.top_caratheodory]; exact le_top) =
      (⊤ : Measure α) :=
  toOuterMeasure_toMeasure (μ := ⊤)
#align measure_theory.outer_measure.to_measure_top MeasureTheory.OuterMeasure.toMeasure_top

@[simp]
theorem toOuterMeasure_top [MeasurableSpace α] :
    (⊤ : Measure α).toOuterMeasure = (⊤ : OuterMeasure α) :=
  rfl
#align measure_theory.measure.to_outer_measure_top MeasureTheory.Measure.toOuterMeasure_top

@[simp]
theorem top_add : ⊤ + μ = ⊤ :=
  top_unique <| Measure.le_add_right le_rfl
#align measure_theory.measure.top_add MeasureTheory.Measure.top_add

@[simp]
theorem add_top : μ + ⊤ = ⊤ :=
  top_unique <| Measure.le_add_left le_rfl
#align measure_theory.measure.add_top MeasureTheory.Measure.add_top

protected theorem zero_le {_m0 : MeasurableSpace α} (μ : Measure α) : 0 ≤ μ :=
  bot_le
#align measure_theory.measure.zero_le MeasureTheory.Measure.zero_le

theorem nonpos_iff_eq_zero' : μ ≤ 0 ↔ μ = 0 :=
  μ.zero_le.le_iff_eq
#align measure_theory.measure.nonpos_iff_eq_zero' MeasureTheory.Measure.nonpos_iff_eq_zero'

@[simp]
theorem measure_univ_eq_zero : μ univ = 0 ↔ μ = 0 :=
  ⟨fun h => bot_unique fun s => (h ▸ measure_mono (subset_univ s) : μ s ≤ 0), fun h =>
    h.symm ▸ rfl⟩
#align measure_theory.measure.measure_univ_eq_zero MeasureTheory.Measure.measure_univ_eq_zero

theorem measure_univ_ne_zero : μ univ ≠ 0 ↔ μ ≠ 0 :=
  measure_univ_eq_zero.not
#align measure_theory.measure.measure_univ_ne_zero MeasureTheory.Measure.measure_univ_ne_zero

instance [NeZero μ] : NeZero (μ univ) := ⟨measure_univ_ne_zero.2 <| NeZero.ne μ⟩

@[simp]
theorem measure_univ_pos : 0 < μ univ ↔ μ ≠ 0 :=
  pos_iff_ne_zero.trans measure_univ_ne_zero
#align measure_theory.measure.measure_univ_pos MeasureTheory.Measure.measure_univ_pos

/-! ### Pushforward and pullback -/


/-- Lift a linear map between `OuterMeasure` spaces such that for each measure `μ` every measurable
set is caratheodory-measurable w.r.t. `f μ` to a linear map between `Measure` spaces. -/
def liftLinear {m0 : MeasurableSpace α} (f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β)
    (hf : ∀ μ : Measure α, ‹_› ≤ (f μ.toOuterMeasure).caratheodory) :
    Measure α →ₗ[ℝ≥0∞] Measure β where
  toFun μ := (f μ.toOuterMeasure).toMeasure (hf μ)
  map_add' μ₁ μ₂ := ext fun s hs => by
    simp only [map_add, coe_add, Pi.add_apply, toMeasure_apply, add_toOuterMeasure,
      OuterMeasure.coe_add, hs]
  map_smul' c μ := ext fun s hs => by
    simp only [LinearMap.map_smulₛₗ, coe_smul, Pi.smul_apply,
      toMeasure_apply, smul_toOuterMeasure (R := ℝ≥0∞), OuterMeasure.coe_smul (R := ℝ≥0∞),
      smul_apply, hs]
#align measure_theory.measure.lift_linear MeasureTheory.Measure.liftLinear

lemma liftLinear_apply₀ {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) {s : Set β}
    (hs : NullMeasurableSet s (liftLinear f hf μ)) : liftLinear f hf μ s = f μ.toOuterMeasure s :=
  toMeasure_apply₀ _ (hf μ) hs

@[simp]
theorem liftLinear_apply {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) {s : Set β}
    (hs : MeasurableSet s) : liftLinear f hf μ s = f μ.toOuterMeasure s :=
  toMeasure_apply _ (hf μ) hs
#align measure_theory.measure.lift_linear_apply MeasureTheory.Measure.liftLinear_apply

theorem le_liftLinear_apply {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) (s : Set β) :
    f μ.toOuterMeasure s ≤ liftLinear f hf μ s :=
  le_toMeasure_apply _ (hf μ) s
#align measure_theory.measure.le_lift_linear_apply MeasureTheory.Measure.le_liftLinear_apply

/-- The pushforward of a measure as a linear map. It is defined to be `0` if `f` is not
a measurable function. -/
def mapₗ [MeasurableSpace α] (f : α → β) : Measure α →ₗ[ℝ≥0∞] Measure β :=
  if hf : Measurable f then
    liftLinear (OuterMeasure.map f) fun μ _s hs t =>
      le_toOuterMeasure_caratheodory μ _ (hf hs) (f ⁻¹' t)
  else 0
#align measure_theory.measure.mapₗ MeasureTheory.Measure.mapₗ

theorem mapₗ_congr {f g : α → β} (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    mapₗ f μ = mapₗ g μ := by
  ext1 s hs
  simpa only [mapₗ, hf, hg, hs, dif_pos, liftLinear_apply, OuterMeasure.map_apply]
    using measure_congr (h.preimage s)
#align measure_theory.measure.mapₗ_congr MeasureTheory.Measure.mapₗ_congr

/-- The pushforward of a measure. It is defined to be `0` if `f` is not an almost everywhere
measurable function. -/
irreducible_def map [MeasurableSpace α] (f : α → β) (μ : Measure α) : Measure β :=
  if hf : AEMeasurable f μ then mapₗ (hf.mk f) μ else 0
#align measure_theory.measure.map MeasureTheory.Measure.map

theorem mapₗ_mk_apply_of_aemeasurable {f : α → β} (hf : AEMeasurable f μ) :
    mapₗ (hf.mk f) μ = map f μ := by simp [map, hf]
#align measure_theory.measure.mapₗ_mk_apply_of_ae_measurable MeasureTheory.Measure.mapₗ_mk_apply_of_aemeasurable

theorem mapₗ_apply_of_measurable {f : α → β} (hf : Measurable f) (μ : Measure α) :
    mapₗ f μ = map f μ := by
  simp only [← mapₗ_mk_apply_of_aemeasurable hf.aemeasurable]
  exact mapₗ_congr hf hf.aemeasurable.measurable_mk hf.aemeasurable.ae_eq_mk
#align measure_theory.measure.mapₗ_apply_of_measurable MeasureTheory.Measure.mapₗ_apply_of_measurable

@[simp]
theorem map_add (μ ν : Measure α) {f : α → β} (hf : Measurable f) :
    (μ + ν).map f = μ.map f + ν.map f := by simp [← mapₗ_apply_of_measurable hf]
#align measure_theory.measure.map_add MeasureTheory.Measure.map_add

@[simp]
theorem map_zero (f : α → β) : (0 : Measure α).map f = 0 := by
  by_cases hf : AEMeasurable f (0 : Measure α) <;> simp [map, hf]
#align measure_theory.measure.map_zero MeasureTheory.Measure.map_zero

@[simp]
theorem map_of_not_aemeasurable {f : α → β} {μ : Measure α} (hf : ¬AEMeasurable f μ) :
    μ.map f = 0 := by simp [map, hf]
#align measure_theory.measure.map_of_not_ae_measurable MeasureTheory.Measure.map_of_not_aemeasurable

theorem map_congr {f g : α → β} (h : f =ᵐ[μ] g) : Measure.map f μ = Measure.map g μ := by
  by_cases hf : AEMeasurable f μ
  · have hg : AEMeasurable g μ := hf.congr h
    simp only [← mapₗ_mk_apply_of_aemeasurable hf, ← mapₗ_mk_apply_of_aemeasurable hg]
    exact
      mapₗ_congr hf.measurable_mk hg.measurable_mk (hf.ae_eq_mk.symm.trans (h.trans hg.ae_eq_mk))
  · have hg : ¬AEMeasurable g μ := by simpa [← aemeasurable_congr h] using hf
    simp [map_of_not_aemeasurable, hf, hg]
#align measure_theory.measure.map_congr MeasureTheory.Measure.map_congr

@[simp]
protected theorem map_smul (c : ℝ≥0∞) (μ : Measure α) (f : α → β) :
    (c • μ).map f = c • μ.map f := by
  rcases eq_or_ne c 0 with (rfl | hc); · simp
  by_cases hf : AEMeasurable f μ
  · have hfc : AEMeasurable f (c • μ) :=
      ⟨hf.mk f, hf.measurable_mk, (ae_smul_measure_iff hc).2 hf.ae_eq_mk⟩
    simp only [← mapₗ_mk_apply_of_aemeasurable hf, ← mapₗ_mk_apply_of_aemeasurable hfc,
      LinearMap.map_smulₛₗ, RingHom.id_apply]
    congr 1
    apply mapₗ_congr hfc.measurable_mk hf.measurable_mk
    exact EventuallyEq.trans ((ae_smul_measure_iff hc).1 hfc.ae_eq_mk.symm) hf.ae_eq_mk
  · have hfc : ¬AEMeasurable f (c • μ) := by
      intro hfc
      exact hf ⟨hfc.mk f, hfc.measurable_mk, (ae_smul_measure_iff hc).1 hfc.ae_eq_mk⟩
    simp [map_of_not_aemeasurable hf, map_of_not_aemeasurable hfc]
#align measure_theory.measure.map_smul MeasureTheory.Measure.map_smul

@[simp]
protected theorem map_smul_nnreal (c : ℝ≥0) (μ : Measure α) (f : α → β) :
    (c • μ).map f = c • μ.map f :=
  μ.map_smul (c : ℝ≥0∞) f
#align measure_theory.measure.map_smul_nnreal MeasureTheory.Measure.map_smul_nnreal

variable {f : α → β}

lemma map_apply₀ {f : α → β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : NullMeasurableSet s (map f μ)) : μ.map f s = μ (f ⁻¹' s) := by
  rw [map, dif_pos hf, mapₗ, dif_pos hf.measurable_mk] at hs ⊢
  rw [liftLinear_apply₀ _ hs, measure_congr (hf.ae_eq_mk.preimage s)]
  rfl

/-- We can evaluate the pushforward on measurable sets. For non-measurable sets, see
  `MeasureTheory.Measure.le_map_apply` and `MeasurableEquiv.map_apply`. -/
@[simp]
theorem map_apply_of_aemeasurable (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :
    μ.map f s = μ (f ⁻¹' s) := map_apply₀ hf hs.nullMeasurableSet
#align measure_theory.measure.map_apply_of_ae_measurable MeasureTheory.Measure.map_apply_of_aemeasurable

@[simp]
theorem map_apply (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    μ.map f s = μ (f ⁻¹' s) :=
  map_apply_of_aemeasurable hf.aemeasurable hs
#align measure_theory.measure.map_apply MeasureTheory.Measure.map_apply

theorem map_toOuterMeasure (hf : AEMeasurable f μ) :
    (μ.map f).toOuterMeasure = (OuterMeasure.map f μ.toOuterMeasure).trim := by
  rw [← trimmed, OuterMeasure.trim_eq_trim_iff]
  intro s hs
  simp [hf, hs]
#align measure_theory.measure.map_to_outer_measure MeasureTheory.Measure.map_toOuterMeasure

@[simp] lemma map_eq_zero_iff (hf : AEMeasurable f μ) : μ.map f = 0 ↔ μ = 0 := by
  simp_rw [← measure_univ_eq_zero, map_apply_of_aemeasurable hf .univ, preimage_univ]

@[simp] lemma mapₗ_eq_zero_iff (hf : Measurable f) : Measure.mapₗ f μ = 0 ↔ μ = 0 := by
  rw [mapₗ_apply_of_measurable hf, map_eq_zero_iff hf.aemeasurable]

lemma map_ne_zero_iff (hf : AEMeasurable f μ) : μ.map f ≠ 0 ↔ μ ≠ 0 := (map_eq_zero_iff hf).not
lemma mapₗ_ne_zero_iff (hf : Measurable f) : Measure.mapₗ f μ ≠ 0 ↔ μ ≠ 0 :=
  (mapₗ_eq_zero_iff hf).not

@[simp]
theorem map_id : map id μ = μ :=
  ext fun _ => map_apply measurable_id
#align measure_theory.measure.map_id MeasureTheory.Measure.map_id

@[simp]
theorem map_id' : map (fun x => x) μ = μ :=
  map_id
#align measure_theory.measure.map_id' MeasureTheory.Measure.map_id'

theorem map_map {g : β → γ} {f : α → β} (hg : Measurable g) (hf : Measurable f) :
    (μ.map f).map g = μ.map (g ∘ f) :=
  ext fun s hs => by simp [hf, hg, hs, hg hs, hg.comp hf, ← preimage_comp]
#align measure_theory.measure.map_map MeasureTheory.Measure.map_map

@[mono]
theorem map_mono {f : α → β} (h : μ ≤ ν) (hf : Measurable f) : μ.map f ≤ ν.map f :=
  le_iff.2 fun s hs ↦ by simp [hf.aemeasurable, hs, h _]
#align measure_theory.measure.map_mono MeasureTheory.Measure.map_mono

/-- Even if `s` is not measurable, we can bound `map f μ s` from below.
  See also `MeasurableEquiv.map_apply`. -/
theorem le_map_apply {f : α → β} (hf : AEMeasurable f μ) (s : Set β) : μ (f ⁻¹' s) ≤ μ.map f s :=
  calc
    μ (f ⁻¹' s) ≤ μ (f ⁻¹' toMeasurable (μ.map f) s) := by gcongr; apply subset_toMeasurable
    _ = μ.map f (toMeasurable (μ.map f) s) :=
      (map_apply_of_aemeasurable hf <| measurableSet_toMeasurable _ _).symm
    _ = μ.map f s := measure_toMeasurable _
#align measure_theory.measure.le_map_apply MeasureTheory.Measure.le_map_apply

theorem le_map_apply_image {f : α → β} (hf : AEMeasurable f μ) (s : Set α) :
    μ s ≤ μ.map f (f '' s) :=
  (measure_mono (subset_preimage_image f s)).trans (le_map_apply hf _)

/-- Even if `s` is not measurable, `map f μ s = 0` implies that `μ (f ⁻¹' s) = 0`. -/
theorem preimage_null_of_map_null {f : α → β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : μ.map f s = 0) : μ (f ⁻¹' s) = 0 :=
  nonpos_iff_eq_zero.mp <| (le_map_apply hf s).trans_eq hs
#align measure_theory.measure.preimage_null_of_map_null MeasureTheory.Measure.preimage_null_of_map_null

theorem tendsto_ae_map {f : α → β} (hf : AEMeasurable f μ) : Tendsto f (ae μ) (ae (μ.map f)) :=
  fun _ hs => preimage_null_of_map_null hf hs
#align measure_theory.measure.tendsto_ae_map MeasureTheory.Measure.tendsto_ae_map

/-- Pullback of a `Measure` as a linear map. If `f` sends each measurable set to a measurable
set, then for each measurable set `s` we have `comapₗ f μ s = μ (f '' s)`.

If the linearity is not needed, please use `comap` instead, which works for a larger class of
functions. -/
def comapₗ [MeasurableSpace α] (f : α → β) : Measure β →ₗ[ℝ≥0∞] Measure α :=
  if hf : Injective f ∧ ∀ s, MeasurableSet s → MeasurableSet (f '' s) then
    liftLinear (OuterMeasure.comap f) fun μ s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_diff hf.1]
      apply le_toOuterMeasure_caratheodory
      exact hf.2 s hs
  else 0
#align measure_theory.measure.comapₗ MeasureTheory.Measure.comapₗ

theorem comapₗ_apply {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β)
    (hfi : Injective f) (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β)
    (hs : MeasurableSet s) : comapₗ f μ s = μ (f '' s) := by
  rw [comapₗ, dif_pos, liftLinear_apply _ hs, OuterMeasure.comap_apply, coe_toOuterMeasure]
  exact ⟨hfi, hf⟩
#align measure_theory.measure.comapₗ_apply MeasureTheory.Measure.comapₗ_apply

/-- Pullback of a `Measure`. If `f` sends each measurable set to a null-measurable set,
then for each measurable set `s` we have `comap f μ s = μ (f '' s)`. -/
def comap [MeasurableSpace α] (f : α → β) (μ : Measure β) : Measure α :=
  if hf : Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ then
    (OuterMeasure.comap f μ.toOuterMeasure).toMeasure fun s hs t => by
      simp only [OuterMeasure.comap_apply, image_inter hf.1, image_diff hf.1]
      exact (measure_inter_add_diff₀ _ (hf.2 s hs)).symm
  else 0
#align measure_theory.measure.comap MeasureTheory.Measure.comap

theorem comap_apply₀ [MeasurableSpace α] (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    (hs : NullMeasurableSet s (comap f μ)) : comap f μ s = μ (f '' s) := by
  rw [comap, dif_pos (And.intro hfi hf)] at hs ⊢
  rw [toMeasure_apply₀ _ _ hs, OuterMeasure.comap_apply, coe_toOuterMeasure]
#align measure_theory.measure.comap_apply₀ MeasureTheory.Measure.comap_apply₀

theorem le_comap_apply {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β) (μ : Measure β)
    (hfi : Injective f) (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ) (s : Set α) :
    μ (f '' s) ≤ comap f μ s := by
  rw [comap, dif_pos (And.intro hfi hf)]
  exact le_toMeasure_apply _ _ _
#align measure_theory.measure.le_comap_apply MeasureTheory.Measure.le_comap_apply

theorem comap_apply {β} [MeasurableSpace α] {_mβ : MeasurableSpace β} (f : α → β)
    (hfi : Injective f) (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β)
    (hs : MeasurableSet s) : comap f μ s = μ (f '' s) :=
  comap_apply₀ f μ hfi (fun s hs => (hf s hs).nullMeasurableSet) hs.nullMeasurableSet
#align measure_theory.measure.comap_apply MeasureTheory.Measure.comap_apply

theorem comapₗ_eq_comap {β} [MeasurableSpace α] {_mβ : MeasurableSpace β} (f : α → β)
    (hfi : Injective f) (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β)
    (hs : MeasurableSet s) : comapₗ f μ s = comap f μ s :=
  (comapₗ_apply f hfi hf μ hs).trans (comap_apply f hfi hf μ hs).symm
#align measure_theory.measure.comapₗ_eq_comap MeasureTheory.Measure.comapₗ_eq_comap

theorem measure_image_eq_zero_of_comap_eq_zero {β} [MeasurableSpace α] {_mβ : MeasurableSpace β}
    (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ) {s : Set α} (hs : comap f μ s = 0) :
    μ (f '' s) = 0 :=
  le_antisymm ((le_comap_apply f μ hfi hf s).trans hs.le) (zero_le _)
#align measure_theory.measure.measure_image_eq_zero_of_comap_eq_zero MeasureTheory.Measure.measure_image_eq_zero_of_comap_eq_zero

theorem ae_eq_image_of_ae_eq_comap {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β)
    (μ : Measure β) (hfi : Injective f) (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    {s t : Set α} (hst : s =ᵐ[comap f μ] t) : f '' s =ᵐ[μ] f '' t := by
  rw [EventuallyEq, ae_iff] at hst ⊢
  have h_eq_α : { a : α | ¬s a = t a } = s \ t ∪ t \ s := by
    ext1 x
    simp only [eq_iff_iff, mem_setOf_eq, mem_union, mem_diff]
    tauto
  have h_eq_β : { a : β | ¬(f '' s) a = (f '' t) a } = f '' s \ f '' t ∪ f '' t \ f '' s := by
    ext1 x
    simp only [eq_iff_iff, mem_setOf_eq, mem_union, mem_diff]
    tauto
  rw [← Set.image_diff hfi, ← Set.image_diff hfi, ← Set.image_union] at h_eq_β
  rw [h_eq_β]
  rw [h_eq_α] at hst
  exact measure_image_eq_zero_of_comap_eq_zero f μ hfi hf hst
#align measure_theory.measure.ae_eq_image_of_ae_eq_comap MeasureTheory.Measure.ae_eq_image_of_ae_eq_comap

theorem NullMeasurableSet.image {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β)
    (μ : Measure β) (hfi : Injective f) (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    {s : Set α} (hs : NullMeasurableSet s (μ.comap f)) : NullMeasurableSet (f '' s) μ := by
  refine ⟨toMeasurable μ (f '' toMeasurable (μ.comap f) s), measurableSet_toMeasurable _ _, ?_⟩
  refine EventuallyEq.trans ?_ (NullMeasurableSet.toMeasurable_ae_eq ?_).symm
  swap
  · exact hf _ (measurableSet_toMeasurable _ _)
  have h : toMeasurable (comap f μ) s =ᵐ[comap f μ] s :=
    NullMeasurableSet.toMeasurable_ae_eq hs
  exact ae_eq_image_of_ae_eq_comap f μ hfi hf h.symm
#align measure_theory.measure.null_measurable_set.image MeasureTheory.Measure.NullMeasurableSet.image

theorem comap_preimage {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β) (μ : Measure β)
    {s : Set β} (hf : Injective f) (hf' : Measurable f)
    (h : ∀ t, MeasurableSet t → NullMeasurableSet (f '' t) μ) (hs : MeasurableSet s) :
    μ.comap f (f ⁻¹' s) = μ (s ∩ range f) := by
  rw [comap_apply₀ _ _ hf h (hf' hs).nullMeasurableSet, image_preimage_eq_inter_range]
#align measure_theory.measure.comap_preimage MeasureTheory.Measure.comap_preimage

section Sum

/-- Sum of an indexed family of measures. -/
noncomputable def sum (f : ι → Measure α) : Measure α :=
  (OuterMeasure.sum fun i => (f i).toOuterMeasure).toMeasure <|
    le_trans (le_iInf fun _ => le_toOuterMeasure_caratheodory _)
      (OuterMeasure.le_sum_caratheodory _)
#align measure_theory.measure.sum MeasureTheory.Measure.sum

theorem le_sum_apply (f : ι → Measure α) (s : Set α) : ∑' i, f i s ≤ sum f s :=
  le_toMeasure_apply _ _ _
#align measure_theory.measure.le_sum_apply MeasureTheory.Measure.le_sum_apply

@[simp]
theorem sum_apply (f : ι → Measure α) {s : Set α} (hs : MeasurableSet s) :
    sum f s = ∑' i, f i s :=
  toMeasure_apply _ _ hs
#align measure_theory.measure.sum_apply MeasureTheory.Measure.sum_apply

theorem sum_apply₀ (f : ι → Measure α) {s : Set α} (hs : NullMeasurableSet s (sum f)) :
    sum f s = ∑' i, f i s := by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases hs.exists_measurable_subset_ae_eq  with ⟨t, ts, t_meas, ht⟩
  calc
  sum f s = sum f t := measure_congr ht.symm
  _ = ∑' i, f i t := sum_apply _ t_meas
  _ ≤ ∑' i, f i s := ENNReal.tsum_le_tsum fun i ↦ measure_mono ts

/-! For the next theorem, the countability assumption is necessary. For a counterexample, consider
an uncountable space, with a distinguished point `x₀`, and the sigma-algebra made of countable sets
not containing `x₀`, and their complements. All points but `x₀` are measurable.
Consider the sum of the Dirac masses at points different from `x₀`, and `s = x₀`. For any Dirac mass
`δ_x`, we have `δ_x (x₀) = 0`, so `∑' x, δ_x (x₀) = 0`. On the other hand, the measure `sum δ_x`
gives mass one to each point different from `x₀`, so it gives infinite mass to any measurable set
containing `x₀` (as such a set is uncountable), and by outer regularity one get `sum δ_x {x₀} = ∞`.
-/
theorem sum_apply_of_countable [Countable ι] (f : ι → Measure α) (s : Set α) :
    sum f s = ∑' i, f i s := by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases exists_measurable_superset_forall_eq f s with ⟨t, hst, htm, ht⟩
  calc
  sum f s ≤ sum f t := measure_mono hst
  _ = ∑' i, f i t := sum_apply _ htm
  _ = ∑' i, f i s := by simp [ht]

theorem le_sum (μ : ι → Measure α) (i : ι) : μ i ≤ sum μ :=
  le_iff.2 fun s hs ↦ by simpa only [sum_apply μ hs] using ENNReal.le_tsum i
#align measure_theory.measure.le_sum MeasureTheory.Measure.le_sum

@[simp]
theorem sum_apply_eq_zero [Countable ι] {μ : ι → Measure α} {s : Set α} :
    sum μ s = 0 ↔ ∀ i, μ i s = 0 := by
  simp [sum_apply_of_countable]
#align measure_theory.measure.sum_apply_eq_zero MeasureTheory.Measure.sum_apply_eq_zero

theorem sum_apply_eq_zero' {μ : ι → Measure α} {s : Set α} (hs : MeasurableSet s) :
    sum μ s = 0 ↔ ∀ i, μ i s = 0 := by simp [hs]
#align measure_theory.measure.sum_apply_eq_zero' MeasureTheory.Measure.sum_apply_eq_zero'

@[simp]
lemma sum_zero : Measure.sum (fun (_ : ι) ↦ (0 : Measure α)) = 0 := by
  ext s hs
  simp [Measure.sum_apply _ hs]

theorem sum_sum {ι' : Type*} (μ : ι → ι' → Measure α) :
    (sum fun n => sum (μ n)) = sum (fun (p : ι × ι') ↦ μ p.1 p.2) := by
  ext1 s hs
  simp [sum_apply _ hs, ENNReal.tsum_prod']

theorem sum_comm {ι' : Type*} (μ : ι → ι' → Measure α) :
    (sum fun n => sum (μ n)) = sum fun m => sum fun n => μ n m := by
  ext1 s hs
  simp_rw [sum_apply _ hs]
  rw [ENNReal.tsum_comm]
#align measure_theory.measure.sum_comm MeasureTheory.Measure.sum_comm

theorem ae_sum_iff [Countable ι] {μ : ι → Measure α} {p : α → Prop} :
    (∀ᵐ x ∂sum μ, p x) ↔ ∀ i, ∀ᵐ x ∂μ i, p x :=
  sum_apply_eq_zero
#align measure_theory.measure.ae_sum_iff MeasureTheory.Measure.ae_sum_iff

theorem ae_sum_iff' {μ : ι → Measure α} {p : α → Prop} (h : MeasurableSet { x | p x }) :
    (∀ᵐ x ∂sum μ, p x) ↔ ∀ i, ∀ᵐ x ∂μ i, p x :=
  sum_apply_eq_zero' h.compl
#align measure_theory.measure.ae_sum_iff' MeasureTheory.Measure.ae_sum_iff'

@[simp]
theorem sum_fintype [Fintype ι] (μ : ι → Measure α) : sum μ = ∑ i, μ i := by
  ext1 s hs
  simp only [sum_apply, finset_sum_apply, hs, tsum_fintype]
#align measure_theory.measure.sum_fintype MeasureTheory.Measure.sum_fintype

theorem sum_coe_finset (s : Finset ι) (μ : ι → Measure α) :
    (sum fun i : s => μ i) = ∑ i ∈ s, μ i := by rw [sum_fintype, Finset.sum_coe_sort s μ]
#align measure_theory.measure.sum_coe_finset MeasureTheory.Measure.sum_coe_finset

@[simp]
theorem ae_sum_eq [Countable ι] (μ : ι → Measure α) : ae (sum μ) = ⨆ i, ae (μ i) :=
  Filter.ext fun _ => ae_sum_iff.trans mem_iSup.symm
#align measure_theory.measure.ae_sum_eq MeasureTheory.Measure.ae_sum_eq

theorem sum_bool (f : Bool → Measure α) : sum f = f true + f false := by
  rw [sum_fintype, Fintype.sum_bool]
#align measure_theory.measure.sum_bool MeasureTheory.Measure.sum_bool

theorem sum_cond (μ ν : Measure α) : (sum fun b => cond b μ ν) = μ + ν :=
  sum_bool _
#align measure_theory.measure.sum_cond MeasureTheory.Measure.sum_cond

@[simp]
theorem sum_of_empty [IsEmpty ι] (μ : ι → Measure α) : sum μ = 0 := by
  rw [← measure_univ_eq_zero, sum_apply _ MeasurableSet.univ, tsum_empty]
#align measure_theory.measure.sum_of_empty MeasureTheory.Measure.sum_of_empty

theorem sum_add_sum_compl (s : Set ι) (μ : ι → Measure α) :
    ((sum fun i : s => μ i) + sum fun i : ↥sᶜ => μ i) = sum μ := by
  ext1 t ht
  simp only [add_apply, sum_apply _ ht]
  exact tsum_add_tsum_compl (f := fun i => μ i t) ENNReal.summable ENNReal.summable
#align measure_theory.measure.sum_add_sum_compl MeasureTheory.Measure.sum_add_sum_compl

theorem sum_congr {μ ν : ℕ → Measure α} (h : ∀ n, μ n = ν n) : sum μ = sum ν :=
  congr_arg sum (funext h)
#align measure_theory.measure.sum_congr MeasureTheory.Measure.sum_congr

theorem sum_add_sum {ι : Type*} (μ ν : ι → Measure α) : sum μ + sum ν = sum fun n => μ n + ν n := by
  ext1 s hs
  simp only [add_apply, sum_apply _ hs, Pi.add_apply, coe_add,
    tsum_add ENNReal.summable ENNReal.summable]
#align measure_theory.measure.sum_add_sum MeasureTheory.Measure.sum_add_sum

@[simp] lemma sum_comp_equiv {ι ι' : Type*} (e : ι' ≃ ι) (m : ι → Measure α) :
    sum (m ∘ e) = sum m := by
  ext s hs
  simpa [hs, sum_apply] using e.tsum_eq (fun n ↦ m n s)

@[simp] lemma sum_extend_zero {ι ι' : Type*} {f : ι → ι'} (hf : Injective f) (m : ι → Measure α) :
    sum (Function.extend f m 0) = sum m := by
  ext s hs
  simp [*, Function.apply_extend (fun μ : Measure α ↦ μ s)]
end Sum

/-! ### Absolute continuity -/

/-- We say that `μ` is absolutely continuous with respect to `ν`, or that `μ` is dominated by `ν`,
  if `ν(A) = 0` implies that `μ(A) = 0`. -/
def AbsolutelyContinuous {_m0 : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  ∀ ⦃s : Set α⦄, ν s = 0 → μ s = 0
#align measure_theory.measure.absolutely_continuous MeasureTheory.Measure.AbsolutelyContinuous

@[inherit_doc MeasureTheory.Measure.AbsolutelyContinuous]
scoped[MeasureTheory] infixl:50 " ≪ " => MeasureTheory.Measure.AbsolutelyContinuous

theorem absolutelyContinuous_of_le (h : μ ≤ ν) : μ ≪ ν := fun s hs =>
  nonpos_iff_eq_zero.1 <| hs ▸ le_iff'.1 h s
#align measure_theory.measure.absolutely_continuous_of_le MeasureTheory.Measure.absolutelyContinuous_of_le

alias _root_.LE.le.absolutelyContinuous := absolutelyContinuous_of_le
#align has_le.le.absolutely_continuous LE.le.absolutelyContinuous

theorem absolutelyContinuous_of_eq (h : μ = ν) : μ ≪ ν :=
  h.le.absolutelyContinuous
#align measure_theory.measure.absolutely_continuous_of_eq MeasureTheory.Measure.absolutelyContinuous_of_eq

alias _root_.Eq.absolutelyContinuous := absolutelyContinuous_of_eq
#align eq.absolutely_continuous Eq.absolutelyContinuous

namespace AbsolutelyContinuous

theorem mk (h : ∀ ⦃s : Set α⦄, MeasurableSet s → ν s = 0 → μ s = 0) : μ ≪ ν := by
  intro s hs
  rcases exists_measurable_superset_of_null hs with ⟨t, h1t, h2t, h3t⟩
  exact measure_mono_null h1t (h h2t h3t)
#align measure_theory.measure.absolutely_continuous.mk MeasureTheory.Measure.AbsolutelyContinuous.mk

@[refl]
protected theorem refl {_m0 : MeasurableSpace α} (μ : Measure α) : μ ≪ μ :=
  rfl.absolutelyContinuous
#align measure_theory.measure.absolutely_continuous.refl MeasureTheory.Measure.AbsolutelyContinuous.refl

protected theorem rfl : μ ≪ μ := fun _s hs => hs
#align measure_theory.measure.absolutely_continuous.rfl MeasureTheory.Measure.AbsolutelyContinuous.rfl

instance instIsRefl [MeasurableSpace α] : IsRefl (Measure α) (· ≪ ·) :=
  ⟨fun _ => AbsolutelyContinuous.rfl⟩
#align measure_theory.measure.absolutely_continuous.is_refl MeasureTheory.Measure.AbsolutelyContinuous.instIsRefl

@[simp]
protected lemma zero (μ : Measure α) : 0 ≪ μ := fun s _ ↦ by simp

@[trans]
protected theorem trans (h1 : μ₁ ≪ μ₂) (h2 : μ₂ ≪ μ₃) : μ₁ ≪ μ₃ := fun _s hs => h1 <| h2 hs
#align measure_theory.measure.absolutely_continuous.trans MeasureTheory.Measure.AbsolutelyContinuous.trans

@[mono]
protected theorem map (h : μ ≪ ν) {f : α → β} (hf : Measurable f) : μ.map f ≪ ν.map f :=
  AbsolutelyContinuous.mk fun s hs => by simpa [hf, hs] using @h _
#align measure_theory.measure.absolutely_continuous.map MeasureTheory.Measure.AbsolutelyContinuous.map

protected theorem smul [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : μ ≪ ν) (c : R) : c • μ ≪ ν := fun s hνs => by
  simp only [h hνs, smul_eq_mul, smul_apply, smul_zero]
#align measure_theory.measure.absolutely_continuous.smul MeasureTheory.Measure.AbsolutelyContinuous.smul

protected lemma add (h1 : μ₁ ≪ ν) (h2 : μ₂ ≪ ν') : μ₁ + μ₂ ≪ ν + ν' := by
  intro s hs
  simp only [coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact ⟨h1 hs.1, h2 hs.2⟩

lemma add_left_iff {μ₁ μ₂ ν : Measure α} :
    μ₁ + μ₂ ≪ ν ↔ μ₁ ≪ ν ∧ μ₂ ≪ ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ (h.1.add h.2).trans ?_⟩
  · have : ∀ s, ν s = 0 → μ₁ s = 0 ∧ μ₂ s = 0 := by intro s hs0; simpa using h hs0
    exact ⟨fun s hs0 ↦ (this s hs0).1, fun s hs0 ↦ (this s hs0).2⟩
  · have : ν + ν = 2 • ν := by ext; simp [two_mul]
    rw [this]
    exact AbsolutelyContinuous.rfl.smul 2

lemma add_right (h1 : μ ≪ ν) (ν' : Measure α) : μ ≪ ν + ν' := by
  intro s hs
  simp only [coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact h1 hs.1

end AbsolutelyContinuous

@[simp]
lemma absolutelyContinuous_zero_iff : μ ≪ 0 ↔ μ = 0 :=
  ⟨fun h ↦ measure_univ_eq_zero.mp (h rfl), fun h ↦ h.symm ▸ AbsolutelyContinuous.zero _⟩

alias absolutelyContinuous_refl := AbsolutelyContinuous.refl
alias absolutelyContinuous_rfl := AbsolutelyContinuous.rfl

lemma absolutelyContinuous_sum_left {μs : ι → Measure α} (hμs : ∀ i, μs i ≪ ν) :
    Measure.sum μs ≪ ν :=
  AbsolutelyContinuous.mk fun s hs hs0 ↦ by simp [sum_apply _ hs, fun i ↦ hμs i hs0]

lemma absolutelyContinuous_sum_right {μs : ι → Measure α} (i : ι) (hνμ : ν ≪ μs i) :
    ν ≪ Measure.sum μs := by
  refine AbsolutelyContinuous.mk fun s hs hs0 ↦ ?_
  simp only [sum_apply _ hs, ENNReal.tsum_eq_zero] at hs0
  exact hνμ (hs0 i)

theorem absolutelyContinuous_of_le_smul {μ' : Measure α} {c : ℝ≥0∞} (hμ'_le : μ' ≤ c • μ) :
    μ' ≪ μ :=
  (Measure.absolutelyContinuous_of_le hμ'_le).trans (Measure.AbsolutelyContinuous.rfl.smul c)
#align measure_theory.measure.absolutely_continuous_of_le_smul MeasureTheory.Measure.absolutelyContinuous_of_le_smul

lemma smul_absolutelyContinuous {c : ℝ≥0∞} : c • μ ≪ μ := absolutelyContinuous_of_le_smul le_rfl

lemma absolutelyContinuous_smul {c : ℝ≥0∞} (hc : c ≠ 0) : μ ≪ c • μ := by
  simp [AbsolutelyContinuous, hc]

theorem ae_le_iff_absolutelyContinuous : ae μ ≤ ae ν ↔ μ ≪ ν :=
  ⟨fun h s => by
    rw [measure_zero_iff_ae_nmem, measure_zero_iff_ae_nmem]
    exact fun hs => h hs, fun h s hs => h hs⟩
#align measure_theory.measure.ae_le_iff_absolutely_continuous MeasureTheory.Measure.ae_le_iff_absolutelyContinuous

alias ⟨_root_.LE.le.absolutelyContinuous_of_ae, AbsolutelyContinuous.ae_le⟩ :=
  ae_le_iff_absolutelyContinuous
#align has_le.le.absolutely_continuous_of_ae LE.le.absolutelyContinuous_of_ae
#align measure_theory.measure.absolutely_continuous.ae_le MeasureTheory.Measure.AbsolutelyContinuous.ae_le

alias ae_mono' := AbsolutelyContinuous.ae_le
#align measure_theory.measure.ae_mono' MeasureTheory.Measure.ae_mono'

theorem AbsolutelyContinuous.ae_eq (h : μ ≪ ν) {f g : α → δ} (h' : f =ᵐ[ν] g) : f =ᵐ[μ] g :=
  h.ae_le h'
#align measure_theory.measure.absolutely_continuous.ae_eq MeasureTheory.Measure.AbsolutelyContinuous.ae_eq

protected theorem _root_.MeasureTheory.AEDisjoint.of_absolutelyContinuous
    (h : AEDisjoint μ s t) {ν : Measure α} (h' : ν ≪ μ) :
    AEDisjoint ν s t := h' h

protected theorem _root_.MeasureTheory.AEDisjoint.of_le
    (h : AEDisjoint μ s t) {ν : Measure α} (h' : ν ≤ μ) :
    AEDisjoint ν s t :=
  h.of_absolutelyContinuous (Measure.absolutelyContinuous_of_le h')

/-! ### Quasi measure preserving maps (a.k.a. non-singular maps) -/


/-- A map `f : α → β` is said to be *quasi measure preserving* (a.k.a. non-singular) w.r.t. measures
`μa` and `μb` if it is measurable and `μb s = 0` implies `μa (f ⁻¹' s) = 0`. -/
structure QuasiMeasurePreserving {m0 : MeasurableSpace α} (f : α → β)
  (μa : Measure α := by volume_tac)
  (μb : Measure β := by volume_tac) : Prop where
  protected measurable : Measurable f
  protected absolutelyContinuous : μa.map f ≪ μb
#align measure_theory.measure.quasi_measure_preserving MeasureTheory.Measure.QuasiMeasurePreserving
#align measure_theory.measure.quasi_measure_preserving.measurable MeasureTheory.Measure.QuasiMeasurePreserving.measurable
#align measure_theory.measure.quasi_measure_preserving.absolutely_continuous MeasureTheory.Measure.QuasiMeasurePreserving.absolutelyContinuous

namespace QuasiMeasurePreserving

protected theorem id {_m0 : MeasurableSpace α} (μ : Measure α) : QuasiMeasurePreserving id μ μ :=
  ⟨measurable_id, map_id.absolutelyContinuous⟩
#align measure_theory.measure.quasi_measure_preserving.id MeasureTheory.Measure.QuasiMeasurePreserving.id

variable {μa μa' : Measure α} {μb μb' : Measure β} {μc : Measure γ} {f : α → β}

protected theorem _root_.Measurable.quasiMeasurePreserving
    {_m0 : MeasurableSpace α} (hf : Measurable f) (μ : Measure α) :
    QuasiMeasurePreserving f μ (μ.map f) :=
  ⟨hf, AbsolutelyContinuous.rfl⟩
#align measurable.quasi_measure_preserving Measurable.quasiMeasurePreserving

theorem mono_left (h : QuasiMeasurePreserving f μa μb) (ha : μa' ≪ μa) :
    QuasiMeasurePreserving f μa' μb :=
  ⟨h.1, (ha.map h.1).trans h.2⟩
#align measure_theory.measure.quasi_measure_preserving.mono_left MeasureTheory.Measure.QuasiMeasurePreserving.mono_left

theorem mono_right (h : QuasiMeasurePreserving f μa μb) (ha : μb ≪ μb') :
    QuasiMeasurePreserving f μa μb' :=
  ⟨h.1, h.2.trans ha⟩
#align measure_theory.measure.quasi_measure_preserving.mono_right MeasureTheory.Measure.QuasiMeasurePreserving.mono_right

@[mono]
theorem mono (ha : μa' ≪ μa) (hb : μb ≪ μb') (h : QuasiMeasurePreserving f μa μb) :
    QuasiMeasurePreserving f μa' μb' :=
  (h.mono_left ha).mono_right hb
#align measure_theory.measure.quasi_measure_preserving.mono MeasureTheory.Measure.QuasiMeasurePreserving.mono

protected theorem comp {g : β → γ} {f : α → β} (hg : QuasiMeasurePreserving g μb μc)
    (hf : QuasiMeasurePreserving f μa μb) : QuasiMeasurePreserving (g ∘ f) μa μc :=
  ⟨hg.measurable.comp hf.measurable, by
    rw [← map_map hg.1 hf.1]
    exact (hf.2.map hg.1).trans hg.2⟩
#align measure_theory.measure.quasi_measure_preserving.comp MeasureTheory.Measure.QuasiMeasurePreserving.comp

protected theorem iterate {f : α → α} (hf : QuasiMeasurePreserving f μa μa) :
    ∀ n, QuasiMeasurePreserving f^[n] μa μa
  | 0 => QuasiMeasurePreserving.id μa
  | n + 1 => (hf.iterate n).comp hf
#align measure_theory.measure.quasi_measure_preserving.iterate MeasureTheory.Measure.QuasiMeasurePreserving.iterate

protected theorem aemeasurable (hf : QuasiMeasurePreserving f μa μb) : AEMeasurable f μa :=
  hf.1.aemeasurable
#align measure_theory.measure.quasi_measure_preserving.ae_measurable MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable

theorem ae_map_le (h : QuasiMeasurePreserving f μa μb) : ae (μa.map f) ≤ ae μb :=
  h.2.ae_le
#align measure_theory.measure.quasi_measure_preserving.ae_map_le MeasureTheory.Measure.QuasiMeasurePreserving.ae_map_le

theorem tendsto_ae (h : QuasiMeasurePreserving f μa μb) : Tendsto f (ae μa) (ae μb) :=
  (tendsto_ae_map h.aemeasurable).mono_right h.ae_map_le
#align measure_theory.measure.quasi_measure_preserving.tendsto_ae MeasureTheory.Measure.QuasiMeasurePreserving.tendsto_ae

theorem ae (h : QuasiMeasurePreserving f μa μb) {p : β → Prop} (hg : ∀ᵐ x ∂μb, p x) :
    ∀ᵐ x ∂μa, p (f x) :=
  h.tendsto_ae hg
#align measure_theory.measure.quasi_measure_preserving.ae MeasureTheory.Measure.QuasiMeasurePreserving.ae

theorem ae_eq (h : QuasiMeasurePreserving f μa μb) {g₁ g₂ : β → δ} (hg : g₁ =ᵐ[μb] g₂) :
    g₁ ∘ f =ᵐ[μa] g₂ ∘ f :=
  h.ae hg
#align measure_theory.measure.quasi_measure_preserving.ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.ae_eq

theorem preimage_null (h : QuasiMeasurePreserving f μa μb) {s : Set β} (hs : μb s = 0) :
    μa (f ⁻¹' s) = 0 :=
  preimage_null_of_map_null h.aemeasurable (h.2 hs)
#align measure_theory.measure.quasi_measure_preserving.preimage_null MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null

theorem preimage_mono_ae {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s ≤ᵐ[μb] t) :
    f ⁻¹' s ≤ᵐ[μa] f ⁻¹' t :=
  eventually_map.mp <|
    Eventually.filter_mono (tendsto_ae_map hf.aemeasurable) (Eventually.filter_mono hf.ae_map_le h)
#align measure_theory.measure.quasi_measure_preserving.preimage_mono_ae MeasureTheory.Measure.QuasiMeasurePreserving.preimage_mono_ae

theorem preimage_ae_eq {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s =ᵐ[μb] t) :
    f ⁻¹' s =ᵐ[μa] f ⁻¹' t :=
  EventuallyLE.antisymm (hf.preimage_mono_ae h.le) (hf.preimage_mono_ae h.symm.le)
#align measure_theory.measure.quasi_measure_preserving.preimage_ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.preimage_ae_eq

theorem preimage_iterate_ae_eq {s : Set α} {f : α → α} (hf : QuasiMeasurePreserving f μ μ) (k : ℕ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : f^[k] ⁻¹' s =ᵐ[μ] s := by
  induction' k with k ih; · rfl
  rw [iterate_succ, preimage_comp]
  exact EventuallyEq.trans (hf.preimage_ae_eq ih) hs
#align measure_theory.measure.quasi_measure_preserving.preimage_iterate_ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.preimage_iterate_ae_eq

theorem image_zpow_ae_eq {s : Set α} {e : α ≃ α} (he : QuasiMeasurePreserving e μ μ)
    (he' : QuasiMeasurePreserving e.symm μ μ) (k : ℤ) (hs : e '' s =ᵐ[μ] s) :
    (⇑(e ^ k)) '' s =ᵐ[μ] s := by
  rw [Equiv.image_eq_preimage]
  obtain ⟨k, rfl | rfl⟩ := k.eq_nat_or_neg
  · replace hs : (⇑e⁻¹) ⁻¹' s =ᵐ[μ] s := by rwa [Equiv.image_eq_preimage] at hs
    replace he' : (⇑e⁻¹)^[k] ⁻¹' s =ᵐ[μ] s := he'.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e⁻¹ k, inv_pow e k] at he'
  · rw [zpow_neg, zpow_natCast]
    replace hs : e ⁻¹' s =ᵐ[μ] s := by
      convert he.preimage_ae_eq hs.symm
      rw [Equiv.preimage_image]
    replace he : (⇑e)^[k] ⁻¹' s =ᵐ[μ] s := he.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e k] at he
#align measure_theory.measure.quasi_measure_preserving.image_zpow_ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.image_zpow_ae_eq

-- Need to specify `α := Set α` below because of diamond; see #19041
theorem limsup_preimage_iterate_ae_eq {f : α → α} (hf : QuasiMeasurePreserving f μ μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : limsup (α := Set α) (fun n => (preimage f)^[n] s) atTop =ᵐ[μ] s :=
  haveI : ∀ n, (preimage f)^[n] s =ᵐ[μ] s := by
    intro n
    induction' n with n ih
    · rfl
    simpa only [iterate_succ', comp_apply] using ae_eq_trans (hf.ae_eq ih) hs
  (limsup_ae_eq_of_forall_ae_eq (fun n => (preimage f)^[n] s) this).trans (ae_eq_refl _)
#align measure_theory.measure.quasi_measure_preserving.limsup_preimage_iterate_ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.limsup_preimage_iterate_ae_eq

-- Need to specify `α := Set α` below because of diamond; see #19041
theorem liminf_preimage_iterate_ae_eq {f : α → α} (hf : QuasiMeasurePreserving f μ μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : liminf (α := Set α) (fun n => (preimage f)^[n] s) atTop =ᵐ[μ] s := by
  rw [← ae_eq_set_compl_compl, @Filter.liminf_compl (Set α)]
  rw [← ae_eq_set_compl_compl, ← preimage_compl] at hs
  convert hf.limsup_preimage_iterate_ae_eq hs
  ext1 n
  simp only [← Set.preimage_iterate_eq, comp_apply, preimage_compl]
#align measure_theory.measure.quasi_measure_preserving.liminf_preimage_iterate_ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.liminf_preimage_iterate_ae_eq

/-- By replacing a measurable set that is almost invariant with the `limsup` of its preimages, we
obtain a measurable set that is almost equal and strictly invariant.

(The `liminf` would work just as well.) -/
theorem exists_preimage_eq_of_preimage_ae {f : α → α} (h : QuasiMeasurePreserving f μ μ)
    (hs : MeasurableSet s) (hs' : f ⁻¹' s =ᵐ[μ] s) :
    ∃ t : Set α, MeasurableSet t ∧ t =ᵐ[μ] s ∧ f ⁻¹' t = t :=
  ⟨limsup (fun n => (preimage f)^[n] s) atTop,
    MeasurableSet.measurableSet_limsup fun n =>
      preimage_iterate_eq ▸ h.measurable.iterate n hs,
    h.limsup_preimage_iterate_ae_eq hs',
    Filter.CompleteLatticeHom.apply_limsup_iterate (CompleteLatticeHom.setPreimage f) s⟩
#align measure_theory.measure.quasi_measure_preserving.exists_preimage_eq_of_preimage_ae MeasureTheory.Measure.QuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae

open Pointwise

@[to_additive]
theorem smul_ae_eq_of_ae_eq {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
    {s t : Set α} {μ : Measure α} (g : G)
    (h_qmp : QuasiMeasurePreserving (g⁻¹ • · : α → α) μ μ)
    (h_ae_eq : s =ᵐ[μ] t) : (g • s : Set α) =ᵐ[μ] (g • t : Set α) := by
  simpa only [← preimage_smul_inv] using h_qmp.ae_eq h_ae_eq
#align measure_theory.measure.quasi_measure_preserving.smul_ae_eq_of_ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq
#align measure_theory.measure.quasi_measure_preserving.vadd_ae_eq_of_ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.vadd_ae_eq_of_ae_eq

end QuasiMeasurePreserving

section Pointwise

open Pointwise

@[to_additive]
theorem pairwise_aedisjoint_of_aedisjoint_forall_ne_one {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (h_ae_disjoint : ∀ g ≠ (1 : G), AEDisjoint μ (g • s) s)
    (h_qmp : ∀ g : G, QuasiMeasurePreserving (g • ·) μ μ) :
    Pairwise (AEDisjoint μ on fun g : G => g • s) := by
  intro g₁ g₂ hg
  let g := g₂⁻¹ * g₁
  replace hg : g ≠ 1 := by
    rw [Ne, inv_mul_eq_one]
    exact hg.symm
  have : (g₂⁻¹ • ·) ⁻¹' (g • s ∩ s) = g₁ • s ∩ g₂ • s := by
    rw [preimage_eq_iff_eq_image (MulAction.bijective g₂⁻¹), image_smul, smul_set_inter, smul_smul,
      smul_smul, inv_mul_self, one_smul]
  change μ (g₁ • s ∩ g₂ • s) = 0
  exact this ▸ (h_qmp g₂⁻¹).preimage_null (h_ae_disjoint g hg)
#align measure_theory.measure.pairwise_ae_disjoint_of_ae_disjoint_forall_ne_one MeasureTheory.Measure.pairwise_aedisjoint_of_aedisjoint_forall_ne_one
#align measure_theory.measure.pairwise_ae_disjoint_of_ae_disjoint_forall_ne_zero MeasureTheory.Measure.pairwise_aedisjoint_of_aedisjoint_forall_ne_zero

end Pointwise

/-! ### The `cofinite` filter -/

/-- The filter of sets `s` such that `sᶜ` has finite measure. -/
def cofinite {m0 : MeasurableSpace α} (μ : Measure α) : Filter α :=
  comk (μ · < ∞) (by simp) (fun t ht s hs ↦ (measure_mono hs).trans_lt ht) fun s hs t ht ↦
    (measure_union_le s t).trans_lt <| ENNReal.add_lt_top.2 ⟨hs, ht⟩
#align measure_theory.measure.cofinite MeasureTheory.Measure.cofinite

theorem mem_cofinite : s ∈ μ.cofinite ↔ μ sᶜ < ∞ :=
  Iff.rfl
#align measure_theory.measure.mem_cofinite MeasureTheory.Measure.mem_cofinite

theorem compl_mem_cofinite : sᶜ ∈ μ.cofinite ↔ μ s < ∞ := by rw [mem_cofinite, compl_compl]
#align measure_theory.measure.compl_mem_cofinite MeasureTheory.Measure.compl_mem_cofinite

theorem eventually_cofinite {p : α → Prop} : (∀ᶠ x in μ.cofinite, p x) ↔ μ { x | ¬p x } < ∞ :=
  Iff.rfl
#align measure_theory.measure.eventually_cofinite MeasureTheory.Measure.eventually_cofinite

end Measure

open Measure

open MeasureTheory

protected theorem _root_.AEMeasurable.nullMeasurable {f : α → β} (h : AEMeasurable f μ) :
    NullMeasurable f μ :=
  let ⟨_g, hgm, hg⟩ := h; hgm.nullMeasurable.congr hg.symm
#align ae_measurable.null_measurable AEMeasurable.nullMeasurable

lemma _root_.AEMeasurable.nullMeasurableSet_preimage {f : α → β} {s : Set β}
    (hf : AEMeasurable f μ) (hs : MeasurableSet s) : NullMeasurableSet (f ⁻¹' s) μ :=
  hf.nullMeasurable hs

/-- The preimage of a null measurable set under a (quasi) measure preserving map is a null
measurable set. -/
theorem NullMeasurableSet.preimage {ν : Measure β} {f : α → β} {t : Set β}
    (ht : NullMeasurableSet t ν) (hf : QuasiMeasurePreserving f μ ν) :
    NullMeasurableSet (f ⁻¹' t) μ :=
  ⟨f ⁻¹' toMeasurable ν t, hf.measurable (measurableSet_toMeasurable _ _),
    hf.ae_eq ht.toMeasurable_ae_eq.symm⟩
#align measure_theory.null_measurable_set.preimage MeasureTheory.NullMeasurableSet.preimage

theorem NullMeasurableSet.mono_ac (h : NullMeasurableSet s μ) (hle : ν ≪ μ) :
    NullMeasurableSet s ν :=
  h.preimage <| (QuasiMeasurePreserving.id μ).mono_left hle
#align measure_theory.null_measurable_set.mono_ac MeasureTheory.NullMeasurableSet.mono_ac

theorem NullMeasurableSet.mono (h : NullMeasurableSet s μ) (hle : ν ≤ μ) : NullMeasurableSet s ν :=
  h.mono_ac hle.absolutelyContinuous
#align measure_theory.null_measurable_set.mono MeasureTheory.NullMeasurableSet.mono

theorem AEDisjoint.preimage {ν : Measure β} {f : α → β} {s t : Set β} (ht : AEDisjoint ν s t)
    (hf : QuasiMeasurePreserving f μ ν) : AEDisjoint μ (f ⁻¹' s) (f ⁻¹' t) :=
  hf.preimage_null ht
#align measure_theory.ae_disjoint.preimage MeasureTheory.AEDisjoint.preimage

@[simp]
theorem ae_eq_bot : ae μ = ⊥ ↔ μ = 0 := by
  rw [← empty_mem_iff_bot, mem_ae_iff, compl_empty, measure_univ_eq_zero]
#align measure_theory.ae_eq_bot MeasureTheory.ae_eq_bot

@[simp]
theorem ae_neBot : (ae μ).NeBot ↔ μ ≠ 0 :=
  neBot_iff.trans (not_congr ae_eq_bot)
#align measure_theory.ae_ne_bot MeasureTheory.ae_neBot

instance Measure.ae.neBot [NeZero μ] : (ae μ).NeBot := ae_neBot.2 <| NeZero.ne μ

@[simp]
theorem ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measure α) = ⊥ :=
  ae_eq_bot.2 rfl
#align measure_theory.ae_zero MeasureTheory.ae_zero

@[mono]
theorem ae_mono (h : μ ≤ ν) : ae μ ≤ ae ν :=
  h.absolutelyContinuous.ae_le
#align measure_theory.ae_mono MeasureTheory.ae_mono

theorem mem_ae_map_iff {f : α → β} (hf : AEMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :
    s ∈ ae (μ.map f) ↔ f ⁻¹' s ∈ ae μ := by
  simp only [mem_ae_iff, map_apply_of_aemeasurable hf hs.compl, preimage_compl]
#align measure_theory.mem_ae_map_iff MeasureTheory.mem_ae_map_iff

theorem mem_ae_of_mem_ae_map {f : α → β} (hf : AEMeasurable f μ) {s : Set β}
    (hs : s ∈ ae (μ.map f)) : f ⁻¹' s ∈ ae μ :=
  (tendsto_ae_map hf).eventually hs
#align measure_theory.mem_ae_of_mem_ae_map MeasureTheory.mem_ae_of_mem_ae_map

theorem ae_map_iff {f : α → β} (hf : AEMeasurable f μ) {p : β → Prop}
    (hp : MeasurableSet { x | p x }) : (∀ᵐ y ∂μ.map f, p y) ↔ ∀ᵐ x ∂μ, p (f x) :=
  mem_ae_map_iff hf hp
#align measure_theory.ae_map_iff MeasureTheory.ae_map_iff

theorem ae_of_ae_map {f : α → β} (hf : AEMeasurable f μ) {p : β → Prop} (h : ∀ᵐ y ∂μ.map f, p y) :
    ∀ᵐ x ∂μ, p (f x) :=
  mem_ae_of_mem_ae_map hf h
#align measure_theory.ae_of_ae_map MeasureTheory.ae_of_ae_map

theorem ae_map_mem_range {m0 : MeasurableSpace α} (f : α → β) (hf : MeasurableSet (range f))
    (μ : Measure α) : ∀ᵐ x ∂μ.map f, x ∈ range f := by
  by_cases h : AEMeasurable f μ
  · change range f ∈ ae (μ.map f)
    rw [mem_ae_map_iff h hf]
    filter_upwards using mem_range_self
  · simp [map_of_not_aemeasurable h]
#align measure_theory.ae_map_mem_range MeasureTheory.ae_map_mem_range


section Intervals

theorem biSup_measure_Iic [Preorder α] {s : Set α} (hsc : s.Countable)
    (hst : ∀ x : α, ∃ y ∈ s, x ≤ y) (hdir : DirectedOn (· ≤ ·) s) :
    ⨆ x ∈ s, μ (Iic x) = μ univ := by
  rw [← measure_biUnion_eq_iSup hsc]
  · congr
    simp only [← bex_def] at hst
    exact iUnion₂_eq_univ_iff.2 hst
  · exact directedOn_iff_directed.2 (hdir.directed_val.mono_comp _ fun x y => Iic_subset_Iic.2)
#align measure_theory.bsupr_measure_Iic MeasureTheory.biSup_measure_Iic

theorem tendsto_measure_Ico_atTop [SemilatticeSup α] [NoMaxOrder α]
    [(atTop : Filter α).IsCountablyGenerated] (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Ico a x)) atTop (𝓝 (μ (Ici a))) := by
  haveI : Nonempty α := ⟨a⟩
  have h_mono : Monotone fun x => μ (Ico a x) := fun i j hij => by simp only; gcongr
  convert tendsto_atTop_iSup h_mono
  obtain ⟨xs, hxs_mono, hxs_tendsto⟩ := exists_seq_monotone_tendsto_atTop_atTop α
  have h_Ici : Ici a = ⋃ n, Ico a (xs n) := by
    ext1 x
    simp only [mem_Ici, mem_iUnion, mem_Ico, exists_and_left, iff_self_and]
    intro
    obtain ⟨y, hxy⟩ := NoMaxOrder.exists_gt x
    obtain ⟨n, hn⟩ := tendsto_atTop_atTop.mp hxs_tendsto y
    exact ⟨n, hxy.trans_le (hn n le_rfl)⟩
  rw [h_Ici, measure_iUnion_eq_iSup, iSup_eq_iSup_subseq_of_monotone h_mono hxs_tendsto]
  exact Monotone.directed_le fun i j hij => Ico_subset_Ico_right (hxs_mono hij)
#align measure_theory.tendsto_measure_Ico_at_top MeasureTheory.tendsto_measure_Ico_atTop

theorem tendsto_measure_Ioc_atBot [SemilatticeInf α] [NoMinOrder α]
    [(atBot : Filter α).IsCountablyGenerated] (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Ioc x a)) atBot (𝓝 (μ (Iic a))) := by
  haveI : Nonempty α := ⟨a⟩
  have h_mono : Antitone fun x => μ (Ioc x a) := fun i j hij => by simp only; gcongr
  convert tendsto_atBot_iSup h_mono
  obtain ⟨xs, hxs_mono, hxs_tendsto⟩ := exists_seq_antitone_tendsto_atTop_atBot α
  have h_Iic : Iic a = ⋃ n, Ioc (xs n) a := by
    ext1 x
    simp only [mem_Iic, mem_iUnion, mem_Ioc, exists_and_right, iff_and_self]
    intro
    obtain ⟨y, hxy⟩ := NoMinOrder.exists_lt x
    obtain ⟨n, hn⟩ := tendsto_atTop_atBot.mp hxs_tendsto y
    exact ⟨n, (hn n le_rfl).trans_lt hxy⟩
  rw [h_Iic, measure_iUnion_eq_iSup, iSup_eq_iSup_subseq_of_antitone h_mono hxs_tendsto]
  exact Monotone.directed_le fun i j hij => Ioc_subset_Ioc_left (hxs_mono hij)
#align measure_theory.tendsto_measure_Ioc_at_bot MeasureTheory.tendsto_measure_Ioc_atBot

theorem tendsto_measure_Iic_atTop [SemilatticeSup α] [(atTop : Filter α).IsCountablyGenerated]
    (μ : Measure α) : Tendsto (fun x => μ (Iic x)) atTop (𝓝 (μ univ)) := by
  cases isEmpty_or_nonempty α
  · have h1 : ∀ x : α, Iic x = ∅ := fun x => Subsingleton.elim _ _
    have h2 : (univ : Set α) = ∅ := Subsingleton.elim _ _
    simp_rw [h1, h2]
    exact tendsto_const_nhds
  have h_mono : Monotone fun x => μ (Iic x) := fun i j hij => by simp only; gcongr
  convert tendsto_atTop_iSup h_mono
  obtain ⟨xs, hxs_mono, hxs_tendsto⟩ := exists_seq_monotone_tendsto_atTop_atTop α
  have h_univ : (univ : Set α) = ⋃ n, Iic (xs n) := by
    ext1 x
    simp only [mem_univ, mem_iUnion, mem_Iic, true_iff_iff]
    obtain ⟨n, hn⟩ := tendsto_atTop_atTop.mp hxs_tendsto x
    exact ⟨n, hn n le_rfl⟩
  rw [h_univ, measure_iUnion_eq_iSup, iSup_eq_iSup_subseq_of_monotone h_mono hxs_tendsto]
  exact Monotone.directed_le fun i j hij => Iic_subset_Iic.mpr (hxs_mono hij)
#align measure_theory.tendsto_measure_Iic_at_top MeasureTheory.tendsto_measure_Iic_atTop

theorem tendsto_measure_Ici_atBot [SemilatticeInf α] [h : (atBot : Filter α).IsCountablyGenerated]
    (μ : Measure α) : Tendsto (fun x => μ (Ici x)) atBot (𝓝 (μ univ)) :=
  @tendsto_measure_Iic_atTop αᵒᵈ _ _ h μ
#align measure_theory.tendsto_measure_Ici_at_bot MeasureTheory.tendsto_measure_Ici_atBot

variable [PartialOrder α] {a b : α}

theorem Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ[μ] Iic a := by
  rw [← Iic_diff_right, diff_ae_eq_self, measure_mono_null Set.inter_subset_right ha]
#align measure_theory.Iio_ae_eq_Iic' MeasureTheory.Iio_ae_eq_Iic'

theorem Ioi_ae_eq_Ici' (ha : μ {a} = 0) : Ioi a =ᵐ[μ] Ici a :=
  Iio_ae_eq_Iic' (α := αᵒᵈ) ha
#align measure_theory.Ioi_ae_eq_Ici' MeasureTheory.Ioi_ae_eq_Ici'

theorem Ioo_ae_eq_Ioc' (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Ioc a b :=
  (ae_eq_refl _).inter (Iio_ae_eq_Iic' hb)
#align measure_theory.Ioo_ae_eq_Ioc' MeasureTheory.Ioo_ae_eq_Ioc'

theorem Ioc_ae_eq_Icc' (ha : μ {a} = 0) : Ioc a b =ᵐ[μ] Icc a b :=
  (Ioi_ae_eq_Ici' ha).inter (ae_eq_refl _)
#align measure_theory.Ioc_ae_eq_Icc' MeasureTheory.Ioc_ae_eq_Icc'

theorem Ioo_ae_eq_Ico' (ha : μ {a} = 0) : Ioo a b =ᵐ[μ] Ico a b :=
  (Ioi_ae_eq_Ici' ha).inter (ae_eq_refl _)
#align measure_theory.Ioo_ae_eq_Ico' MeasureTheory.Ioo_ae_eq_Ico'

theorem Ioo_ae_eq_Icc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Icc a b :=
  (Ioi_ae_eq_Ici' ha).inter (Iio_ae_eq_Iic' hb)
#align measure_theory.Ioo_ae_eq_Icc' MeasureTheory.Ioo_ae_eq_Icc'

theorem Ico_ae_eq_Icc' (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Icc a b :=
  (ae_eq_refl _).inter (Iio_ae_eq_Iic' hb)
#align measure_theory.Ico_ae_eq_Icc' MeasureTheory.Ico_ae_eq_Icc'

theorem Ico_ae_eq_Ioc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Ioc a b :=
  (Ioo_ae_eq_Ico' ha).symm.trans (Ioo_ae_eq_Ioc' hb)
#align measure_theory.Ico_ae_eq_Ioc' MeasureTheory.Ico_ae_eq_Ioc'

end Intervals

end

end MeasureTheory

namespace MeasurableEmbedding

open MeasureTheory Measure

variable {m0 : MeasurableSpace α} {m1 : MeasurableSpace β} {f : α → β} (hf : MeasurableEmbedding f)

nonrec theorem map_apply (μ : Measure α) (s : Set β) : μ.map f s = μ (f ⁻¹' s) := by
  refine le_antisymm ?_ (le_map_apply hf.measurable.aemeasurable s)
  set t := f '' toMeasurable μ (f ⁻¹' s) ∪ (range f)ᶜ
  have htm : MeasurableSet t :=
    (hf.measurableSet_image.2 <| measurableSet_toMeasurable _ _).union
      hf.measurableSet_range.compl
  have hst : s ⊆ t := by
    rw [subset_union_compl_iff_inter_subset, ← image_preimage_eq_inter_range]
    exact image_subset _ (subset_toMeasurable _ _)
  have hft : f ⁻¹' t = toMeasurable μ (f ⁻¹' s) := by
    rw [preimage_union, preimage_compl, preimage_range, compl_univ, union_empty,
      hf.injective.preimage_image]
  calc
    μ.map f s ≤ μ.map f t := by gcongr
    _ = μ (f ⁻¹' s) := by rw [map_apply hf.measurable htm, hft, measure_toMeasurable]
#align measurable_embedding.map_apply MeasurableEmbedding.map_apply

lemma comap_add (μ ν : Measure β) : (μ + ν).comap f = μ.comap f + ν.comap f := by
  ext s hs
  simp only [← comapₗ_eq_comap _ hf.injective (fun _ ↦ hf.measurableSet_image.mpr) _ hs,
    _root_.map_add, add_apply]

end MeasurableEmbedding

namespace MeasurableEquiv

/-! Interactions of measurable equivalences and measures -/

open Equiv MeasureTheory.Measure

variable [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- If we map a measure along a measurable equivalence, we can compute the measure on all sets
  (not just the measurable ones). -/
protected theorem map_apply (f : α ≃ᵐ β) (s : Set β) : μ.map f s = μ (f ⁻¹' s) :=
  f.measurableEmbedding.map_apply _ _
#align measurable_equiv.map_apply MeasurableEquiv.map_apply

lemma comap_symm (e : α ≃ᵐ β) : μ.comap e.symm = μ.map e := by
  ext s hs
  rw [e.map_apply, Measure.comap_apply _ e.symm.injective _ _ hs, image_symm]
  exact fun t ht ↦ e.symm.measurableSet_image.mpr ht

lemma map_symm (e : β ≃ᵐ α) : μ.map e.symm = μ.comap e := by
  rw [← comap_symm, symm_symm]

@[simp]
theorem map_symm_map (e : α ≃ᵐ β) : (μ.map e).map e.symm = μ := by
  simp [map_map e.symm.measurable e.measurable]
#align measurable_equiv.map_symm_map MeasurableEquiv.map_symm_map

@[simp]
theorem map_map_symm (e : α ≃ᵐ β) : (ν.map e.symm).map e = ν := by
  simp [map_map e.measurable e.symm.measurable]
#align measurable_equiv.map_map_symm MeasurableEquiv.map_map_symm

theorem map_measurableEquiv_injective (e : α ≃ᵐ β) : Injective (Measure.map e) := by
  intro μ₁ μ₂ hμ
  apply_fun Measure.map e.symm at hμ
  simpa [map_symm_map e] using hμ
#align measurable_equiv.map_measurable_equiv_injective MeasurableEquiv.map_measurableEquiv_injective

theorem map_apply_eq_iff_map_symm_apply_eq (e : α ≃ᵐ β) : μ.map e = ν ↔ ν.map e.symm = μ := by
  rw [← (map_measurableEquiv_injective e).eq_iff, map_map_symm, eq_comm]
#align measurable_equiv.map_apply_eq_iff_map_symm_apply_eq MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq

theorem map_ae (f : α ≃ᵐ β) (μ : Measure α) : Filter.map f (ae μ) = ae (map f μ) := by
  ext s
  simp_rw [mem_map, mem_ae_iff, ← preimage_compl, f.map_apply]
#align measurable_equiv.map_ae MeasurableEquiv.map_ae

theorem quasiMeasurePreserving_symm (μ : Measure α) (e : α ≃ᵐ β) :
    QuasiMeasurePreserving e.symm (map e μ) μ :=
  ⟨e.symm.measurable, by rw [Measure.map_map, e.symm_comp_self, Measure.map_id] <;> measurability⟩
#align measurable_equiv.quasi_measure_preserving_symm MeasurableEquiv.quasiMeasurePreserving_symm

end MeasurableEquiv

namespace MeasureTheory

theorem OuterMeasure.toMeasure_zero [MeasurableSpace α] :
    (0 : OuterMeasure α).toMeasure (le_top.trans OuterMeasure.zero_caratheodory.symm.le) = 0 := by
  rw [← Measure.measure_univ_eq_zero, toMeasure_apply _ _ MeasurableSet.univ,
    OuterMeasure.coe_zero, Pi.zero_apply]
#align measure_theory.outer_measure.to_measure_zero MeasureTheory.OuterMeasure.toMeasure_zero

end MeasureTheory

end
