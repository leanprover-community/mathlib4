/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module measure_theory.measure.measure_space
! leanprover-community/mathlib commit 88fcb83fe7996142dfcfe7368d31304a9adc874a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.NullMeasurable
import Mathbin.MeasureTheory.MeasurableSpace
import Mathbin.Topology.Algebra.Order.LiminfLimsup

/-!
# Measure spaces

The definition of a measure and a measure space are in `measure_theory.measure_space_def`, with
only a few basic properties. This file provides many more properties of these objects.
This separation allows the measurability tactic to import only the file `measure_space_def`, and to
be available in `measure_space` (through `measurable_space`).

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

We introduce the following typeclasses for measures:

* `is_probability_measure μ`: `μ univ = 1`;
* `is_finite_measure μ`: `μ univ < ∞`;
* `sigma_finite μ`: there exists a countable collection of sets that cover `univ`
  where `μ` is finite;
* `is_locally_finite_measure μ` : `∀ x, ∃ s ∈ 𝓝 x, μ s < ∞`;
* `has_no_atoms μ` : `∀ x, μ {x} = 0`; possibly should be redefined as
  `∀ s, 0 < μ s → ∃ t ⊆ s, 0 < μ t ∧ μ t < μ s`.

Given a measure, the null sets are the sets where `μ s = 0`, where `μ` denotes the corresponding
outer measure (so `s` might not be measurable). We can then define the completion of `μ` as the
measure on the least `σ`-algebra that also contains all null sets, by defining the measure to be `0`
on the null sets.

## Main statements

* `completion` is the completion of a measure to all null measurable sets.
* `measure.of_measurable` and `outer_measure.to_measure` are two important ways to define a measure.

## Implementation notes

Given `μ : measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

You often don't want to define a measure via its constructor.
Two ways that are sometimes more convenient:
* `measure.of_measurable` is a way to define a measure by only giving its value on measurable sets
  and proving the properties (1) and (2) mentioned above.
* `outer_measure.to_measure` is a way of obtaining a measure from an outer measure by showing that
  all measurable sets in the measurable space are Carathéodory measurable.

To prove that two measures are equal, there are multiple options:
* `ext`: two measures are equal if they are equal on all measurable sets.
* `ext_of_generate_from_of_Union`: two measures are equal if they are equal on a π-system generating
  the measurable sets, if the π-system contains a spanning increasing sequence of sets where the
  measures take finite value (in particular the measures are σ-finite). This is a special case of
  the more general `ext_of_generate_from_of_cover`
* `ext_of_generate_finite`: two finite measures are equal if they are equal on a π-system
  generating the measurable sets. This is a special case of `ext_of_generate_from_of_Union` using
  `C ∪ {univ}`, but is easier to work with.

A `measure_space` is a class that is a measurable space with a canonical measure.
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

open TopologicalSpace (SecondCountableTopology)

open Classical Topology BigOperators Filter ENNReal NNReal Interval MeasureTheory

variable {α β γ δ ι R R' : Type _}

namespace MeasureTheory

section

variable {m : MeasurableSpace α} {μ μ₁ μ₂ : Measure α} {s s₁ s₂ t : Set α}

instance ae_isMeasurablyGenerated : IsMeasurablyGenerated μ.ae :=
  ⟨fun s hs =>
    let ⟨t, hst, htm, htμ⟩ := exists_measurable_superset_of_null hs
    ⟨tᶜ, compl_mem_ae_iff.2 htμ, htm.compl, compl_subset_comm.1 hst⟩⟩
#align measure_theory.ae_is_measurably_generated MeasureTheory.ae_isMeasurablyGenerated

/-- See also `measure_theory.ae_restrict_uIoc_iff`. -/
theorem ae_uIoc_iff [LinearOrder α] {a b : α} {P : α → Prop} :
    (∀ᵐ x ∂μ, x ∈ Ι a b → P x) ↔ (∀ᵐ x ∂μ, x ∈ Ioc a b → P x) ∧ ∀ᵐ x ∂μ, x ∈ Ioc b a → P x := by
  simp only [uIoc_eq_union, mem_union, or_imp, eventually_and]
#align measure_theory.ae_uIoc_iff MeasureTheory.ae_uIoc_iff

theorem measure_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂) : μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
  measure_union₀ h.NullMeasurableSet hd.AeDisjoint
#align measure_theory.measure_union MeasureTheory.measure_union

theorem measure_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁) : μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
  measure_union₀' h.NullMeasurableSet hd.AeDisjoint
#align measure_theory.measure_union' MeasureTheory.measure_union'

theorem measure_inter_add_diff (s : Set α) (ht : MeasurableSet t) : μ (s ∩ t) + μ (s \ t) = μ s :=
  measure_inter_add_diff₀ _ ht.NullMeasurableSet
#align measure_theory.measure_inter_add_diff MeasureTheory.measure_inter_add_diff

theorem measure_diff_add_inter (s : Set α) (ht : MeasurableSet t) : μ (s \ t) + μ (s ∩ t) = μ s :=
  (add_comm _ _).trans (measure_inter_add_diff s ht)
#align measure_theory.measure_diff_add_inter MeasureTheory.measure_diff_add_inter

theorem measure_union_add_inter (s : Set α) (ht : MeasurableSet t) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t :=
  by
  rw [← measure_inter_add_diff (s ∪ t) ht, Set.union_inter_cancel_right, union_diff_right, ←
    measure_inter_add_diff s ht]
  ac_rfl
#align measure_theory.measure_union_add_inter MeasureTheory.measure_union_add_inter

theorem measure_union_add_inter' (hs : MeasurableSet s) (t : Set α) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [union_comm, inter_comm, measure_union_add_inter t hs, add_comm]
#align measure_theory.measure_union_add_inter' MeasureTheory.measure_union_add_inter'

theorem measure_add_measure_compl (h : MeasurableSet s) : μ s + μ (sᶜ) = μ univ :=
  measure_add_measure_compl₀ h.NullMeasurableSet
#align measure_theory.measure_add_measure_compl MeasureTheory.measure_add_measure_compl

theorem measure_bUnion₀ {s : Set β} {f : β → Set α} (hs : s.Countable)
    (hd : s.Pairwise (AeDisjoint μ on f)) (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
    μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) :=
  by
  haveI := hs.to_encodable
  rw [bUnion_eq_Union]
  exact measure_Union₀ (hd.on_injective Subtype.coe_injective fun x => x.2) fun x => h x x.2
#align measure_theory.measure_bUnion₀ MeasureTheory.measure_bUnion₀

theorem measure_bUnion {s : Set β} {f : β → Set α} (hs : s.Countable) (hd : s.PairwiseDisjoint f)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) :=
  measure_bUnion₀ hs hd.AeDisjoint fun b hb => (h b hb).NullMeasurableSet
#align measure_theory.measure_bUnion MeasureTheory.measure_bUnion

theorem measure_sUnion₀ {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise (AeDisjoint μ))
    (h : ∀ s ∈ S, NullMeasurableSet s μ) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_bUnion, measure_bUnion₀ hs hd h]
#align measure_theory.measure_sUnion₀ MeasureTheory.measure_sUnion₀

theorem measure_unionₛ {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise Disjoint)
    (h : ∀ s ∈ S, MeasurableSet s) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_bUnion, measure_bUnion hs hd h]
#align measure_theory.measure_sUnion MeasureTheory.measure_unionₛ

theorem measure_bUnion_finset₀ {s : Finset ι} {f : ι → Set α}
    (hd : Set.Pairwise (↑s) (AeDisjoint μ on f)) (hm : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
    μ (⋃ b ∈ s, f b) = ∑ p in s, μ (f p) :=
  by
  rw [← Finset.sum_attach, Finset.attach_eq_univ, ← tsum_fintype]
  exact measure_bUnion₀ s.countable_to_set hd hm
#align measure_theory.measure_bUnion_finset₀ MeasureTheory.measure_bUnion_finset₀

theorem measure_bUnion_finset {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑ p in s, μ (f p) :=
  measure_bUnion_finset₀ hd.AeDisjoint fun b hb => (hm b hb).NullMeasurableSet
#align measure_theory.measure_bUnion_finset MeasureTheory.measure_bUnion_finset

/-- The measure of a disjoint union (even uncountable) of measurable sets is at least the sum of
the measures of the sets. -/
theorem tsum_meas_le_meas_unionᵢ_of_disjoint {ι : Type _} [MeasurableSpace α] (μ : Measure α)
    {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) :=
  by
  rcases show Summable fun i => μ (As i) from ENNReal.summable with ⟨S, hS⟩
  rw [hS.tsum_eq]
  refine' tendsto_le_of_eventuallyLE hS tendsto_const_nhds (eventually_of_forall _)
  intro s
  rw [← measure_bUnion_finset (fun i hi j hj hij => As_disj hij) fun i _ => As_mble i]
  exact measure_mono (Union₂_subset_Union (fun i : ι => i ∈ s) fun i : ι => As i)
#align measure_theory.tsum_meas_le_meas_Union_of_disjoint MeasureTheory.tsum_meas_le_meas_unionᵢ_of_disjoint

/-- If `s` is a countable set, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem tsum_measure_preimage_singleton {s : Set β} (hs : s.Countable) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑' b : s, μ (f ⁻¹' {↑b})) = μ (f ⁻¹' s) := by
  rw [← Set.bunionᵢ_preimage_singleton, measure_bUnion hs (pairwise_disjoint_fiber _ _) hf]
#align measure_theory.tsum_measure_preimage_singleton MeasureTheory.tsum_measure_preimage_singleton

/-- If `s` is a `finset`, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
theorem sum_measure_preimage_singleton (s : Finset β) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑ b in s, μ (f ⁻¹' {b})) = μ (f ⁻¹' ↑s) := by
  simp only [← measure_bUnion_finset (pairwise_disjoint_fiber _ _) hf,
    Finset.set_bunionᵢ_preimage_singleton]
#align measure_theory.sum_measure_preimage_singleton MeasureTheory.sum_measure_preimage_singleton

theorem measure_diff_null' (h : μ (s₁ ∩ s₂) = 0) : μ (s₁ \ s₂) = μ s₁ :=
  measure_congr <| diff_ae_eq_self.2 h
#align measure_theory.measure_diff_null' MeasureTheory.measure_diff_null'

theorem measure_diff_null (h : μ s₂ = 0) : μ (s₁ \ s₂) = μ s₁ :=
  measure_diff_null' <| measure_mono_null (inter_subset_right _ _) h
#align measure_theory.measure_diff_null MeasureTheory.measure_diff_null

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
  tsub_le_iff_left.2 <|
    calc
      μ s₁ ≤ μ (s₂ ∪ s₁) := measure_mono (subset_union_right _ _)
      _ = μ (s₂ ∪ s₁ \ s₂) := (congr_arg μ union_diff_self.symm)
      _ ≤ μ s₂ + μ (s₁ \ s₂) := measure_union_le _ _
      
#align measure_theory.le_measure_diff MeasureTheory.le_measure_diff

theorem measure_diff_lt_of_lt_add (hs : MeasurableSet s) (hst : s ⊆ t) (hs' : μ s ≠ ∞) {ε : ℝ≥0∞}
    (h : μ t < μ s + ε) : μ (t \ s) < ε :=
  by
  rw [measure_diff hst hs hs']; rw [add_comm] at h
  exact ENNReal.sub_lt_of_lt_add (measure_mono hst) h
#align measure_theory.measure_diff_lt_of_lt_add MeasureTheory.measure_diff_lt_of_lt_add

theorem measure_diff_le_iff_le_add (hs : MeasurableSet s) (hst : s ⊆ t) (hs' : μ s ≠ ∞) {ε : ℝ≥0∞} :
    μ (t \ s) ≤ ε ↔ μ t ≤ μ s + ε := by rwa [measure_diff hst hs hs', tsub_le_iff_left]
#align measure_theory.measure_diff_le_iff_le_add MeasureTheory.measure_diff_le_iff_le_add

theorem measure_eq_measure_of_null_diff {s t : Set α} (hst : s ⊆ t) (h_nulldiff : μ (t \ s) = 0) :
    μ s = μ t :=
  measure_congr (hst.EventuallyLE.antisymm <| ae_le_set.mpr h_nulldiff)
#align measure_theory.measure_eq_measure_of_null_diff MeasureTheory.measure_eq_measure_of_null_diff

theorem measure_eq_measure_of_between_null_diff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃)
    (h_nulldiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ :=
  by
  have le12 : μ s₁ ≤ μ s₂ := measure_mono h12
  have le23 : μ s₂ ≤ μ s₃ := measure_mono h23
  have key : μ s₃ ≤ μ s₁ :=
    calc
      μ s₃ = μ (s₃ \ s₁ ∪ s₁) := by rw [diff_union_of_subset (h12.trans h23)]
      _ ≤ μ (s₃ \ s₁) + μ s₁ := (measure_union_le _ _)
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

theorem measure_compl (h₁ : MeasurableSet s) (h_fin : μ s ≠ ∞) : μ (sᶜ) = μ univ - μ s :=
  by
  rw [compl_eq_univ_diff]
  exact measure_diff (subset_univ s) h₁ h_fin
#align measure_theory.measure_compl MeasureTheory.measure_compl

@[simp]
theorem union_ae_eq_left_iff_ae_subset : (s ∪ t : Set α) =ᵐ[μ] s ↔ t ≤ᵐ[μ] s :=
  by
  rw [ae_le_set]
  refine'
    ⟨fun h => by simpa only [union_diff_left] using (ae_eq_set.mp h).1, fun h =>
      eventually_le_antisymm_iff.mpr
        ⟨by rwa [ae_le_set, union_diff_left],
          HasSubset.Subset.eventuallyLE <| subset_union_left s t⟩⟩
#align measure_theory.union_ae_eq_left_iff_ae_subset MeasureTheory.union_ae_eq_left_iff_ae_subset

@[simp]
theorem union_ae_eq_right_iff_ae_subset : (s ∪ t : Set α) =ᵐ[μ] t ↔ s ≤ᵐ[μ] t := by
  rw [union_comm, union_ae_eq_left_iff_ae_subset]
#align measure_theory.union_ae_eq_right_iff_ae_subset MeasureTheory.union_ae_eq_right_iff_ae_subset

theorem ae_eq_of_ae_subset_of_measure_ge (h₁ : s ≤ᵐ[μ] t) (h₂ : μ t ≤ μ s) (hsm : MeasurableSet s)
    (ht : μ t ≠ ∞) : s =ᵐ[μ] t :=
  by
  refine' eventually_le_antisymm_iff.mpr ⟨h₁, ae_le_set.mpr _⟩
  replace h₂ : μ t = μ s; exact h₂.antisymm (measure_mono_ae h₁)
  replace ht : μ s ≠ ∞; exact h₂ ▸ ht
  rw [measure_diff' t hsm ht, measure_congr (union_ae_eq_left_iff_ae_subset.mpr h₁), h₂, tsub_self]
#align measure_theory.ae_eq_of_ae_subset_of_measure_ge MeasureTheory.ae_eq_of_ae_subset_of_measure_ge

/-- If `s ⊆ t`, `μ t ≤ μ s`, `μ t ≠ ∞`, and `s` is measurable, then `s =ᵐ[μ] t`. -/
theorem ae_eq_of_subset_of_measure_ge (h₁ : s ⊆ t) (h₂ : μ t ≤ μ s) (hsm : MeasurableSet s)
    (ht : μ t ≠ ∞) : s =ᵐ[μ] t :=
  ae_eq_of_ae_subset_of_measure_ge (HasSubset.Subset.eventuallyLE h₁) h₂ hsm ht
#align measure_theory.ae_eq_of_subset_of_measure_ge MeasureTheory.ae_eq_of_subset_of_measure_ge

theorem measure_unionᵢ_congr_of_subset [Countable β] {s : β → Set α} {t : β → Set α}
    (hsub : ∀ b, s b ⊆ t b) (h_le : ∀ b, μ (t b) ≤ μ (s b)) : μ (⋃ b, s b) = μ (⋃ b, t b) :=
  by
  rcases em (∃ b, μ (t b) = ∞) with (⟨b, hb⟩ | htop)
  ·
    calc
      μ (⋃ b, s b) = ∞ := top_unique (hb ▸ (h_le b).trans <| measure_mono <| subset_Union _ _)
      _ = μ (⋃ b, t b) := Eq.symm <| top_unique <| hb ▸ measure_mono <| subset_Union _ _
      
  push_neg  at htop
  refine' le_antisymm (measure_mono (Union_mono hsub)) _
  set M := to_measurable μ
  have H : ∀ b, (M (t b) ∩ M (⋃ b, s b) : Set α) =ᵐ[μ] M (t b) :=
    by
    refine' fun b => ae_eq_of_subset_of_measure_ge (inter_subset_left _ _) _ _ _
    ·
      calc
        μ (M (t b)) = μ (t b) := measure_to_measurable _
        _ ≤ μ (s b) := (h_le b)
        _ ≤ μ (M (t b) ∩ M (⋃ b, s b)) :=
          measure_mono <|
            subset_inter ((hsub b).trans <| subset_to_measurable _ _)
              ((subset_Union _ _).trans <| subset_to_measurable _ _)
        
    · exact (measurable_set_to_measurable _ _).inter (measurable_set_to_measurable _ _)
    · rw [measure_to_measurable]
      exact htop b
  calc
    μ (⋃ b, t b) ≤ μ (⋃ b, M (t b)) := measure_mono (Union_mono fun b => subset_to_measurable _ _)
    _ = μ (⋃ b, M (t b) ∩ M (⋃ b, s b)) := (measure_congr (EventuallyEq.countable_unionᵢ H).symm)
    _ ≤ μ (M (⋃ b, s b)) := (measure_mono (Union_subset fun b => inter_subset_right _ _))
    _ = μ (⋃ b, s b) := measure_to_measurable _
    
#align measure_theory.measure_Union_congr_of_subset MeasureTheory.measure_unionᵢ_congr_of_subset

theorem measure_union_congr_of_subset {t₁ t₂ : Set α} (hs : s₁ ⊆ s₂) (hsμ : μ s₂ ≤ μ s₁)
    (ht : t₁ ⊆ t₂) (htμ : μ t₂ ≤ μ t₁) : μ (s₁ ∪ t₁) = μ (s₂ ∪ t₂) :=
  by
  rw [union_eq_Union, union_eq_Union]
  exact measure_Union_congr_of_subset (Bool.forall_bool.2 ⟨ht, hs⟩) (Bool.forall_bool.2 ⟨htμ, hsμ⟩)
#align measure_theory.measure_union_congr_of_subset MeasureTheory.measure_union_congr_of_subset

@[simp]
theorem measure_unionᵢ_toMeasurable [Countable β] (s : β → Set α) :
    μ (⋃ b, toMeasurable μ (s b)) = μ (⋃ b, s b) :=
  Eq.symm <|
    measure_unionᵢ_congr_of_subset (fun b => subset_toMeasurable _ _) fun b =>
      (measure_toMeasurable _).le
#align measure_theory.measure_Union_to_measurable MeasureTheory.measure_unionᵢ_toMeasurable

theorem measure_bUnion_toMeasurable {I : Set β} (hc : I.Countable) (s : β → Set α) :
    μ (⋃ b ∈ I, toMeasurable μ (s b)) = μ (⋃ b ∈ I, s b) :=
  by
  haveI := hc.to_encodable
  simp only [bUnion_eq_Union, measure_Union_to_measurable]
#align measure_theory.measure_bUnion_to_measurable MeasureTheory.measure_bUnion_toMeasurable

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
    (∑ i in s, μ (t i)) ≤ μ (univ : Set α) :=
  by
  rw [← measure_bUnion_finset H h]
  exact measure_mono (subset_univ _)
#align measure_theory.sum_measure_le_measure_univ MeasureTheory.sum_measure_le_measure_univ

theorem tsum_measure_le_measure_univ {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i))
    (H : Pairwise (Disjoint on s)) : (∑' i, μ (s i)) ≤ μ (univ : Set α) :=
  by
  rw [ENNReal.tsum_eq_supᵢ_sum]
  exact supᵢ_le fun s => sum_measure_le_measure_univ (fun i hi => hs i) fun i hi j hj hij => H hij
#align measure_theory.tsum_measure_le_measure_univ MeasureTheory.tsum_measure_le_measure_univ

/-- Pigeonhole principle for measure spaces: if `∑' i, μ (s i) > μ univ`, then
one of the intersections `s i ∩ s j` is not empty. -/
theorem exists_nonempty_inter_of_measure_univ_lt_tsum_measure {m : MeasurableSpace α}
    (μ : Measure α) {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i))
    (H : μ (univ : Set α) < ∑' i, μ (s i)) : ∃ (i j : _)(h : i ≠ j), (s i ∩ s j).Nonempty :=
  by
  contrapose! H
  apply tsum_measure_le_measure_univ hs
  intro i j hij
  rw [Function.onFun, disjoint_iff_inf_le]
  exact fun x hx => H i j hij ⟨x, hx⟩
#align measure_theory.exists_nonempty_inter_of_measure_univ_lt_tsum_measure MeasureTheory.exists_nonempty_inter_of_measure_univ_lt_tsum_measure

/-- Pigeonhole principle for measure spaces: if `s` is a `finset` and
`∑ i in s, μ (t i) > μ univ`, then one of the intersections `t i ∩ t j` is not empty. -/
theorem exists_nonempty_inter_of_measure_univ_lt_sum_measure {m : MeasurableSpace α} (μ : Measure α)
    {s : Finset ι} {t : ι → Set α} (h : ∀ i ∈ s, MeasurableSet (t i))
    (H : μ (univ : Set α) < ∑ i in s, μ (t i)) :
    ∃ i ∈ s, ∃ j ∈ s, ∃ h : i ≠ j, (t i ∩ t j).Nonempty :=
  by
  contrapose! H
  apply sum_measure_le_measure_univ h
  intro i hi j hj hij
  rw [Function.onFun, disjoint_iff_inf_le]
  exact fun x hx => H i hi j hj hij ⟨x, hx⟩
#align measure_theory.exists_nonempty_inter_of_measure_univ_lt_sum_measure MeasureTheory.exists_nonempty_inter_of_measure_univ_lt_sum_measure

/-- If two sets `s` and `t` are included in a set `u`, and `μ s + μ t > μ u`,
then `s` intersects `t`. Version assuming that `t` is measurable. -/
theorem nonempty_inter_of_measure_lt_add {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (ht : MeasurableSet t) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ u < μ s + μ t) : (s ∩ t).Nonempty :=
  by
  rw [← Set.not_disjoint_iff_nonempty_inter]
  contrapose! h
  calc
    μ s + μ t = μ (s ∪ t) := (measure_union h ht).symm
    _ ≤ μ u := measure_mono (union_subset h's h't)
    
#align measure_theory.nonempty_inter_of_measure_lt_add MeasureTheory.nonempty_inter_of_measure_lt_add

/-- If two sets `s` and `t` are included in a set `u`, and `μ s + μ t > μ u`,
then `s` intersects `t`. Version assuming that `s` is measurable. -/
theorem nonempty_inter_of_measure_lt_add' {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (hs : MeasurableSet s) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ u < μ s + μ t) : (s ∩ t).Nonempty :=
  by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measure_lt_add μ hs h't h's h
#align measure_theory.nonempty_inter_of_measure_lt_add' MeasureTheory.nonempty_inter_of_measure_lt_add'

/-- Continuity from below: the measure of the union of a directed sequence of (not necessarily
-measurable) sets is the supremum of the measures. -/
theorem measure_unionᵢ_eq_supᵢ [Countable ι] {s : ι → Set α} (hd : Directed (· ⊆ ·) s) :
    μ (⋃ i, s i) = ⨆ i, μ (s i) := by
  cases nonempty_encodable ι
  -- WLOG, `ι = ℕ`
  generalize ht : Function.extend Encodable.encode s ⊥ = t
  replace hd : Directed (· ⊆ ·) t := ht ▸ hd.extend_bot Encodable.encode_injective
  suffices μ (⋃ n, t n) = ⨆ n, μ (t n)
    by
    simp only [← ht, encodable.encode_injective.apply_extend μ, ← supr_eq_Union,
      supᵢ_extend_bot Encodable.encode_injective, (· ∘ ·), Pi.bot_apply, bot_eq_empty,
      measure_empty] at this
    exact this.trans (supᵢ_extend_bot Encodable.encode_injective _)
  clear! ι
  -- The `≥` inequality is trivial
  refine' le_antisymm _ (supᵢ_le fun i => measure_mono <| subset_Union _ _)
  -- Choose `T n ⊇ t n` of the same measure, put `Td n = disjointed T`
  set T : ℕ → Set α := fun n => to_measurable μ (t n)
  set Td : ℕ → Set α := disjointed T
  have hm : ∀ n, MeasurableSet (Td n) :=
    MeasurableSet.disjointed fun n => measurable_set_to_measurable _ _
  calc
    μ (⋃ n, t n) ≤ μ (⋃ n, T n) := measure_mono (Union_mono fun i => subset_to_measurable _ _)
    _ = μ (⋃ n, Td n) := by rw [unionᵢ_disjointed]
    _ ≤ ∑' n, μ (Td n) := (measure_Union_le _)
    _ = ⨆ I : Finset ℕ, ∑ n in I, μ (Td n) := ENNReal.tsum_eq_supᵢ_sum
    _ ≤ ⨆ n, μ (t n) := supᵢ_le fun I => _
    
  rcases hd.finset_le I with ⟨N, hN⟩
  calc
    (∑ n in I, μ (Td n)) = μ (⋃ n ∈ I, Td n) :=
      (measure_bUnion_finset ((disjoint_disjointed T).set_pairwise I) fun n _ => hm n).symm
    _ ≤ μ (⋃ n ∈ I, T n) := (measure_mono (Union₂_mono fun n hn => disjointed_subset _ _))
    _ = μ (⋃ n ∈ I, t n) := (measure_bUnion_to_measurable I.countable_to_set _)
    _ ≤ μ (t N) := (measure_mono (Union₂_subset hN))
    _ ≤ ⨆ n, μ (t n) := le_supᵢ (μ ∘ t) N
    
#align measure_theory.measure_Union_eq_supr MeasureTheory.measure_unionᵢ_eq_supᵢ

theorem measure_bUnion_eq_supᵢ {s : ι → Set α} {t : Set ι} (ht : t.Countable)
    (hd : DirectedOn ((· ⊆ ·) on s) t) : μ (⋃ i ∈ t, s i) = ⨆ i ∈ t, μ (s i) :=
  by
  haveI := ht.to_encodable
  rw [bUnion_eq_Union, measure_Union_eq_supr hd.directed_coe, ← supᵢ_subtype'']
#align measure_theory.measure_bUnion_eq_supr MeasureTheory.measure_bUnion_eq_supᵢ

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s k) -/
/-- Continuity from above: the measure of the intersection of a decreasing sequence of measurable
sets is the infimum of the measures. -/
theorem measure_interᵢ_eq_infᵢ [Countable ι] {s : ι → Set α} (h : ∀ i, MeasurableSet (s i))
    (hd : Directed (· ⊇ ·) s) (hfin : ∃ i, μ (s i) ≠ ∞) : μ (⋂ i, s i) = ⨅ i, μ (s i) :=
  by
  rcases hfin with ⟨k, hk⟩
  have : ∀ (t) (_ : t ⊆ s k), μ t ≠ ∞ := fun t ht => ne_top_of_le_ne_top hk (measure_mono ht)
  rw [← ENNReal.sub_sub_cancel hk (infᵢ_le _ k), ENNReal.sub_infᵢ, ←
    ENNReal.sub_sub_cancel hk (measure_mono (Inter_subset _ k)), ←
    measure_diff (Inter_subset _ k) (MeasurableSet.interᵢ h) (this _ (Inter_subset _ k)),
    diff_Inter, measure_Union_eq_supr]
  · congr 1
    refine' le_antisymm (supᵢ_mono' fun i => _) (supᵢ_mono fun i => _)
    · rcases hd i k with ⟨j, hji, hjk⟩
      use j
      rw [← measure_diff hjk (h _) (this _ hjk)]
      exact measure_mono (diff_subset_diff_right hji)
    · rw [tsub_le_iff_right, ← measure_union disjoint_sdiff_left (h i), Set.union_comm]
      exact measure_mono (diff_subset_iff.1 <| subset.refl _)
  · exact hd.mono_comp _ fun _ _ => diff_subset_diff_right
#align measure_theory.measure_Inter_eq_infi MeasureTheory.measure_interᵢ_eq_infᵢ

/-- Continuity from below: the measure of the union of an increasing sequence of measurable sets
is the limit of the measures. -/
theorem tendsto_measure_unionᵢ [SemilatticeSup ι] [Countable ι] {s : ι → Set α} (hm : Monotone s) :
    Tendsto (μ ∘ s) atTop (𝓝 (μ (⋃ n, s n))) :=
  by
  rw [measure_Union_eq_supr (directed_of_sup hm)]
  exact tendsto_atTop_supᵢ fun n m hnm => measure_mono <| hm hnm
#align measure_theory.tendsto_measure_Union MeasureTheory.tendsto_measure_unionᵢ

/-- Continuity from above: the measure of the intersection of a decreasing sequence of measurable
sets is the limit of the measures. -/
theorem tendsto_measure_interᵢ [Countable ι] [SemilatticeSup ι] {s : ι → Set α}
    (hs : ∀ n, MeasurableSet (s n)) (hm : Antitone s) (hf : ∃ i, μ (s i) ≠ ∞) :
    Tendsto (μ ∘ s) atTop (𝓝 (μ (⋂ n, s n))) :=
  by
  rw [measure_Inter_eq_infi hs (directed_of_sup hm) hf]
  exact tendsto_atTop_infᵢ fun n m hnm => measure_mono <| hm hnm
#align measure_theory.tendsto_measure_Inter MeasureTheory.tendsto_measure_interᵢ

/-- The measure of the intersection of a decreasing sequence of measurable
sets indexed by a linear order with first countable topology is the limit of the measures. -/
theorem tendsto_measure_bInter_gt {ι : Type _} [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [DenselyOrdered ι] [TopologicalSpace.FirstCountableTopology ι] {s : ι → Set α}
    {a : ι} (hs : ∀ r > a, MeasurableSet (s r)) (hm : ∀ i j, a < i → i ≤ j → s i ⊆ s j)
    (hf : ∃ r > a, μ (s r) ≠ ∞) : Tendsto (μ ∘ s) (𝓝[Ioi a] a) (𝓝 (μ (⋂ r > a, s r))) :=
  by
  refine' tendsto_order.2 ⟨fun l hl => _, fun L hL => _⟩
  ·
    filter_upwards [self_mem_nhdsWithin]with r hr using hl.trans_le
        (measure_mono (bInter_subset_of_mem hr))
  obtain ⟨u, u_anti, u_pos, u_lim⟩ :
    ∃ u : ℕ → ι, StrictAnti u ∧ (∀ n : ℕ, a < u n) ∧ tendsto u at_top (𝓝 a) :=
    by
    rcases hf with ⟨r, ar, hr⟩
    rcases exists_seq_strictAnti_tendsto' ar with ⟨w, w_anti, w_mem, w_lim⟩
    exact ⟨w, w_anti, fun n => (w_mem n).1, w_lim⟩
  have A : tendsto (μ ∘ s ∘ u) at_top (𝓝 (μ (⋂ n, s (u n)))) :=
    by
    refine' tendsto_measure_Inter (fun n => hs _ (u_pos n)) _ _
    · intro m n hmn
      exact hm _ _ (u_pos n) (u_anti.antitone hmn)
    · rcases hf with ⟨r, rpos, hr⟩
      obtain ⟨n, hn⟩ : ∃ n : ℕ, u n < r := ((tendsto_order.1 u_lim).2 r rpos).exists
      refine' ⟨n, ne_of_lt (lt_of_le_of_lt _ hr.lt_top)⟩
      exact measure_mono (hm _ _ (u_pos n) hn.le)
  have B : (⋂ n, s (u n)) = ⋂ r > a, s r :=
    by
    apply subset.antisymm
    · simp only [subset_Inter_iff, gt_iff_lt]
      intro r rpos
      obtain ⟨n, hn⟩ : ∃ n, u n < r := ((tendsto_order.1 u_lim).2 _ rpos).exists
      exact subset.trans (Inter_subset _ n) (hm (u n) r (u_pos n) hn.le)
    · simp only [subset_Inter_iff, gt_iff_lt]
      intro n
      apply bInter_subset_of_mem
      exact u_pos n
  rw [B] at A
  obtain ⟨n, hn⟩ : ∃ n, μ (s (u n)) < L := ((tendsto_order.1 A).2 _ hL).exists
  have : Ioc a (u n) ∈ 𝓝[>] a := Ioc_mem_nhdsWithin_Ioi ⟨le_rfl, u_pos n⟩
  filter_upwards [this]with r hr using lt_of_le_of_lt (measure_mono (hm _ _ hr.1 hr.2)) hn
#align measure_theory.tendsto_measure_bInter_gt MeasureTheory.tendsto_measure_bInter_gt

/-- One direction of the **Borel-Cantelli lemma**: if (sᵢ) is a sequence of sets such
that `∑ μ sᵢ` is finite, then the limit superior of the `sᵢ` is a null set. -/
theorem measure_limsup_eq_zero {s : ℕ → Set α} (hs : (∑' i, μ (s i)) ≠ ∞) :
    μ (limsup s atTop) = 0 :=
  by
  -- First we replace the sequence `sₙ` with a sequence of measurable sets `tₙ ⊇ sₙ` of the same
  -- measure.
  set t : ℕ → Set α := fun n => to_measurable μ (s n)
  have ht : (∑' i, μ (t i)) ≠ ∞ := by simpa only [t, measure_to_measurable] using hs
  suffices μ (limsup t at_top) = 0
    by
    have A : s ≤ t := fun n => subset_to_measurable μ (s n)
    -- TODO default args fail
    exact
      measure_mono_null
        (limsup_le_limsup (eventually_of_forall (pi.le_def.mp A)) is_cobounded_le_of_bot
          is_bounded_le_of_top)
        this
  -- Next we unfold `limsup` for sets and replace equality with an inequality
  simp only [limsup_eq_infi_supr_of_nat', Set.infᵢ_eq_interᵢ, Set.supᵢ_eq_unionᵢ, ←
    nonpos_iff_eq_zero]
  -- Finally, we estimate `μ (⋃ i, t (i + n))` by `∑ i', μ (t (i + n))`
  refine'
    le_of_tendsto_of_tendsto'
      (tendsto_measure_Inter
        (fun i => MeasurableSet.unionᵢ fun b => measurable_set_to_measurable _ _) _
        ⟨0, ne_top_of_le_ne_top ht (measure_Union_le t)⟩)
      (ENNReal.tendsto_sum_nat_add (μ ∘ t) ht) fun n => measure_Union_le _
  intro n m hnm x
  simp only [Set.mem_unionᵢ]
  exact fun ⟨i, hi⟩ => ⟨i + (m - n), by simpa only [add_assoc, tsub_add_cancel_of_le hnm] using hi⟩
#align measure_theory.measure_limsup_eq_zero MeasureTheory.measure_limsup_eq_zero

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic filter.is_bounded_default -/
theorem measure_liminf_eq_zero {s : ℕ → Set α} (h : (∑' i, μ (s i)) ≠ ⊤) : μ (liminf s atTop) = 0 :=
  by
  rw [← le_zero_iff]
  have : liminf s at_top ≤ limsup s at_top :=
    liminf_le_limsup
      (by
        run_tac
          is_bounded_default)
      (by
        run_tac
          is_bounded_default)
  exact (μ.mono this).trans (by simp [measure_limsup_eq_zero h])
#align measure_theory.measure_liminf_eq_zero MeasureTheory.measure_liminf_eq_zero

theorem limsup_ae_eq_of_forall_ae_eq (s : ℕ → Set α) {t : Set α}
    (h : ∀ n, s n =ᵐ[μ] t) :-- Need `@` below because of diamond; see gh issue #16932
        @limsup
        (Set α) ℕ _ s atTop =ᵐ[μ]
      t :=
  by
  simp_rw [ae_eq_set] at h⊢
  constructor
  · rw [at_top.limsup_sdiff s t]
    apply measure_limsup_eq_zero
    simp [h]
  · rw [at_top.sdiff_limsup s t]
    apply measure_liminf_eq_zero
    simp [h]
#align measure_theory.limsup_ae_eq_of_forall_ae_eq MeasureTheory.limsup_ae_eq_of_forall_ae_eq

theorem liminf_ae_eq_of_forall_ae_eq (s : ℕ → Set α) {t : Set α}
    (h : ∀ n, s n =ᵐ[μ] t) :-- Need `@` below because of diamond; see gh issue #16932
        @liminf
        (Set α) ℕ _ s atTop =ᵐ[μ]
      t :=
  by
  simp_rw [ae_eq_set] at h⊢
  constructor
  · rw [at_top.liminf_sdiff s t]
    apply measure_liminf_eq_zero
    simp [h]
  · rw [at_top.sdiff_liminf s t]
    apply measure_limsup_eq_zero
    simp [h]
#align measure_theory.liminf_ae_eq_of_forall_ae_eq MeasureTheory.liminf_ae_eq_of_forall_ae_eq

theorem measure_if {x : β} {t : Set β} {s : Set α} :
    μ (if x ∈ t then s else ∅) = indicator t (fun _ => μ s) x := by split_ifs <;> simp [h]
#align measure_theory.measure_if MeasureTheory.measure_if

end

section OuterMeasure

variable [ms : MeasurableSpace α] {s t : Set α}

include ms

/-- Obtain a measure by giving an outer measure where all sets in the σ-algebra are
  Carathéodory measurable. -/
def OuterMeasure.toMeasure (m : OuterMeasure α) (h : ms ≤ m.caratheodory) : Measure α :=
  Measure.ofMeasurable (fun s _ => m s) m.Empty fun f hf hd =>
    m.unionᵢ_eq_of_caratheodory (fun i => h _ (hf i)) hd
#align measure_theory.outer_measure.to_measure MeasureTheory.OuterMeasure.toMeasure

theorem le_toOuterMeasure_caratheodory (μ : Measure α) : ms ≤ μ.toOuterMeasure.caratheodory :=
  fun s hs t => (measure_inter_add_diff _ hs).symm
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
    (hs : NullMeasurableSet s (m.toMeasure h)) : m.toMeasure h s = m s :=
  by
  refine' le_antisymm _ (le_to_measure_apply _ _ _)
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, hts, htm, heq⟩
  calc
    m.to_measure h s = m.to_measure h t := measure_congr HEq.symm
    _ = m t := (to_measure_apply m h htm)
    _ ≤ m s := m.mono hts
    
#align measure_theory.to_measure_apply₀ MeasureTheory.toMeasure_apply₀

@[simp]
theorem toOuterMeasure_toMeasure {μ : Measure α} :
    μ.toOuterMeasure.toMeasure (le_toOuterMeasure_caratheodory _) = μ :=
  Measure.ext fun s => μ.toOuterMeasure.trim_eq
#align measure_theory.to_outer_measure_to_measure MeasureTheory.toOuterMeasure_toMeasure

@[simp]
theorem boundedBy_measure (μ : Measure α) : OuterMeasure.boundedBy μ = μ.toOuterMeasure :=
  μ.toOuterMeasure.boundedBy_eq_self
#align measure_theory.bounded_by_measure MeasureTheory.boundedBy_measure

end OuterMeasure

variable {m0 : MeasurableSpace α} [MeasurableSpace β] [MeasurableSpace γ]

variable {μ μ₁ μ₂ μ₃ ν ν' ν₁ ν₂ : Measure α} {s s' t : Set α}

namespace Measure

/-- If `u` is a superset of `t` with the same (finite) measure (both sets possibly non-measurable),
then for any measurable set `s` one also has `μ (t ∩ s) = μ (u ∩ s)`. -/
theorem measure_inter_eq_of_measure_eq {s t u : Set α} (hs : MeasurableSet s) (h : μ t = μ u)
    (htu : t ⊆ u) (ht_ne_top : μ t ≠ ∞) : μ (t ∩ s) = μ (u ∩ s) :=
  by
  rw [h] at ht_ne_top
  refine' le_antisymm (measure_mono (inter_subset_inter_left _ htu)) _
  have A : μ (u ∩ s) + μ (u \ s) ≤ μ (t ∩ s) + μ (u \ s) :=
    calc
      μ (u ∩ s) + μ (u \ s) = μ u := measure_inter_add_diff _ hs
      _ = μ t := h.symm
      _ = μ (t ∩ s) + μ (t \ s) := (measure_inter_add_diff _ hs).symm
      _ ≤ μ (t ∩ s) + μ (u \ s) :=
        add_le_add le_rfl (measure_mono (diff_subset_diff htu subset.rfl))
      
  have B : μ (u \ s) ≠ ∞ := (lt_of_le_of_lt (measure_mono (diff_subset _ _)) ht_ne_top.lt_top).Ne
  exact ENNReal.le_of_add_le_add_right B A
#align measure_theory.measure.measure_inter_eq_of_measure_eq MeasureTheory.Measure.measure_inter_eq_of_measure_eq

/-- The measurable superset `to_measurable μ t` of `t` (which has the same measure as `t`)
satisfies, for any measurable set `s`, the equality `μ (to_measurable μ t ∩ s) = μ (u ∩ s)`.
Here, we require that the measure of `t` is finite. The conclusion holds without this assumption
when the measure is sigma_finite, see `measure_to_measurable_inter_of_sigma_finite`. -/
theorem measure_toMeasurable_inter {s t : Set α} (hs : MeasurableSet s) (ht : μ t ≠ ∞) :
    μ (toMeasurable μ t ∩ s) = μ (t ∩ s) :=
  (measure_inter_eq_of_measure_eq hs (measure_toMeasurable t).symm (subset_toMeasurable μ t)
      ht).symm
#align measure_theory.measure.measure_to_measurable_inter MeasureTheory.Measure.measure_toMeasurable_inter

/-! ### The `ℝ≥0∞`-module of measures -/


instance [MeasurableSpace α] : Zero (Measure α) :=
  ⟨{  toOuterMeasure := 0
      m_unionᵢ := fun f hf hd => tsum_zero.symm
      trimmed := OuterMeasure.trim_zero }⟩

@[simp]
theorem zero_toOuterMeasure {m : MeasurableSpace α} : (0 : Measure α).toOuterMeasure = 0 :=
  rfl
#align measure_theory.measure.zero_to_outer_measure MeasureTheory.Measure.zero_toOuterMeasure

@[simp, norm_cast]
theorem coe_zero {m : MeasurableSpace α} : ⇑(0 : Measure α) = 0 :=
  rfl
#align measure_theory.measure.coe_zero MeasureTheory.Measure.coe_zero

instance [IsEmpty α] {m : MeasurableSpace α} : Subsingleton (Measure α) :=
  ⟨fun μ ν => by
    ext1 s hs
    simp only [eq_empty_of_is_empty s, measure_empty]⟩

theorem eq_zero_of_isEmpty [IsEmpty α] {m : MeasurableSpace α} (μ : Measure α) : μ = 0 :=
  Subsingleton.elim μ 0
#align measure_theory.measure.eq_zero_of_is_empty MeasureTheory.Measure.eq_zero_of_isEmpty

instance [MeasurableSpace α] : Inhabited (Measure α) :=
  ⟨0⟩

instance [MeasurableSpace α] : Add (Measure α) :=
  ⟨fun μ₁ μ₂ =>
    { toOuterMeasure := μ₁.toOuterMeasure + μ₂.toOuterMeasure
      m_unionᵢ := fun s hs hd =>
        show μ₁ (⋃ i, s i) + μ₂ (⋃ i, s i) = ∑' i, μ₁ (s i) + μ₂ (s i) by
          rw [ENNReal.tsum_add, measure_Union hd hs, measure_Union hd hs]
      trimmed := by rw [outer_measure.trim_add, μ₁.trimmed, μ₂.trimmed] }⟩

@[simp]
theorem add_toOuterMeasure {m : MeasurableSpace α} (μ₁ μ₂ : Measure α) :
    (μ₁ + μ₂).toOuterMeasure = μ₁.toOuterMeasure + μ₂.toOuterMeasure :=
  rfl
#align measure_theory.measure.add_to_outer_measure MeasureTheory.Measure.add_toOuterMeasure

@[simp, norm_cast]
theorem coe_add {m : MeasurableSpace α} (μ₁ μ₂ : Measure α) : ⇑(μ₁ + μ₂) = μ₁ + μ₂ :=
  rfl
#align measure_theory.measure.coe_add MeasureTheory.Measure.coe_add

theorem add_apply {m : MeasurableSpace α} (μ₁ μ₂ : Measure α) (s : Set α) :
    (μ₁ + μ₂) s = μ₁ s + μ₂ s :=
  rfl
#align measure_theory.measure.add_apply MeasureTheory.Measure.add_apply

section SMul

variable [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]

variable [SMul R' ℝ≥0∞] [IsScalarTower R' ℝ≥0∞ ℝ≥0∞]

instance [MeasurableSpace α] : SMul R (Measure α) :=
  ⟨fun c μ =>
    { toOuterMeasure := c • μ.toOuterMeasure
      m_unionᵢ := fun s hs hd =>
        by
        rw [← smul_one_smul ℝ≥0∞ c (_ : outer_measure α)]
        dsimp
        simp_rw [measure_Union hd hs, ENNReal.tsum_mul_left]
      trimmed := by rw [outer_measure.trim_smul, μ.trimmed] }⟩

@[simp]
theorem smul_toOuterMeasure {m : MeasurableSpace α} (c : R) (μ : Measure α) :
    (c • μ).toOuterMeasure = c • μ.toOuterMeasure :=
  rfl
#align measure_theory.measure.smul_to_outer_measure MeasureTheory.Measure.smul_toOuterMeasure

@[simp, norm_cast]
theorem coe_smul {m : MeasurableSpace α} (c : R) (μ : Measure α) : ⇑(c • μ) = c • μ :=
  rfl
#align measure_theory.measure.coe_smul MeasureTheory.Measure.coe_smul

@[simp]
theorem smul_apply {m : MeasurableSpace α} (c : R) (μ : Measure α) (s : Set α) :
    (c • μ) s = c • μ s :=
  rfl
#align measure_theory.measure.smul_apply MeasureTheory.Measure.smul_apply

instance [SMulCommClass R R' ℝ≥0∞] [MeasurableSpace α] : SMulCommClass R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_comm _ _ _⟩

instance [SMul R R'] [IsScalarTower R R' ℝ≥0∞] [MeasurableSpace α] :
    IsScalarTower R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_assoc _ _ _⟩

instance [SMul Rᵐᵒᵖ ℝ≥0∞] [IsCentralScalar R ℝ≥0∞] [MeasurableSpace α] :
    IsCentralScalar R (Measure α) :=
  ⟨fun _ _ => ext fun _ _ => op_smul_eq_smul _ _⟩

end SMul

instance [Monoid R] [MulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [MeasurableSpace α] :
    MulAction R (Measure α) :=
  Injective.mulAction _ toOuterMeasure_injective smul_toOuterMeasure

instance addCommMonoid [MeasurableSpace α] : AddCommMonoid (Measure α) :=
  toOuterMeasure_injective.AddCommMonoid toOuterMeasure zero_toOuterMeasure add_toOuterMeasure
    fun _ _ => smul_toOuterMeasure _ _
#align measure_theory.measure.add_comm_monoid MeasureTheory.Measure.addCommMonoid

/-- Coercion to function as an additive monoid homomorphism. -/
def coeAddHom {m : MeasurableSpace α} : Measure α →+ Set α → ℝ≥0∞ :=
  ⟨coeFn, coe_zero, coe_add⟩
#align measure_theory.measure.coe_add_hom MeasureTheory.Measure.coeAddHom

@[simp]
theorem coe_finset_sum {m : MeasurableSpace α} (I : Finset ι) (μ : ι → Measure α) :
    ⇑(∑ i in I, μ i) = ∑ i in I, μ i :=
  (@coeAddHom α m).map_sum _ _
#align measure_theory.measure.coe_finset_sum MeasureTheory.Measure.coe_finset_sum

theorem finset_sum_apply {m : MeasurableSpace α} (I : Finset ι) (μ : ι → Measure α) (s : Set α) :
    (∑ i in I, μ i) s = ∑ i in I, μ i s := by rw [coe_finset_sum, Finset.sum_apply]
#align measure_theory.measure.finset_sum_apply MeasureTheory.Measure.finset_sum_apply

instance [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [MeasurableSpace α] :
    DistribMulAction R (Measure α) :=
  Injective.distribMulAction ⟨toOuterMeasure, zero_toOuterMeasure, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure

instance [Semiring R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [MeasurableSpace α] :
    Module R (Measure α) :=
  Injective.module R ⟨toOuterMeasure, zero_toOuterMeasure, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure

@[simp]
theorem coe_nNReal_smul_apply {m : MeasurableSpace α} (c : ℝ≥0) (μ : Measure α) (s : Set α) :
    (c • μ) s = c * μ s :=
  rfl
#align measure_theory.measure.coe_nnreal_smul_apply MeasureTheory.Measure.coe_nNReal_smul_apply

theorem ae_smul_measure_iff {p : α → Prop} {c : ℝ≥0∞} (hc : c ≠ 0) :
    (∀ᵐ x ∂c • μ, p x) ↔ ∀ᵐ x ∂μ, p x := by simp [ae_iff, hc]
#align measure_theory.measure.ae_smul_measure_iff MeasureTheory.Measure.ae_smul_measure_iff

theorem measure_eq_left_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t)
    (h'' : (μ + ν) s = (μ + ν) t) : μ s = μ t :=
  by
  refine' le_antisymm (measure_mono h') _
  have : μ t + ν t ≤ μ s + ν t :=
    calc
      μ t + ν t = μ s + ν s := h''.symm
      _ ≤ μ s + ν t := add_le_add le_rfl (measure_mono h')
      
  apply ENNReal.le_of_add_le_add_right _ this
  simp only [not_or, ENNReal.add_eq_top, Pi.add_apply, Ne.def, coe_add] at h
  exact h.2
#align measure_theory.measure.measure_eq_left_of_subset_of_measure_add_eq MeasureTheory.Measure.measure_eq_left_of_subset_of_measure_add_eq

theorem measure_eq_right_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t)
    (h'' : (μ + ν) s = (μ + ν) t) : ν s = ν t :=
  by
  rw [add_comm] at h'' h
  exact measure_eq_left_of_subset_of_measure_add_eq h h' h''
#align measure_theory.measure.measure_eq_right_of_subset_of_measure_add_eq MeasureTheory.Measure.measure_eq_right_of_subset_of_measure_add_eq

theorem measure_toMeasurable_add_inter_left {s t : Set α} (hs : MeasurableSet s)
    (ht : (μ + ν) t ≠ ∞) : μ (toMeasurable (μ + ν) t ∩ s) = μ (t ∩ s) :=
  by
  refine' (measure_inter_eq_of_measure_eq hs _ (subset_to_measurable _ _) _).symm
  · refine'
      measure_eq_left_of_subset_of_measure_add_eq _ (subset_to_measurable _ _)
        (measure_to_measurable t).symm
    rwa [measure_to_measurable t]
  · simp only [not_or, ENNReal.add_eq_top, Pi.add_apply, Ne.def, coe_add] at ht
    exact ht.1
#align measure_theory.measure.measure_to_measurable_add_inter_left MeasureTheory.Measure.measure_toMeasurable_add_inter_left

theorem measure_toMeasurable_add_inter_right {s t : Set α} (hs : MeasurableSet s)
    (ht : (μ + ν) t ≠ ∞) : ν (toMeasurable (μ + ν) t ∩ s) = ν (t ∩ s) :=
  by
  rw [add_comm] at ht⊢
  exact measure_to_measurable_add_inter_left hs ht
#align measure_theory.measure.measure_to_measurable_add_inter_right MeasureTheory.Measure.measure_toMeasurable_add_inter_right

/-! ### The complete lattice of measures -/


/-- Measures are partially ordered.

The definition of less equal here is equivalent to the definition without the
measurable set condition, and this is shown by `measure.le_iff'`. It is defined
this way since, to prove `μ ≤ ν`, we may simply `intros s hs` instead of rewriting followed
by `intros s hs`. -/
instance [MeasurableSpace α] : PartialOrder (Measure α)
    where
  le m₁ m₂ := ∀ s, MeasurableSet s → m₁ s ≤ m₂ s
  le_refl m s hs := le_rfl
  le_trans m₁ m₂ m₃ h₁ h₂ s hs := le_trans (h₁ s hs) (h₂ s hs)
  le_antisymm m₁ m₂ h₁ h₂ := ext fun s hs => le_antisymm (h₁ s hs) (h₂ s hs)

theorem le_iff : μ₁ ≤ μ₂ ↔ ∀ s, MeasurableSet s → μ₁ s ≤ μ₂ s :=
  Iff.rfl
#align measure_theory.measure.le_iff MeasureTheory.Measure.le_iff

theorem toOuterMeasure_le : μ₁.toOuterMeasure ≤ μ₂.toOuterMeasure ↔ μ₁ ≤ μ₂ := by
  rw [← μ₂.trimmed, outer_measure.le_trim_iff] <;> rfl
#align measure_theory.measure.to_outer_measure_le MeasureTheory.Measure.toOuterMeasure_le

theorem le_iff' : μ₁ ≤ μ₂ ↔ ∀ s, μ₁ s ≤ μ₂ s :=
  toOuterMeasure_le.symm
#align measure_theory.measure.le_iff' MeasureTheory.Measure.le_iff'

theorem lt_iff : μ < ν ↔ μ ≤ ν ∧ ∃ s, MeasurableSet s ∧ μ s < ν s :=
  lt_iff_le_not_le.trans <|
    and_congr Iff.rfl <| by simp only [le_iff, not_forall, not_le, exists_prop]
#align measure_theory.measure.lt_iff MeasureTheory.Measure.lt_iff

theorem lt_iff' : μ < ν ↔ μ ≤ ν ∧ ∃ s, μ s < ν s :=
  lt_iff_le_not_le.trans <| and_congr Iff.rfl <| by simp only [le_iff', not_forall, not_le]
#align measure_theory.measure.lt_iff' MeasureTheory.Measure.lt_iff'

instance covariant_add_le [MeasurableSpace α] :
    CovariantClass (Measure α) (Measure α) (· + ·) (· ≤ ·) :=
  ⟨fun ν μ₁ μ₂ hμ s hs => add_le_add_left (hμ s hs) _⟩
#align measure_theory.measure.covariant_add_le MeasureTheory.Measure.covariant_add_le

protected theorem le_add_left (h : μ ≤ ν) : μ ≤ ν' + ν := fun s hs => le_add_left (h s hs)
#align measure_theory.measure.le_add_left MeasureTheory.Measure.le_add_left

protected theorem le_add_right (h : μ ≤ ν) : μ ≤ ν + ν' := fun s hs => le_add_right (h s hs)
#align measure_theory.measure.le_add_right MeasureTheory.Measure.le_add_right

section Inf

variable {m : Set (Measure α)}

theorem infₛ_caratheodory (s : Set α) (hs : MeasurableSet s) :
    measurable_set[(infₛ (toOuterMeasure '' m)).caratheodory] s :=
  by
  rw [outer_measure.Inf_eq_bounded_by_Inf_gen]
  refine' outer_measure.bounded_by_caratheodory fun t => _
  simp only [outer_measure.Inf_gen, le_infᵢ_iff, ball_image_iff, coe_to_outer_measure,
    measure_eq_infi t]
  intro μ hμ u htu hu
  have hm : ∀ {s t}, s ⊆ t → outer_measure.Inf_gen (to_outer_measure '' m) s ≤ μ t :=
    by
    intro s t hst
    rw [outer_measure.Inf_gen_def]
    refine' infᵢ_le_of_le μ.to_outer_measure (infᵢ_le_of_le (mem_image_of_mem _ hμ) _)
    rw [to_outer_measure_apply]
    refine' measure_mono hst
  rw [← measure_inter_add_diff u hs]
  refine' add_le_add (hm <| inter_subset_inter_left _ htu) (hm <| diff_subset_diff_left htu)
#align measure_theory.measure.Inf_caratheodory MeasureTheory.Measure.infₛ_caratheodory

instance [MeasurableSpace α] : InfSet (Measure α) :=
  ⟨fun m => (infₛ (toOuterMeasure '' m)).toMeasure <| infₛ_caratheodory⟩

theorem infₛ_apply (hs : MeasurableSet s) : infₛ m s = infₛ (toOuterMeasure '' m) s :=
  toMeasure_apply _ _ hs
#align measure_theory.measure.Inf_apply MeasureTheory.Measure.infₛ_apply

private theorem measure_Inf_le (h : μ ∈ m) : infₛ m ≤ μ :=
  have : infₛ (toOuterMeasure '' m) ≤ μ.toOuterMeasure := infₛ_le (mem_image_of_mem _ h)
  fun s hs => by rw [infₛ_apply hs, ← to_outer_measure_apply] <;> exact this s
#align measure_theory.measure.measure_Inf_le measure_theory.measure.measure_Inf_le

private theorem measure_le_Inf (h : ∀ μ' ∈ m, μ ≤ μ') : μ ≤ infₛ m :=
  have : μ.toOuterMeasure ≤ infₛ (toOuterMeasure '' m) :=
    le_infₛ <| ball_image_of_ball fun μ hμ => toOuterMeasure_le.2 <| h _ hμ
  fun s hs => by rw [infₛ_apply hs, ← to_outer_measure_apply] <;> exact this s
#align measure_theory.measure.measure_le_Inf measure_theory.measure.measure_le_Inf

instance [MeasurableSpace α] : CompleteSemilatticeInf (Measure α) :=
  { (by infer_instance : PartialOrder (Measure α)),
    (by infer_instance :
      InfSet (Measure α)) with
    inf_le := fun s a => measure_infₛ_le
    le_inf := fun s a => measure_le_infₛ }

instance [MeasurableSpace α] : CompleteLattice (Measure α) :=
  {/- Adding an explicit `top` makes `leanchecker` fail, see lean#364, disable for now
      
        top := (⊤ : outer_measure α).to_measure (by rw [outer_measure.top_caratheodory]; exact le_top),
        le_top := λ a s hs,
          by cases s.eq_empty_or_nonempty with h  h;
            simp [h, to_measure_apply ⊤ _ hs, outer_measure.top_apply],
      -/
      completeLatticeOfCompleteSemilatticeInf
      (Measure α) with
    bot := 0
    bot_le := fun a s hs => bot_le }

end Inf

@[simp]
theorem top_add : ⊤ + μ = ⊤ :=
  top_unique <| Measure.le_add_right le_rfl
#align measure_theory.measure.top_add MeasureTheory.Measure.top_add

@[simp]
theorem add_top : μ + ⊤ = ⊤ :=
  top_unique <| Measure.le_add_left le_rfl
#align measure_theory.measure.add_top MeasureTheory.Measure.add_top

protected theorem zero_le {m0 : MeasurableSpace α} (μ : Measure α) : 0 ≤ μ :=
  bot_le
#align measure_theory.measure.zero_le MeasureTheory.Measure.zero_le

theorem nonpos_iff_eq_zero' : μ ≤ 0 ↔ μ = 0 :=
  μ.zero_le.le_iff_eq
#align measure_theory.measure.nonpos_iff_eq_zero' MeasureTheory.Measure.nonpos_iff_eq_zero'

@[simp]
theorem measure_univ_eq_zero : μ univ = 0 ↔ μ = 0 :=
  ⟨fun h => bot_unique fun s hs => trans_rel_left (· ≤ ·) (measure_mono (subset_univ s)) h, fun h =>
    h.symm ▸ rfl⟩
#align measure_theory.measure.measure_univ_eq_zero MeasureTheory.Measure.measure_univ_eq_zero

theorem measure_univ_ne_zero : μ univ ≠ 0 ↔ μ ≠ 0 :=
  measure_univ_eq_zero.Not
#align measure_theory.measure.measure_univ_ne_zero MeasureTheory.Measure.measure_univ_ne_zero

@[simp]
theorem measure_univ_pos : 0 < μ univ ↔ μ ≠ 0 :=
  pos_iff_ne_zero.trans measure_univ_ne_zero
#align measure_theory.measure.measure_univ_pos MeasureTheory.Measure.measure_univ_pos

/-! ### Pushforward and pullback -/


/-- Lift a linear map between `outer_measure` spaces such that for each measure `μ` every measurable
set is caratheodory-measurable w.r.t. `f μ` to a linear map between `measure` spaces. -/
def liftLinear {m0 : MeasurableSpace α} (f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β)
    (hf : ∀ μ : Measure α, ‹_› ≤ (f μ.toOuterMeasure).caratheodory) : Measure α →ₗ[ℝ≥0∞] Measure β
    where
  toFun μ := (f μ.toOuterMeasure).toMeasure (hf μ)
  map_add' μ₁ μ₂ := ext fun s hs => by simp [hs]
  map_smul' c μ := ext fun s hs => by simp [hs]
#align measure_theory.measure.lift_linear MeasureTheory.Measure.liftLinear

@[simp]
theorem liftLinear_apply {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) {s : Set β}
    (hs : MeasurableSet s) : liftLinear f hf μ s = f μ.toOuterMeasure s :=
  toMeasure_apply _ _ hs
#align measure_theory.measure.lift_linear_apply MeasureTheory.Measure.liftLinear_apply

theorem le_liftLinear_apply {f : OuterMeasure α →ₗ[ℝ≥0∞] OuterMeasure β} (hf) (s : Set β) :
    f μ.toOuterMeasure s ≤ liftLinear f hf μ s :=
  le_toMeasure_apply _ _ s
#align measure_theory.measure.le_lift_linear_apply MeasureTheory.Measure.le_liftLinear_apply

/-- The pushforward of a measure as a linear map. It is defined to be `0` if `f` is not
a measurable function. -/
def mapₗ [MeasurableSpace α] (f : α → β) : Measure α →ₗ[ℝ≥0∞] Measure β :=
  if hf : Measurable f then
    liftLinear (OuterMeasure.map f) fun μ s hs t =>
      le_toOuterMeasure_caratheodory μ _ (hf hs) (f ⁻¹' t)
  else 0
#align measure_theory.measure.mapₗ MeasureTheory.Measure.mapₗ

theorem mapₗ_congr {f g : α → β} (hf : Measurable f) (hg : Measurable g) (h : f =ᵐ[μ] g) :
    mapₗ f μ = mapₗ g μ := by
  ext1 s hs
  simpa only [mapₗ, hf, hg, hs, dif_pos, lift_linear_apply, outer_measure.map_apply,
    coe_to_outer_measure] using measure_congr (h.preimage s)
#align measure_theory.measure.mapₗ_congr MeasureTheory.Measure.mapₗ_congr

/-- The pushforward of a measure. It is defined to be `0` if `f` is not an almost everywhere
measurable function. -/
irreducible_def map [MeasurableSpace α] (f : α → β) (μ : Measure α) : Measure β :=
  if hf : AeMeasurable f μ then mapₗ (hf.mk f) μ else 0
#align measure_theory.measure.map MeasureTheory.Measure.map

include m0

theorem mapₗ_mk_apply_of_aeMeasurable {f : α → β} (hf : AeMeasurable f μ) :
    mapₗ (hf.mk f) μ = map f μ := by simp [map, hf]
#align measure_theory.measure.mapₗ_mk_apply_of_ae_measurable MeasureTheory.Measure.mapₗ_mk_apply_of_aeMeasurable

theorem mapₗ_apply_of_measurable {f : α → β} (hf : Measurable f) (μ : Measure α) :
    mapₗ f μ = map f μ :=
  by
  simp only [← mapₗ_mk_apply_of_ae_measurable hf.ae_measurable]
  exact mapₗ_congr hf hf.ae_measurable.measurable_mk hf.ae_measurable.ae_eq_mk
#align measure_theory.measure.mapₗ_apply_of_measurable MeasureTheory.Measure.mapₗ_apply_of_measurable

@[simp]
theorem map_add (μ ν : Measure α) {f : α → β} (hf : Measurable f) :
    (μ + ν).map f = μ.map f + ν.map f := by simp [← mapₗ_apply_of_measurable hf]
#align measure_theory.measure.map_add MeasureTheory.Measure.map_add

@[simp]
theorem map_zero (f : α → β) : (0 : Measure α).map f = 0 := by
  by_cases hf : AeMeasurable f (0 : Measure α) <;> simp [map, hf]
#align measure_theory.measure.map_zero MeasureTheory.Measure.map_zero

theorem map_of_not_aeMeasurable {f : α → β} {μ : Measure α} (hf : ¬AeMeasurable f μ) :
    μ.map f = 0 := by simp [map, hf]
#align measure_theory.measure.map_of_not_ae_measurable MeasureTheory.Measure.map_of_not_aeMeasurable

theorem map_congr {f g : α → β} (h : f =ᵐ[μ] g) : Measure.map f μ = Measure.map g μ :=
  by
  by_cases hf : AeMeasurable f μ
  · have hg : AeMeasurable g μ := hf.congr h
    simp only [← mapₗ_mk_apply_of_ae_measurable hf, ← mapₗ_mk_apply_of_ae_measurable hg]
    exact
      mapₗ_congr hf.measurable_mk hg.measurable_mk (hf.ae_eq_mk.symm.trans (h.trans hg.ae_eq_mk))
  · have hg : ¬AeMeasurable g μ := by simpa [← aeMeasurable_congr h] using hf
    simp [map_of_not_ae_measurable, hf, hg]
#align measure_theory.measure.map_congr MeasureTheory.Measure.map_congr

@[simp]
protected theorem map_smul (c : ℝ≥0∞) (μ : Measure α) (f : α → β) : (c • μ).map f = c • μ.map f :=
  by
  rcases eq_or_ne c 0 with (rfl | hc); · simp
  by_cases hf : AeMeasurable f μ
  · have hfc : AeMeasurable f (c • μ) :=
      ⟨hf.mk f, hf.measurable_mk, (ae_smul_measure_iff hc).2 hf.ae_eq_mk⟩
    simp only [← mapₗ_mk_apply_of_ae_measurable hf, ← mapₗ_mk_apply_of_ae_measurable hfc,
      LinearMap.map_smulₛₗ, RingHom.id_apply]
    congr 1
    apply mapₗ_congr hfc.measurable_mk hf.measurable_mk
    exact eventually_eq.trans ((ae_smul_measure_iff hc).1 hfc.ae_eq_mk.symm) hf.ae_eq_mk
  · have hfc : ¬AeMeasurable f (c • μ) := by
      intro hfc
      exact hf ⟨hfc.mk f, hfc.measurable_mk, (ae_smul_measure_iff hc).1 hfc.ae_eq_mk⟩
    simp [map_of_not_ae_measurable hf, map_of_not_ae_measurable hfc]
#align measure_theory.measure.map_smul MeasureTheory.Measure.map_smul

@[simp]
protected theorem map_smul_nNReal (c : ℝ≥0) (μ : Measure α) (f : α → β) :
    (c • μ).map f = c • μ.map f :=
  μ.map_smul (c : ℝ≥0∞) f
#align measure_theory.measure.map_smul_nnreal MeasureTheory.Measure.map_smul_nNReal

/-- We can evaluate the pushforward on measurable sets. For non-measurable sets, see
  `measure_theory.measure.le_map_apply` and `measurable_equiv.map_apply`. -/
@[simp]
theorem map_apply_of_aeMeasurable {f : α → β} (hf : AeMeasurable f μ) {s : Set β}
    (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s) := by
  simpa only [mapₗ, hf.measurable_mk, hs, dif_pos, lift_linear_apply, outer_measure.map_apply,
    coe_to_outer_measure, ← mapₗ_mk_apply_of_ae_measurable hf] using
    measure_congr (hf.ae_eq_mk.symm.preimage s)
#align measure_theory.measure.map_apply_of_ae_measurable MeasureTheory.Measure.map_apply_of_aeMeasurable

@[simp]
theorem map_apply {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    μ.map f s = μ (f ⁻¹' s) :=
  map_apply_of_aeMeasurable hf.AeMeasurable hs
#align measure_theory.measure.map_apply MeasureTheory.Measure.map_apply

theorem map_toOuterMeasure {f : α → β} (hf : AeMeasurable f μ) :
    (μ.map f).toOuterMeasure = (OuterMeasure.map f μ.toOuterMeasure).trim :=
  by
  rw [← trimmed, outer_measure.trim_eq_trim_iff]
  intro s hs
  rw [coe_to_outer_measure, map_apply_of_ae_measurable hf hs, outer_measure.map_apply,
    coe_to_outer_measure]
#align measure_theory.measure.map_to_outer_measure MeasureTheory.Measure.map_toOuterMeasure

@[simp]
theorem map_id : map id μ = μ :=
  ext fun s => map_apply measurable_id
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
theorem map_mono {f : α → β} (h : μ ≤ ν) (hf : Measurable f) : μ.map f ≤ ν.map f := fun s hs => by
  simp [hf.ae_measurable, hs, h _ (hf hs)]
#align measure_theory.measure.map_mono MeasureTheory.Measure.map_mono

/-- Even if `s` is not measurable, we can bound `map f μ s` from below.
  See also `measurable_equiv.map_apply`. -/
theorem le_map_apply {f : α → β} (hf : AeMeasurable f μ) (s : Set β) : μ (f ⁻¹' s) ≤ μ.map f s :=
  calc
    μ (f ⁻¹' s) ≤ μ (f ⁻¹' toMeasurable (μ.map f) s) :=
      measure_mono <| preimage_mono <| subset_toMeasurable _ _
    _ = μ.map f (toMeasurable (μ.map f) s) :=
      (map_apply_of_aeMeasurable hf <| measurableSet_toMeasurable _ _).symm
    _ = μ.map f s := measure_toMeasurable _
    
#align measure_theory.measure.le_map_apply MeasureTheory.Measure.le_map_apply

/-- Even if `s` is not measurable, `map f μ s = 0` implies that `μ (f ⁻¹' s) = 0`. -/
theorem preimage_null_of_map_null {f : α → β} (hf : AeMeasurable f μ) {s : Set β}
    (hs : μ.map f s = 0) : μ (f ⁻¹' s) = 0 :=
  nonpos_iff_eq_zero.mp <| (le_map_apply hf s).trans_eq hs
#align measure_theory.measure.preimage_null_of_map_null MeasureTheory.Measure.preimage_null_of_map_null

theorem tendsto_ae_map {f : α → β} (hf : AeMeasurable f μ) : Tendsto f μ.ae (μ.map f).ae :=
  fun s hs => preimage_null_of_map_null hf hs
#align measure_theory.measure.tendsto_ae_map MeasureTheory.Measure.tendsto_ae_map

omit m0

/-- Pullback of a `measure` as a linear map. If `f` sends each measurable set to a measurable
set, then for each measurable set `s` we have `comapₗ f μ s = μ (f '' s)`.

If the linearity is not needed, please use `comap` instead, which works for a larger class of
functions. -/
def comapₗ [MeasurableSpace α] (f : α → β) : Measure β →ₗ[ℝ≥0∞] Measure α :=
  if hf : Injective f ∧ ∀ s, MeasurableSet s → MeasurableSet (f '' s) then
    liftLinear (OuterMeasure.comap f) fun μ s hs t =>
      by
      simp only [coe_to_outer_measure, outer_measure.comap_apply, image_inter hf.1, image_diff hf.1]
      apply le_to_outer_measure_caratheodory
      exact hf.2 s hs
  else 0
#align measure_theory.measure.comapₗ MeasureTheory.Measure.comapₗ

theorem comapₗ_apply {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β)
    (hfi : Injective f) (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β)
    (hs : MeasurableSet s) : comapₗ f μ s = μ (f '' s) :=
  by
  rw [comapₗ, dif_pos, lift_linear_apply _ hs, outer_measure.comap_apply, coe_to_outer_measure]
  exact ⟨hfi, hf⟩
#align measure_theory.measure.comapₗ_apply MeasureTheory.Measure.comapₗ_apply

/-- Pullback of a `measure`. If `f` sends each measurable set to a null-measurable set,
then for each measurable set `s` we have `comap f μ s = μ (f '' s)`. -/
def comap [MeasurableSpace α] (f : α → β) (μ : Measure β) : Measure α :=
  if hf : Injective f ∧ ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ then
    (OuterMeasure.comap f μ.toOuterMeasure).toMeasure fun s hs t =>
      by
      simp only [coe_to_outer_measure, outer_measure.comap_apply, image_inter hf.1, image_diff hf.1]
      exact (measure_inter_add_diff₀ _ (hf.2 s hs)).symm
  else 0
#align measure_theory.measure.comap MeasureTheory.Measure.comap

theorem comap_apply₀ [MeasurableSpace α] (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    (hs : NullMeasurableSet s (comap f μ)) : comap f μ s = μ (f '' s) :=
  by
  rw [comap, dif_pos (And.intro hfi hf)] at hs⊢
  rw [to_measure_apply₀ _ _ hs, outer_measure.comap_apply, coe_to_outer_measure]
#align measure_theory.measure.comap_apply₀ MeasureTheory.Measure.comap_apply₀

theorem le_comap_apply {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β) (μ : Measure β)
    (hfi : Injective f) (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ) (s : Set α) :
    μ (f '' s) ≤ comap f μ s :=
  by
  rw [comap, dif_pos (And.intro hfi hf)]
  exact le_to_measure_apply _ _ _
#align measure_theory.measure.le_comap_apply MeasureTheory.Measure.le_comap_apply

theorem comap_apply {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β) (hs : MeasurableSet s) :
    comap f μ s = μ (f '' s) :=
  comap_apply₀ f μ hfi (fun s hs => (hf s hs).NullMeasurableSet) hs.NullMeasurableSet
#align measure_theory.measure.comap_apply MeasureTheory.Measure.comap_apply

theorem comapₗ_eq_comap {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β)
    (hfi : Injective f) (hf : ∀ s, MeasurableSet s → MeasurableSet (f '' s)) (μ : Measure β)
    (hs : MeasurableSet s) : comapₗ f μ s = comap f μ s :=
  (comapₗ_apply f hfi hf μ hs).trans (comap_apply f hfi hf μ hs).symm
#align measure_theory.measure.comapₗ_eq_comap MeasureTheory.Measure.comapₗ_eq_comap

theorem measure_image_eq_zero_of_comap_eq_zero {β} [MeasurableSpace α] {mβ : MeasurableSpace β}
    (f : α → β) (μ : Measure β) (hfi : Injective f)
    (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ) {s : Set α} (hs : comap f μ s = 0) :
    μ (f '' s) = 0 :=
  le_antisymm ((le_comap_apply f μ hfi hf s).trans hs.le) (zero_le _)
#align measure_theory.measure.measure_image_eq_zero_of_comap_eq_zero MeasureTheory.Measure.measure_image_eq_zero_of_comap_eq_zero

theorem ae_eq_image_of_ae_eq_comap {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β)
    (μ : Measure β) (hfi : Injective f) (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    {s t : Set α} (hst : s =ᵐ[comap f μ] t) : f '' s =ᵐ[μ] f '' t :=
  by
  rw [eventually_eq, ae_iff] at hst⊢
  have h_eq_α : { a : α | ¬s a = t a } = s \ t ∪ t \ s :=
    by
    ext1 x
    simp only [eq_iff_iff, mem_set_of_eq, mem_union, mem_diff]
    tauto
  have h_eq_β : { a : β | ¬(f '' s) a = (f '' t) a } = f '' s \ f '' t ∪ f '' t \ f '' s :=
    by
    ext1 x
    simp only [eq_iff_iff, mem_set_of_eq, mem_union, mem_diff]
    tauto
  rw [← Set.image_diff hfi, ← Set.image_diff hfi, ← Set.image_union] at h_eq_β
  rw [h_eq_β]
  rw [h_eq_α] at hst
  exact measure_image_eq_zero_of_comap_eq_zero f μ hfi hf hst
#align measure_theory.measure.ae_eq_image_of_ae_eq_comap MeasureTheory.Measure.ae_eq_image_of_ae_eq_comap

theorem NullMeasurableSet.image {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β)
    (μ : Measure β) (hfi : Injective f) (hf : ∀ s, MeasurableSet s → NullMeasurableSet (f '' s) μ)
    {s : Set α} (hs : NullMeasurableSet s (μ.comap f)) : NullMeasurableSet (f '' s) μ :=
  by
  refine' ⟨to_measurable μ (f '' to_measurable (μ.comap f) s), measurable_set_to_measurable _ _, _⟩
  refine' eventually_eq.trans _ (null_measurable_set.to_measurable_ae_eq _).symm
  swap
  · exact hf _ (measurable_set_to_measurable _ _)
  have h : to_measurable (comap f μ) s =ᵐ[comap f μ] s :=
    @null_measurable_set.to_measurable_ae_eq _ _ (μ.comap f : Measure α) s hs
  exact ae_eq_image_of_ae_eq_comap f μ hfi hf h.symm
#align measure_theory.measure.null_measurable_set.image MeasureTheory.Measure.NullMeasurableSet.image

theorem comap_preimage {β} [MeasurableSpace α] {mβ : MeasurableSpace β} (f : α → β) (μ : Measure β)
    {s : Set β} (hf : Injective f) (hf' : Measurable f)
    (h : ∀ t, MeasurableSet t → NullMeasurableSet (f '' t) μ) (hs : MeasurableSet s) :
    μ.comap f (f ⁻¹' s) = μ (s ∩ range f) := by
  rw [comap_apply₀ _ _ hf h (hf' hs).NullMeasurableSet, image_preimage_eq_inter_range]
#align measure_theory.measure.comap_preimage MeasureTheory.Measure.comap_preimage

section Subtype

/-! ### Subtype of a measure space -/


section ComapAnyMeasure

theorem MeasurableSet.nullMeasurableSetSubtypeCoe {t : Set s} (hs : NullMeasurableSet s μ)
    (ht : MeasurableSet t) : NullMeasurableSet ((coe : s → α) '' t) μ :=
  by
  rw [Subtype.measurableSpace, comap_eq_generate_from] at ht
  refine'
    generate_from_induction (fun t : Set s => null_measurable_set (coe '' t) μ)
      { t : Set s | ∃ s' : Set α, MeasurableSet s' ∧ coe ⁻¹' s' = t } _ _ _ _ ht
  · rintro t' ⟨s', hs', rfl⟩
    rw [Subtype.image_preimage_coe]
    exact hs'.null_measurable_set.inter hs
  · simp only [image_empty, null_measurable_set_empty]
  · intro t'
    simp only [← range_diff_image Subtype.coe_injective, Subtype.range_coe_subtype, set_of_mem_eq]
    exact hs.diff
  · intro f
    rw [image_Union]
    exact null_measurable_set.Union
#align measure_theory.measure.measurable_set.null_measurable_set_subtype_coe MeasureTheory.Measure.MeasurableSet.nullMeasurableSetSubtypeCoe

theorem NullMeasurableSet.subtypeCoe {t : Set s} (hs : NullMeasurableSet s μ)
    (ht : NullMeasurableSet t (μ.comap Subtype.val)) : NullMeasurableSet ((coe : s → α) '' t) μ :=
  NullMeasurableSet.image coe μ Subtype.coe_injective
    (fun t => MeasurableSet.nullMeasurableSetSubtypeCoe hs) ht
#align measure_theory.measure.null_measurable_set.subtype_coe MeasureTheory.Measure.NullMeasurableSet.subtypeCoe

theorem measure_subtype_coe_le_comap (hs : NullMeasurableSet s μ) (t : Set s) :
    μ ((coe : s → α) '' t) ≤ μ.comap Subtype.val t :=
  le_comap_apply _ _ Subtype.coe_injective (fun t => MeasurableSet.nullMeasurableSetSubtypeCoe hs) _
#align measure_theory.measure.measure_subtype_coe_le_comap MeasureTheory.Measure.measure_subtype_coe_le_comap

theorem measure_subtype_coe_eq_zero_of_comap_eq_zero (hs : NullMeasurableSet s μ) {t : Set s}
    (ht : μ.comap Subtype.val t = 0) : μ ((coe : s → α) '' t) = 0 :=
  eq_bot_iff.mpr <| (measure_subtype_coe_le_comap hs t).trans ht.le
#align measure_theory.measure.measure_subtype_coe_eq_zero_of_comap_eq_zero MeasureTheory.Measure.measure_subtype_coe_eq_zero_of_comap_eq_zero

end ComapAnyMeasure

section MeasureSpace

variable [MeasureSpace α] {p : α → Prop}

instance Subtype.measureSpace : MeasureSpace (Subtype p) :=
  { Subtype.measurableSpace with volume := Measure.comap Subtype.val volume }
#align measure_theory.measure.subtype.measure_space MeasureTheory.Measure.Subtype.measureSpace

theorem Subtype.volume_def : (volume : Measure s) = volume.comap Subtype.val :=
  rfl
#align measure_theory.measure.subtype.volume_def MeasureTheory.Measure.Subtype.volume_def

theorem Subtype.volume_univ (hs : NullMeasurableSet s) : volume (univ : Set s) = volume s :=
  by
  rw [subtype.volume_def, comap_apply₀ _ _ _ _ measurable_set.univ.null_measurable_set]
  · congr
    simp only [Subtype.val_eq_coe, image_univ, Subtype.range_coe_subtype, set_of_mem_eq]
  · exact Subtype.coe_injective
  · exact fun t => measurable_set.null_measurable_set_subtype_coe hs
#align measure_theory.measure.subtype.volume_univ MeasureTheory.Measure.Subtype.volume_univ

theorem volume_subtype_coe_le_volume (hs : NullMeasurableSet s) (t : Set s) :
    volume ((coe : s → α) '' t) ≤ volume t :=
  measure_subtype_coe_le_comap hs t
#align measure_theory.measure.volume_subtype_coe_le_volume MeasureTheory.Measure.volume_subtype_coe_le_volume

theorem volume_subtype_coe_eq_zero_of_volume_eq_zero (hs : NullMeasurableSet s) {t : Set s}
    (ht : volume t = 0) : volume ((coe : s → α) '' t) = 0 :=
  measure_subtype_coe_eq_zero_of_comap_eq_zero hs ht
#align measure_theory.measure.volume_subtype_coe_eq_zero_of_volume_eq_zero MeasureTheory.Measure.volume_subtype_coe_eq_zero_of_volume_eq_zero

end MeasureSpace

end Subtype

/-! ### Restricting a measure -/


/-- Restrict a measure `μ` to a set `s` as an `ℝ≥0∞`-linear map. -/
def restrictₗ {m0 : MeasurableSpace α} (s : Set α) : Measure α →ₗ[ℝ≥0∞] Measure α :=
  liftLinear (OuterMeasure.restrict s) fun μ s' hs' t =>
    by
    suffices μ (s ∩ t) = μ (s ∩ t ∩ s') + μ ((s ∩ t) \ s') by
      simpa [← Set.inter_assoc, Set.inter_comm _ s, ← inter_diff_assoc]
    exact le_to_outer_measure_caratheodory _ _ hs' _
#align measure_theory.measure.restrictₗ MeasureTheory.Measure.restrictₗ

/-- Restrict a measure `μ` to a set `s`. -/
def restrict {m0 : MeasurableSpace α} (μ : Measure α) (s : Set α) : Measure α :=
  restrictₗ s μ
#align measure_theory.measure.restrict MeasureTheory.Measure.restrict

@[simp]
theorem restrictₗ_apply {m0 : MeasurableSpace α} (s : Set α) (μ : Measure α) :
    restrictₗ s μ = μ.restrict s :=
  rfl
#align measure_theory.measure.restrictₗ_apply MeasureTheory.Measure.restrictₗ_apply

/-- This lemma shows that `restrict` and `to_outer_measure` commute. Note that the LHS has a
restrict on measures and the RHS has a restrict on outer measures. -/
theorem restrict_toOuterMeasure_eq_toOuterMeasure_restrict (h : MeasurableSet s) :
    (μ.restrict s).toOuterMeasure = OuterMeasure.restrict s μ.toOuterMeasure := by
  simp_rw [restrict, restrictₗ, lift_linear, LinearMap.coe_mk, to_measure_to_outer_measure,
    outer_measure.restrict_trim h, μ.trimmed]
#align measure_theory.measure.restrict_to_outer_measure_eq_to_outer_measure_restrict MeasureTheory.Measure.restrict_toOuterMeasure_eq_toOuterMeasure_restrict

theorem restrict_apply₀ (ht : NullMeasurableSet t (μ.restrict s)) : μ.restrict s t = μ (t ∩ s) :=
  (toMeasure_apply₀ _ _ ht).trans <| by
    simp only [coe_to_outer_measure, outer_measure.restrict_apply]
#align measure_theory.measure.restrict_apply₀ MeasureTheory.Measure.restrict_apply₀

/-- If `t` is a measurable set, then the measure of `t` with respect to the restriction of
  the measure to `s` equals the outer measure of `t ∩ s`. An alternate version requiring that `s`
  be measurable instead of `t` exists as `measure.restrict_apply'`. -/
@[simp]
theorem restrict_apply (ht : MeasurableSet t) : μ.restrict s t = μ (t ∩ s) :=
  restrict_apply₀ ht.NullMeasurableSet
#align measure_theory.measure.restrict_apply MeasureTheory.Measure.restrict_apply

/-- Restriction of a measure to a subset is monotone both in set and in measure. -/
theorem restrict_mono' {m0 : MeasurableSpace α} ⦃s s' : Set α⦄ ⦃μ ν : Measure α⦄ (hs : s ≤ᵐ[μ] s')
    (hμν : μ ≤ ν) : μ.restrict s ≤ ν.restrict s' := fun t ht =>
  calc
    μ.restrict s t = μ (t ∩ s) := restrict_apply ht
    _ ≤ μ (t ∩ s') := (measure_mono_ae <| hs.mono fun x hx ⟨hxt, hxs⟩ => ⟨hxt, hx hxs⟩)
    _ ≤ ν (t ∩ s') := (le_iff'.1 hμν (t ∩ s'))
    _ = ν.restrict s' t := (restrict_apply ht).symm
    
#align measure_theory.measure.restrict_mono' MeasureTheory.Measure.restrict_mono'

/-- Restriction of a measure to a subset is monotone both in set and in measure. -/
@[mono]
theorem restrict_mono {m0 : MeasurableSpace α} ⦃s s' : Set α⦄ (hs : s ⊆ s') ⦃μ ν : Measure α⦄
    (hμν : μ ≤ ν) : μ.restrict s ≤ ν.restrict s' :=
  restrict_mono' (ae_of_all _ hs) hμν
#align measure_theory.measure.restrict_mono MeasureTheory.Measure.restrict_mono

theorem restrict_mono_ae (h : s ≤ᵐ[μ] t) : μ.restrict s ≤ μ.restrict t :=
  restrict_mono' h (le_refl μ)
#align measure_theory.measure.restrict_mono_ae MeasureTheory.Measure.restrict_mono_ae

theorem restrict_congr_set (h : s =ᵐ[μ] t) : μ.restrict s = μ.restrict t :=
  le_antisymm (restrict_mono_ae h.le) (restrict_mono_ae h.symm.le)
#align measure_theory.measure.restrict_congr_set MeasureTheory.Measure.restrict_congr_set

/-- If `s` is a measurable set, then the outer measure of `t` with respect to the restriction of
the measure to `s` equals the outer measure of `t ∩ s`. This is an alternate version of
`measure.restrict_apply`, requiring that `s` is measurable instead of `t`. -/
@[simp]
theorem restrict_apply' (hs : MeasurableSet s) : μ.restrict s t = μ (t ∩ s) := by
  rw [← coe_to_outer_measure, measure.restrict_to_outer_measure_eq_to_outer_measure_restrict hs,
    outer_measure.restrict_apply s t _, coe_to_outer_measure]
#align measure_theory.measure.restrict_apply' MeasureTheory.Measure.restrict_apply'

theorem restrict_apply₀' (hs : NullMeasurableSet s μ) : μ.restrict s t = μ (t ∩ s) := by
  rw [← restrict_congr_set hs.to_measurable_ae_eq,
    restrict_apply' (measurable_set_to_measurable _ _),
    measure_congr ((ae_eq_refl t).inter hs.to_measurable_ae_eq)]
#align measure_theory.measure.restrict_apply₀' MeasureTheory.Measure.restrict_apply₀'

theorem restrict_le_self : μ.restrict s ≤ μ := fun t ht =>
  calc
    μ.restrict s t = μ (t ∩ s) := restrict_apply ht
    _ ≤ μ t := measure_mono <| inter_subset_left t s
    
#align measure_theory.measure.restrict_le_self MeasureTheory.Measure.restrict_le_self

variable (μ)

theorem restrict_eq_self (h : s ⊆ t) : μ.restrict t s = μ s :=
  (le_iff'.1 restrict_le_self s).antisymm <|
    calc
      μ s ≤ μ (toMeasurable (μ.restrict t) s ∩ t) :=
        measure_mono (subset_inter (subset_toMeasurable _ _) h)
      _ = μ.restrict t s := by
        rw [← restrict_apply (measurable_set_to_measurable _ _), measure_to_measurable]
      
#align measure_theory.measure.restrict_eq_self MeasureTheory.Measure.restrict_eq_self

@[simp]
theorem restrict_apply_self (s : Set α) : (μ.restrict s) s = μ s :=
  restrict_eq_self μ Subset.rfl
#align measure_theory.measure.restrict_apply_self MeasureTheory.Measure.restrict_apply_self

variable {μ}

theorem restrict_apply_univ (s : Set α) : μ.restrict s univ = μ s := by
  rw [restrict_apply MeasurableSet.univ, Set.univ_inter]
#align measure_theory.measure.restrict_apply_univ MeasureTheory.Measure.restrict_apply_univ

theorem le_restrict_apply (s t : Set α) : μ (t ∩ s) ≤ μ.restrict s t :=
  calc
    μ (t ∩ s) = μ.restrict s (t ∩ s) := (restrict_eq_self μ (inter_subset_right _ _)).symm
    _ ≤ μ.restrict s t := measure_mono (inter_subset_left _ _)
    
#align measure_theory.measure.le_restrict_apply MeasureTheory.Measure.le_restrict_apply

theorem restrict_apply_superset (h : s ⊆ t) : μ.restrict s t = μ s :=
  ((measure_mono (subset_univ _)).trans_eq <| restrict_apply_univ _).antisymm
    ((restrict_apply_self μ s).symm.trans_le <| measure_mono h)
#align measure_theory.measure.restrict_apply_superset MeasureTheory.Measure.restrict_apply_superset

@[simp]
theorem restrict_add {m0 : MeasurableSpace α} (μ ν : Measure α) (s : Set α) :
    (μ + ν).restrict s = μ.restrict s + ν.restrict s :=
  (restrictₗ s).map_add μ ν
#align measure_theory.measure.restrict_add MeasureTheory.Measure.restrict_add

@[simp]
theorem restrict_zero {m0 : MeasurableSpace α} (s : Set α) : (0 : Measure α).restrict s = 0 :=
  (restrictₗ s).map_zero
#align measure_theory.measure.restrict_zero MeasureTheory.Measure.restrict_zero

@[simp]
theorem restrict_smul {m0 : MeasurableSpace α} (c : ℝ≥0∞) (μ : Measure α) (s : Set α) :
    (c • μ).restrict s = c • μ.restrict s :=
  (restrictₗ s).map_smul c μ
#align measure_theory.measure.restrict_smul MeasureTheory.Measure.restrict_smul

theorem restrict_restrict₀ (hs : NullMeasurableSet s (μ.restrict t)) :
    (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  ext fun u hu => by
    simp only [Set.inter_assoc, restrict_apply hu,
      restrict_apply₀ (hu.null_measurable_set.inter hs)]
#align measure_theory.measure.restrict_restrict₀ MeasureTheory.Measure.restrict_restrict₀

@[simp]
theorem restrict_restrict (hs : MeasurableSet s) : (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  restrict_restrict₀ hs.NullMeasurableSet
#align measure_theory.measure.restrict_restrict MeasureTheory.Measure.restrict_restrict

theorem restrict_restrict_of_subset (h : s ⊆ t) : (μ.restrict t).restrict s = μ.restrict s :=
  by
  ext1 u hu
  rw [restrict_apply hu, restrict_apply hu, restrict_eq_self]
  exact (inter_subset_right _ _).trans h
#align measure_theory.measure.restrict_restrict_of_subset MeasureTheory.Measure.restrict_restrict_of_subset

theorem restrict_restrict₀' (ht : NullMeasurableSet t μ) :
    (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  ext fun u hu => by simp only [restrict_apply hu, restrict_apply₀' ht, inter_assoc]
#align measure_theory.measure.restrict_restrict₀' MeasureTheory.Measure.restrict_restrict₀'

theorem restrict_restrict' (ht : MeasurableSet t) :
    (μ.restrict t).restrict s = μ.restrict (s ∩ t) :=
  restrict_restrict₀' ht.NullMeasurableSet
#align measure_theory.measure.restrict_restrict' MeasureTheory.Measure.restrict_restrict'

theorem restrict_comm (hs : MeasurableSet s) :
    (μ.restrict t).restrict s = (μ.restrict s).restrict t := by
  rw [restrict_restrict hs, restrict_restrict' hs, inter_comm]
#align measure_theory.measure.restrict_comm MeasureTheory.Measure.restrict_comm

theorem restrict_apply_eq_zero (ht : MeasurableSet t) : μ.restrict s t = 0 ↔ μ (t ∩ s) = 0 := by
  rw [restrict_apply ht]
#align measure_theory.measure.restrict_apply_eq_zero MeasureTheory.Measure.restrict_apply_eq_zero

theorem measure_inter_eq_zero_of_restrict (h : μ.restrict s t = 0) : μ (t ∩ s) = 0 :=
  nonpos_iff_eq_zero.1 (h ▸ le_restrict_apply _ _)
#align measure_theory.measure.measure_inter_eq_zero_of_restrict MeasureTheory.Measure.measure_inter_eq_zero_of_restrict

theorem restrict_apply_eq_zero' (hs : MeasurableSet s) : μ.restrict s t = 0 ↔ μ (t ∩ s) = 0 := by
  rw [restrict_apply' hs]
#align measure_theory.measure.restrict_apply_eq_zero' MeasureTheory.Measure.restrict_apply_eq_zero'

@[simp]
theorem restrict_eq_zero : μ.restrict s = 0 ↔ μ s = 0 := by
  rw [← measure_univ_eq_zero, restrict_apply_univ]
#align measure_theory.measure.restrict_eq_zero MeasureTheory.Measure.restrict_eq_zero

theorem restrict_zero_set {s : Set α} (h : μ s = 0) : μ.restrict s = 0 :=
  restrict_eq_zero.2 h
#align measure_theory.measure.restrict_zero_set MeasureTheory.Measure.restrict_zero_set

@[simp]
theorem restrict_empty : μ.restrict ∅ = 0 :=
  restrict_zero_set measure_empty
#align measure_theory.measure.restrict_empty MeasureTheory.Measure.restrict_empty

@[simp]
theorem restrict_univ : μ.restrict univ = μ :=
  ext fun s hs => by simp [hs]
#align measure_theory.measure.restrict_univ MeasureTheory.Measure.restrict_univ

theorem restrict_inter_add_diff₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ.restrict (s ∩ t) + μ.restrict (s \ t) = μ.restrict s :=
  by
  ext1 u hu
  simp only [add_apply, restrict_apply hu, ← inter_assoc, diff_eq]
  exact measure_inter_add_diff₀ (u ∩ s) ht
#align measure_theory.measure.restrict_inter_add_diff₀ MeasureTheory.Measure.restrict_inter_add_diff₀

theorem restrict_inter_add_diff (s : Set α) (ht : MeasurableSet t) :
    μ.restrict (s ∩ t) + μ.restrict (s \ t) = μ.restrict s :=
  restrict_inter_add_diff₀ s ht.NullMeasurableSet
#align measure_theory.measure.restrict_inter_add_diff MeasureTheory.Measure.restrict_inter_add_diff

theorem restrict_union_add_inter₀ (s : Set α) (ht : NullMeasurableSet t μ) :
    μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t := by
  rw [← restrict_inter_add_diff₀ (s ∪ t) ht, union_inter_cancel_right, union_diff_right, ←
    restrict_inter_add_diff₀ s ht, add_comm, ← add_assoc, add_right_comm]
#align measure_theory.measure.restrict_union_add_inter₀ MeasureTheory.Measure.restrict_union_add_inter₀

theorem restrict_union_add_inter (s : Set α) (ht : MeasurableSet t) :
    μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t :=
  restrict_union_add_inter₀ s ht.NullMeasurableSet
#align measure_theory.measure.restrict_union_add_inter MeasureTheory.Measure.restrict_union_add_inter

theorem restrict_union_add_inter' (hs : MeasurableSet s) (t : Set α) :
    μ.restrict (s ∪ t) + μ.restrict (s ∩ t) = μ.restrict s + μ.restrict t := by
  simpa only [union_comm, inter_comm, add_comm] using restrict_union_add_inter t hs
#align measure_theory.measure.restrict_union_add_inter' MeasureTheory.Measure.restrict_union_add_inter'

theorem restrict_union₀ (h : AeDisjoint μ s t) (ht : NullMeasurableSet t μ) :
    μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t := by
  simp [← restrict_union_add_inter₀ s ht, restrict_zero_set h]
#align measure_theory.measure.restrict_union₀ MeasureTheory.Measure.restrict_union₀

theorem restrict_union (h : Disjoint s t) (ht : MeasurableSet t) :
    μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t :=
  restrict_union₀ h.AeDisjoint ht.NullMeasurableSet
#align measure_theory.measure.restrict_union MeasureTheory.Measure.restrict_union

theorem restrict_union' (h : Disjoint s t) (hs : MeasurableSet s) :
    μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t := by
  rw [union_comm, restrict_union h.symm hs, add_comm]
#align measure_theory.measure.restrict_union' MeasureTheory.Measure.restrict_union'

@[simp]
theorem restrict_add_restrict_compl (hs : MeasurableSet s) : μ.restrict s + μ.restrict (sᶜ) = μ :=
  by
  rw [← restrict_union (@disjoint_compl_right (Set α) _ _) hs.compl, union_compl_self,
    restrict_univ]
#align measure_theory.measure.restrict_add_restrict_compl MeasureTheory.Measure.restrict_add_restrict_compl

@[simp]
theorem restrict_compl_add_restrict (hs : MeasurableSet s) : μ.restrict (sᶜ) + μ.restrict s = μ :=
  by rw [add_comm, restrict_add_restrict_compl hs]
#align measure_theory.measure.restrict_compl_add_restrict MeasureTheory.Measure.restrict_compl_add_restrict

theorem restrict_union_le (s s' : Set α) : μ.restrict (s ∪ s') ≤ μ.restrict s + μ.restrict s' :=
  by
  intro t ht
  suffices μ (t ∩ s ∪ t ∩ s') ≤ μ (t ∩ s) + μ (t ∩ s') by simpa [ht, inter_union_distrib_left]
  apply measure_union_le
#align measure_theory.measure.restrict_union_le MeasureTheory.Measure.restrict_union_le

theorem restrict_unionᵢ_apply_ae [Countable ι] {s : ι → Set α} (hd : Pairwise (AeDisjoint μ on s))
    (hm : ∀ i, NullMeasurableSet (s i) μ) {t : Set α} (ht : MeasurableSet t) :
    μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t :=
  by
  simp only [restrict_apply, ht, inter_Union]
  exact
    measure_Union₀ (hd.mono fun i j h => h.mono (inter_subset_right _ _) (inter_subset_right _ _))
      fun i => ht.null_measurable_set.inter (hm i)
#align measure_theory.measure.restrict_Union_apply_ae MeasureTheory.Measure.restrict_unionᵢ_apply_ae

theorem restrict_unionᵢ_apply [Countable ι] {s : ι → Set α} (hd : Pairwise (Disjoint on s))
    (hm : ∀ i, MeasurableSet (s i)) {t : Set α} (ht : MeasurableSet t) :
    μ.restrict (⋃ i, s i) t = ∑' i, μ.restrict (s i) t :=
  restrict_unionᵢ_apply_ae hd.AeDisjoint (fun i => (hm i).NullMeasurableSet) ht
#align measure_theory.measure.restrict_Union_apply MeasureTheory.Measure.restrict_unionᵢ_apply

theorem restrict_unionᵢ_apply_eq_supᵢ [Countable ι] {s : ι → Set α} (hd : Directed (· ⊆ ·) s)
    {t : Set α} (ht : MeasurableSet t) : μ.restrict (⋃ i, s i) t = ⨆ i, μ.restrict (s i) t :=
  by
  simp only [restrict_apply ht, inter_Union]
  rw [measure_Union_eq_supr]
  exacts[hd.mono_comp _ fun s₁ s₂ => inter_subset_inter_right _]
#align measure_theory.measure.restrict_Union_apply_eq_supr MeasureTheory.Measure.restrict_unionᵢ_apply_eq_supᵢ

/-- The restriction of the pushforward measure is the pushforward of the restriction. For a version
assuming only `ae_measurable`, see `restrict_map_of_ae_measurable`. -/
theorem restrict_map {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) :
    (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  ext fun t ht => by simp [*, hf ht]
#align measure_theory.measure.restrict_map MeasureTheory.Measure.restrict_map

theorem restrict_toMeasurable (h : μ s ≠ ∞) : μ.restrict (toMeasurable μ s) = μ.restrict s :=
  ext fun t ht => by
    rw [restrict_apply ht, restrict_apply ht, inter_comm, measure_to_measurable_inter ht h,
      inter_comm]
#align measure_theory.measure.restrict_to_measurable MeasureTheory.Measure.restrict_toMeasurable

theorem restrict_eq_self_of_ae_mem {m0 : MeasurableSpace α} ⦃s : Set α⦄ ⦃μ : Measure α⦄
    (hs : ∀ᵐ x ∂μ, x ∈ s) : μ.restrict s = μ :=
  calc
    μ.restrict s = μ.restrict univ := restrict_congr_set (eventuallyEq_univ.mpr hs)
    _ = μ := restrict_univ
    
#align measure_theory.measure.restrict_eq_self_of_ae_mem MeasureTheory.Measure.restrict_eq_self_of_ae_mem

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem restrict_congr_meas (hs : MeasurableSet s) :
    μ.restrict s = ν.restrict s ↔ ∀ (t) (_ : t ⊆ s), MeasurableSet t → μ t = ν t :=
  ⟨fun H t hts ht => by
    rw [← inter_eq_self_of_subset_left hts, ← restrict_apply ht, H, restrict_apply ht], fun H =>
    ext fun t ht => by
      rw [restrict_apply ht, restrict_apply ht, H _ (inter_subset_right _ _) (ht.inter hs)]⟩
#align measure_theory.measure.restrict_congr_meas MeasureTheory.Measure.restrict_congr_meas

theorem restrict_congr_mono (hs : s ⊆ t) (h : μ.restrict t = ν.restrict t) :
    μ.restrict s = ν.restrict s := by
  rw [← restrict_restrict_of_subset hs, h, restrict_restrict_of_subset hs]
#align measure_theory.measure.restrict_congr_mono MeasureTheory.Measure.restrict_congr_mono

/-- If two measures agree on all measurable subsets of `s` and `t`, then they agree on all
measurable subsets of `s ∪ t`. -/
theorem restrict_union_congr :
    μ.restrict (s ∪ t) = ν.restrict (s ∪ t) ↔
      μ.restrict s = ν.restrict s ∧ μ.restrict t = ν.restrict t :=
  by
  refine'
    ⟨fun h =>
      ⟨restrict_congr_mono (subset_union_left _ _) h,
        restrict_congr_mono (subset_union_right _ _) h⟩,
      _⟩
  rintro ⟨hs, ht⟩
  ext1 u hu
  simp only [restrict_apply hu, inter_union_distrib_left]
  rcases exists_measurable_superset₂ μ ν (u ∩ s) with ⟨US, hsub, hm, hμ, hν⟩
  calc
    μ (u ∩ s ∪ u ∩ t) = μ (US ∪ u ∩ t) := measure_union_congr_of_subset hsub hμ.le subset.rfl le_rfl
    _ = μ US + μ ((u ∩ t) \ US) := (measure_add_diff hm _).symm
    _ = restrict μ s u + restrict μ t (u \ US) := by
      simp only [restrict_apply, hu, hu.diff hm, hμ, ← inter_comm t, inter_diff_assoc]
    _ = restrict ν s u + restrict ν t (u \ US) := by rw [hs, ht]
    _ = ν US + ν ((u ∩ t) \ US) := by
      simp only [restrict_apply, hu, hu.diff hm, hν, ← inter_comm t, inter_diff_assoc]
    _ = ν (US ∪ u ∩ t) := (measure_add_diff hm _)
    _ = ν (u ∩ s ∪ u ∩ t) := Eq.symm <| measure_union_congr_of_subset hsub hν.le subset.rfl le_rfl
    
#align measure_theory.measure.restrict_union_congr MeasureTheory.Measure.restrict_union_congr

theorem restrict_finset_bUnion_congr {s : Finset ι} {t : ι → Set α} :
    μ.restrict (⋃ i ∈ s, t i) = ν.restrict (⋃ i ∈ s, t i) ↔
      ∀ i ∈ s, μ.restrict (t i) = ν.restrict (t i) :=
  by
  induction' s using Finset.induction_on with i s hi hs; · simp
  simp only [forall_eq_or_imp, Union_Union_eq_or_left, Finset.mem_insert]
  rw [restrict_union_congr, ← hs]
#align measure_theory.measure.restrict_finset_bUnion_congr MeasureTheory.Measure.restrict_finset_bUnion_congr

theorem restrict_unionᵢ_congr [Countable ι] {s : ι → Set α} :
    μ.restrict (⋃ i, s i) = ν.restrict (⋃ i, s i) ↔ ∀ i, μ.restrict (s i) = ν.restrict (s i) :=
  by
  refine' ⟨fun h i => restrict_congr_mono (subset_Union _ _) h, fun h => _⟩
  ext1 t ht
  have D : Directed (· ⊆ ·) fun t : Finset ι => ⋃ i ∈ t, s i :=
    directed_of_sup fun t₁ t₂ ht => bUnion_subset_bUnion_left ht
  rw [Union_eq_Union_finset]
  simp only [restrict_Union_apply_eq_supr D ht, restrict_finset_bUnion_congr.2 fun i hi => h i]
#align measure_theory.measure.restrict_Union_congr MeasureTheory.Measure.restrict_unionᵢ_congr

theorem restrict_bUnion_congr {s : Set ι} {t : ι → Set α} (hc : s.Countable) :
    μ.restrict (⋃ i ∈ s, t i) = ν.restrict (⋃ i ∈ s, t i) ↔
      ∀ i ∈ s, μ.restrict (t i) = ν.restrict (t i) :=
  by
  haveI := hc.to_encodable
  simp only [bUnion_eq_Union, SetCoe.forall', restrict_Union_congr]
#align measure_theory.measure.restrict_bUnion_congr MeasureTheory.Measure.restrict_bUnion_congr

theorem restrict_unionₛ_congr {S : Set (Set α)} (hc : S.Countable) :
    μ.restrict (⋃₀ S) = ν.restrict (⋃₀ S) ↔ ∀ s ∈ S, μ.restrict s = ν.restrict s := by
  rw [sUnion_eq_bUnion, restrict_bUnion_congr hc]
#align measure_theory.measure.restrict_sUnion_congr MeasureTheory.Measure.restrict_unionₛ_congr

/-- This lemma shows that `Inf` and `restrict` commute for measures. -/
theorem restrict_infₛ_eq_infₛ_restrict {m0 : MeasurableSpace α} {m : Set (Measure α)}
    (hm : m.Nonempty) (ht : MeasurableSet t) :
    (infₛ m).restrict t = infₛ ((fun μ : Measure α => μ.restrict t) '' m) :=
  by
  ext1 s hs
  simp_rw [infₛ_apply hs, restrict_apply hs, infₛ_apply (MeasurableSet.inter hs ht),
    Set.image_image, restrict_to_outer_measure_eq_to_outer_measure_restrict ht, ←
    Set.image_image _ to_outer_measure, ← outer_measure.restrict_Inf_eq_Inf_restrict _ (hm.image _),
    outer_measure.restrict_apply]
#align measure_theory.measure.restrict_Inf_eq_Inf_restrict MeasureTheory.Measure.restrict_infₛ_eq_infₛ_restrict

theorem exists_mem_of_measure_ne_zero_of_ae (hs : μ s ≠ 0) {p : α → Prop}
    (hp : ∀ᵐ x ∂μ.restrict s, p x) : ∃ x, x ∈ s ∧ p x :=
  by
  rw [← μ.restrict_apply_self, ← frequently_ae_mem_iff] at hs
  exact (hs.and_eventually hp).exists
#align measure_theory.measure.exists_mem_of_measure_ne_zero_of_ae MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae

/-! ### Extensionality results -/


/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `Union`). -/
theorem ext_iff_of_unionᵢ_eq_univ [Countable ι] {s : ι → Set α} (hs : (⋃ i, s i) = univ) :
    μ = ν ↔ ∀ i, μ.restrict (s i) = ν.restrict (s i) := by
  rw [← restrict_Union_congr, hs, restrict_univ, restrict_univ]
#align measure_theory.measure.ext_iff_of_Union_eq_univ MeasureTheory.Measure.ext_iff_of_unionᵢ_eq_univ

alias ext_iff_of_Union_eq_univ ↔ _ ext_of_Union_eq_univ
#align measure_theory.measure.ext_of_Union_eq_univ MeasureTheory.Measure.ext_of_unionᵢ_eq_univ

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `bUnion`). -/
theorem ext_iff_of_bUnion_eq_univ {S : Set ι} {s : ι → Set α} (hc : S.Countable)
    (hs : (⋃ i ∈ S, s i) = univ) : μ = ν ↔ ∀ i ∈ S, μ.restrict (s i) = ν.restrict (s i) := by
  rw [← restrict_bUnion_congr hc, hs, restrict_univ, restrict_univ]
#align measure_theory.measure.ext_iff_of_bUnion_eq_univ MeasureTheory.Measure.ext_iff_of_bUnion_eq_univ

alias ext_iff_of_bUnion_eq_univ ↔ _ ext_of_bUnion_eq_univ
#align measure_theory.measure.ext_of_bUnion_eq_univ MeasureTheory.Measure.ext_of_bUnion_eq_univ

/-- Two measures are equal if they have equal restrictions on a spanning collection of sets
  (formulated using `sUnion`). -/
theorem ext_iff_of_unionₛ_eq_univ {S : Set (Set α)} (hc : S.Countable) (hs : ⋃₀ S = univ) :
    μ = ν ↔ ∀ s ∈ S, μ.restrict s = ν.restrict s :=
  ext_iff_of_bUnion_eq_univ hc <| by rwa [← sUnion_eq_bUnion]
#align measure_theory.measure.ext_iff_of_sUnion_eq_univ MeasureTheory.Measure.ext_iff_of_unionₛ_eq_univ

alias ext_iff_of_sUnion_eq_univ ↔ _ ext_of_sUnion_eq_univ
#align measure_theory.measure.ext_of_sUnion_eq_univ MeasureTheory.Measure.ext_of_unionₛ_eq_univ

theorem ext_of_generateFrom_of_cover {S T : Set (Set α)} (h_gen : ‹_› = generateFrom S)
    (hc : T.Countable) (h_inter : IsPiSystem S) (hU : ⋃₀ T = univ) (htop : ∀ t ∈ T, μ t ≠ ∞)
    (ST_eq : ∀ t ∈ T, ∀ s ∈ S, μ (s ∩ t) = ν (s ∩ t)) (T_eq : ∀ t ∈ T, μ t = ν t) : μ = ν :=
  by
  refine' ext_of_sUnion_eq_univ hc hU fun t ht => _
  ext1 u hu
  simp only [restrict_apply hu]
  refine' induction_on_inter h_gen h_inter _ (ST_eq t ht) _ _ hu
  · simp only [Set.empty_inter, measure_empty]
  · intro v hv hvt
    have := T_eq t ht
    rw [Set.inter_comm] at hvt⊢
    rwa [← measure_inter_add_diff t hv, ← measure_inter_add_diff t hv, ← hvt,
      ENNReal.add_right_inj] at this
    exact ne_top_of_le_ne_top (htop t ht) (measure_mono <| Set.inter_subset_left _ _)
  · intro f hfd hfm h_eq
    simp only [← restrict_apply (hfm _), ← restrict_apply (MeasurableSet.unionᵢ hfm)] at h_eq⊢
    simp only [measure_Union hfd hfm, h_eq]
#align measure_theory.measure.ext_of_generate_from_of_cover MeasureTheory.Measure.ext_of_generateFrom_of_cover

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on a increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `sUnion`. -/
theorem ext_of_generateFrom_of_cover_subset {S T : Set (Set α)} (h_gen : ‹_› = generateFrom S)
    (h_inter : IsPiSystem S) (h_sub : T ⊆ S) (hc : T.Countable) (hU : ⋃₀ T = univ)
    (htop : ∀ s ∈ T, μ s ≠ ∞) (h_eq : ∀ s ∈ S, μ s = ν s) : μ = ν :=
  by
  refine' ext_of_generate_from_of_cover h_gen hc h_inter hU htop _ fun t ht => h_eq t (h_sub ht)
  intro t ht s hs; cases' (s ∩ t).eq_empty_or_nonempty with H H
  · simp only [H, measure_empty]
  · exact h_eq _ (h_inter _ hs _ (h_sub ht) H)
#align measure_theory.measure.ext_of_generate_from_of_cover_subset MeasureTheory.Measure.ext_of_generateFrom_of_cover_subset

/-- Two measures are equal if they are equal on the π-system generating the σ-algebra,
  and they are both finite on a increasing spanning sequence of sets in the π-system.
  This lemma is formulated using `Union`.
  `finite_spanning_sets_in.ext` is a reformulation of this lemma. -/
theorem ext_of_generateFrom_of_unionᵢ (C : Set (Set α)) (B : ℕ → Set α) (hA : ‹_› = generateFrom C)
    (hC : IsPiSystem C) (h1B : (⋃ i, B i) = univ) (h2B : ∀ i, B i ∈ C) (hμB : ∀ i, μ (B i) ≠ ∞)
    (h_eq : ∀ s ∈ C, μ s = ν s) : μ = ν :=
  by
  refine' ext_of_generate_from_of_cover_subset hA hC _ (countable_range B) h1B _ h_eq
  · rintro _ ⟨i, rfl⟩
    apply h2B
  · rintro _ ⟨i, rfl⟩
    apply hμB
#align measure_theory.measure.ext_of_generate_from_of_Union MeasureTheory.Measure.ext_of_generateFrom_of_unionᵢ

section Dirac

variable [MeasurableSpace α]

/-- The dirac measure. -/
def dirac (a : α) : Measure α :=
  (OuterMeasure.dirac a).toMeasure (by simp)
#align measure_theory.measure.dirac MeasureTheory.Measure.dirac

instance : MeasureSpace PUnit :=
  ⟨dirac PUnit.unit⟩

theorem le_dirac_apply {a} : s.indicator 1 a ≤ dirac a s :=
  OuterMeasure.dirac_apply a s ▸ le_toMeasure_apply _ _ _
#align measure_theory.measure.le_dirac_apply MeasureTheory.Measure.le_dirac_apply

@[simp]
theorem dirac_apply' (a : α) (hs : MeasurableSet s) : dirac a s = s.indicator 1 a :=
  toMeasure_apply _ _ hs
#align measure_theory.measure.dirac_apply' MeasureTheory.Measure.dirac_apply'

@[simp]
theorem dirac_apply_of_mem {a : α} (h : a ∈ s) : dirac a s = 1 :=
  by
  have : ∀ t : Set α, a ∈ t → t.indicator (1 : α → ℝ≥0∞) a = 1 := fun t ht => indicator_of_mem ht 1
  refine' le_antisymm (this univ trivial ▸ _) (this s h ▸ le_dirac_apply)
  rw [← dirac_apply' a MeasurableSet.univ]
  exact measure_mono (subset_univ s)
#align measure_theory.measure.dirac_apply_of_mem MeasureTheory.Measure.dirac_apply_of_mem

@[simp]
theorem dirac_apply [MeasurableSingletonClass α] (a : α) (s : Set α) :
    dirac a s = s.indicator 1 a := by
  by_cases h : a ∈ s; · rw [dirac_apply_of_mem h, indicator_of_mem h, Pi.one_apply]
  rw [indicator_of_not_mem h, ← nonpos_iff_eq_zero]
  calc
    dirac a s ≤ dirac a ({a}ᶜ) := measure_mono (subset_compl_comm.1 <| singleton_subset_iff.2 h)
    _ = 0 := by simp [dirac_apply' _ (measurable_set_singleton _).compl]
    
#align measure_theory.measure.dirac_apply MeasureTheory.Measure.dirac_apply

theorem map_dirac {f : α → β} (hf : Measurable f) (a : α) : (dirac a).map f = dirac (f a) :=
  ext fun s hs => by simp [hs, map_apply hf hs, hf hs, indicator_apply]
#align measure_theory.measure.map_dirac MeasureTheory.Measure.map_dirac

@[simp]
theorem restrict_singleton (μ : Measure α) (a : α) : μ.restrict {a} = μ {a} • dirac a :=
  by
  ext1 s hs
  by_cases ha : a ∈ s
  · have : s ∩ {a} = {a} := by simpa
    simp [*]
  · have : s ∩ {a} = ∅ := inter_singleton_eq_empty.2 ha
    simp [*]
#align measure_theory.measure.restrict_singleton MeasureTheory.Measure.restrict_singleton

end Dirac

section Sum

include m0

/-- Sum of an indexed family of measures. -/
def sum (f : ι → Measure α) : Measure α :=
  (OuterMeasure.sum fun i => (f i).toOuterMeasure).toMeasure <|
    le_trans (le_infᵢ fun i => le_to_outer_measure_caratheodory _)
      (OuterMeasure.le_sum_caratheodory _)
#align measure_theory.measure.sum MeasureTheory.Measure.sum

theorem le_sum_apply (f : ι → Measure α) (s : Set α) : (∑' i, f i s) ≤ sum f s :=
  le_toMeasure_apply _ _ _
#align measure_theory.measure.le_sum_apply MeasureTheory.Measure.le_sum_apply

@[simp]
theorem sum_apply (f : ι → Measure α) {s : Set α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s :=
  toMeasure_apply _ _ hs
#align measure_theory.measure.sum_apply MeasureTheory.Measure.sum_apply

theorem le_sum (μ : ι → Measure α) (i : ι) : μ i ≤ sum μ := fun s hs => by
  simp only [sum_apply μ hs, ENNReal.le_tsum i]
#align measure_theory.measure.le_sum MeasureTheory.Measure.le_sum

@[simp]
theorem sum_apply_eq_zero [Countable ι] {μ : ι → Measure α} {s : Set α} :
    sum μ s = 0 ↔ ∀ i, μ i s = 0 :=
  by
  refine'
    ⟨fun h i => nonpos_iff_eq_zero.1 <| h ▸ le_iff'.1 (le_sum μ i) _, fun h =>
      nonpos_iff_eq_zero.1 _⟩
  rcases exists_measurable_superset_forall_eq μ s with ⟨t, hst, htm, ht⟩
  calc
    Sum μ s ≤ Sum μ t := measure_mono hst
    _ = 0 := by simp [*]
    
#align measure_theory.measure.sum_apply_eq_zero MeasureTheory.Measure.sum_apply_eq_zero

theorem sum_apply_eq_zero' {μ : ι → Measure α} {s : Set α} (hs : MeasurableSet s) :
    sum μ s = 0 ↔ ∀ i, μ i s = 0 := by simp [hs]
#align measure_theory.measure.sum_apply_eq_zero' MeasureTheory.Measure.sum_apply_eq_zero'

theorem sum_comm {ι' : Type _} (μ : ι → ι' → Measure α) :
    (sum fun n => sum (μ n)) = sum fun m => sum fun n => μ n m :=
  by
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
theorem sum_fintype [Fintype ι] (μ : ι → Measure α) : sum μ = ∑ i, μ i :=
  by
  ext1 s hs
  simp only [sum_apply, finset_sum_apply, hs, tsum_fintype]
#align measure_theory.measure.sum_fintype MeasureTheory.Measure.sum_fintype

@[simp]
theorem sum_coe_finset (s : Finset ι) (μ : ι → Measure α) :
    (sum fun i : s => μ i) = ∑ i in s, μ i := by rw [sum_fintype, Finset.sum_coe_sort s μ]
#align measure_theory.measure.sum_coe_finset MeasureTheory.Measure.sum_coe_finset

@[simp]
theorem ae_sum_eq [Countable ι] (μ : ι → Measure α) : (sum μ).ae = ⨆ i, (μ i).ae :=
  Filter.ext fun s => ae_sum_iff.trans mem_supᵢ.symm
#align measure_theory.measure.ae_sum_eq MeasureTheory.Measure.ae_sum_eq

@[simp]
theorem sum_bool (f : Bool → Measure α) : sum f = f true + f false := by
  rw [sum_fintype, Fintype.sum_bool]
#align measure_theory.measure.sum_bool MeasureTheory.Measure.sum_bool

@[simp]
theorem sum_cond (μ ν : Measure α) : (sum fun b => cond b μ ν) = μ + ν :=
  sum_bool _
#align measure_theory.measure.sum_cond MeasureTheory.Measure.sum_cond

@[simp]
theorem restrict_sum (μ : ι → Measure α) {s : Set α} (hs : MeasurableSet s) :
    (sum μ).restrict s = sum fun i => (μ i).restrict s :=
  ext fun t ht => by simp only [sum_apply, restrict_apply, ht, ht.inter hs]
#align measure_theory.measure.restrict_sum MeasureTheory.Measure.restrict_sum

@[simp]
theorem sum_of_empty [IsEmpty ι] (μ : ι → Measure α) : sum μ = 0 := by
  rw [← measure_univ_eq_zero, sum_apply _ MeasurableSet.univ, tsum_empty]
#align measure_theory.measure.sum_of_empty MeasureTheory.Measure.sum_of_empty

theorem sum_add_sum_compl (s : Set ι) (μ : ι → Measure α) :
    ((sum fun i : s => μ i) + sum fun i : sᶜ => μ i) = sum μ :=
  by
  ext1 t ht
  simp only [add_apply, sum_apply _ ht]
  exact @tsum_add_tsum_compl ℝ≥0∞ ι _ _ _ (fun i => μ i t) _ s ENNReal.summable ENNReal.summable
#align measure_theory.measure.sum_add_sum_compl MeasureTheory.Measure.sum_add_sum_compl

theorem sum_congr {μ ν : ℕ → Measure α} (h : ∀ n, μ n = ν n) : sum μ = sum ν :=
  congr_arg sum (funext h)
#align measure_theory.measure.sum_congr MeasureTheory.Measure.sum_congr

theorem sum_add_sum (μ ν : ℕ → Measure α) : sum μ + sum ν = sum fun n => μ n + ν n :=
  by
  ext1 s hs
  simp only [add_apply, sum_apply _ hs, Pi.add_apply, coe_add,
    tsum_add ENNReal.summable ENNReal.summable]
#align measure_theory.measure.sum_add_sum MeasureTheory.Measure.sum_add_sum

/-- If `f` is a map with countable codomain, then `μ.map f` is a sum of Dirac measures. -/
theorem map_eq_sum [Countable β] [MeasurableSingletonClass β] (μ : Measure α) (f : α → β)
    (hf : Measurable f) : μ.map f = sum fun b : β => μ (f ⁻¹' {b}) • dirac b :=
  by
  ext1 s hs
  have : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y}) := fun y _ => hf (measurable_set_singleton _)
  simp [← tsum_measure_preimage_singleton (to_countable s) this, *,
    tsum_subtype s fun b => μ (f ⁻¹' {b}), ← indicator_mul_right s fun b => μ (f ⁻¹' {b})]
#align measure_theory.measure.map_eq_sum MeasureTheory.Measure.map_eq_sum

/-- A measure on a countable type is a sum of Dirac measures. -/
@[simp]
theorem sum_smul_dirac [Countable α] [MeasurableSingletonClass α] (μ : Measure α) :
    (sum fun a => μ {a} • dirac a) = μ := by simpa using (map_eq_sum μ id measurable_id).symm
#align measure_theory.measure.sum_smul_dirac MeasureTheory.Measure.sum_smul_dirac

/-- Given that `α` is a countable, measurable space with all singleton sets measurable,
write the measure of a set `s` as the sum of the measure of `{x}` for all `x ∈ s`. -/
theorem tsum_indicator_apply_singleton [Countable α] [MeasurableSingletonClass α] (μ : Measure α)
    (s : Set α) (hs : MeasurableSet s) : (∑' x : α, s.indicator (fun x => μ {x}) x) = μ s :=
  calc
    (∑' x : α, s.indicator (fun x => μ {x}) x) = Measure.sum (fun a => μ {a} • Measure.dirac a) s :=
      by
      simp only [measure.sum_apply _ hs, measure.smul_apply, smul_eq_mul, measure.dirac_apply,
        Set.indicator_apply, mul_ite, Pi.one_apply, mul_one, MulZeroClass.mul_zero]
    _ = μ s := by rw [μ.sum_smul_dirac]
    
#align measure_theory.measure.tsum_indicator_apply_singleton MeasureTheory.Measure.tsum_indicator_apply_singleton

omit m0

end Sum

theorem restrict_unionᵢ_ae [Countable ι] {s : ι → Set α} (hd : Pairwise (AeDisjoint μ on s))
    (hm : ∀ i, NullMeasurableSet (s i) μ) : μ.restrict (⋃ i, s i) = sum fun i => μ.restrict (s i) :=
  ext fun t ht => by simp only [sum_apply _ ht, restrict_Union_apply_ae hd hm ht]
#align measure_theory.measure.restrict_Union_ae MeasureTheory.Measure.restrict_unionᵢ_ae

theorem restrict_unionᵢ [Countable ι] {s : ι → Set α} (hd : Pairwise (Disjoint on s))
    (hm : ∀ i, MeasurableSet (s i)) : μ.restrict (⋃ i, s i) = sum fun i => μ.restrict (s i) :=
  restrict_unionᵢ_ae hd.AeDisjoint fun i => (hm i).NullMeasurableSet
#align measure_theory.measure.restrict_Union MeasureTheory.Measure.restrict_unionᵢ

theorem restrict_unionᵢ_le [Countable ι] {s : ι → Set α} :
    μ.restrict (⋃ i, s i) ≤ sum fun i => μ.restrict (s i) :=
  by
  intro t ht
  suffices μ (⋃ i, t ∩ s i) ≤ ∑' i, μ (t ∩ s i) by simpa [ht, inter_Union]
  apply measure_Union_le
#align measure_theory.measure.restrict_Union_le MeasureTheory.Measure.restrict_unionᵢ_le

section Count

variable [MeasurableSpace α]

/-- Counting measure on any measurable space. -/
def count : Measure α :=
  sum dirac
#align measure_theory.measure.count MeasureTheory.Measure.count

theorem le_count_apply : (∑' i : s, 1 : ℝ≥0∞) ≤ count s :=
  calc
    (∑' i : s, 1 : ℝ≥0∞) = ∑' i, indicator s 1 i := tsum_subtype s 1
    _ ≤ ∑' i, dirac i s := (ENNReal.tsum_le_tsum fun x => le_dirac_apply)
    _ ≤ count s := le_sum_apply _ _
    
#align measure_theory.measure.le_count_apply MeasureTheory.Measure.le_count_apply

theorem count_apply (hs : MeasurableSet s) : count s = ∑' i : s, 1 := by
  simp only [count, sum_apply, hs, dirac_apply', ← tsum_subtype s 1, Pi.one_apply]
#align measure_theory.measure.count_apply MeasureTheory.Measure.count_apply

@[simp]
theorem count_empty : count (∅ : Set α) = 0 := by rw [count_apply MeasurableSet.empty, tsum_empty]
#align measure_theory.measure.count_empty MeasureTheory.Measure.count_empty

@[simp]
theorem count_apply_finset' {s : Finset α} (s_mble : MeasurableSet (s : Set α)) :
    count (↑s : Set α) = s.card :=
  calc
    count (↑s : Set α) = ∑' i : (↑s : Set α), 1 := count_apply s_mble
    _ = ∑ i in s, 1 := (s.tsum_subtype 1)
    _ = s.card := by simp
    
#align measure_theory.measure.count_apply_finset' MeasureTheory.Measure.count_apply_finset'

@[simp]
theorem count_apply_finset [MeasurableSingletonClass α] (s : Finset α) :
    count (↑s : Set α) = s.card :=
  count_apply_finset' s.MeasurableSet
#align measure_theory.measure.count_apply_finset MeasureTheory.Measure.count_apply_finset

theorem count_apply_finite' {s : Set α} (s_fin : s.Finite) (s_mble : MeasurableSet s) :
    count s = s_fin.toFinset.card := by
  simp [←
    @count_apply_finset' _ _ s_fin.to_finset (by simpa only [finite.coe_to_finset] using s_mble)]
#align measure_theory.measure.count_apply_finite' MeasureTheory.Measure.count_apply_finite'

theorem count_apply_finite [MeasurableSingletonClass α] (s : Set α) (hs : s.Finite) :
    count s = hs.toFinset.card := by rw [← count_apply_finset, finite.coe_to_finset]
#align measure_theory.measure.count_apply_finite MeasureTheory.Measure.count_apply_finite

/-- `count` measure evaluates to infinity at infinite sets. -/
theorem count_apply_infinite (hs : s.Infinite) : count s = ∞ :=
  by
  refine' top_unique (le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n => _)
  rcases hs.exists_subset_card_eq n with ⟨t, ht, rfl⟩
  calc
    (t.card : ℝ≥0∞) = ∑ i in t, 1 := by simp
    _ = ∑' i : (t : Set α), 1 := (t.tsum_subtype 1).symm
    _ ≤ count (t : Set α) := le_count_apply
    _ ≤ count s := measure_mono ht
    
#align measure_theory.measure.count_apply_infinite MeasureTheory.Measure.count_apply_infinite

@[simp]
theorem count_apply_eq_top' (s_mble : MeasurableSet s) : count s = ∞ ↔ s.Infinite :=
  by
  by_cases hs : s.finite
  · simp [Set.Infinite, hs, count_apply_finite' hs s_mble]
  · change s.infinite at hs
    simp [hs, count_apply_infinite]
#align measure_theory.measure.count_apply_eq_top' MeasureTheory.Measure.count_apply_eq_top'

@[simp]
theorem count_apply_eq_top [MeasurableSingletonClass α] : count s = ∞ ↔ s.Infinite :=
  by
  by_cases hs : s.finite
  · exact count_apply_eq_top' hs.measurable_set
  · change s.infinite at hs
    simp [hs, count_apply_infinite]
#align measure_theory.measure.count_apply_eq_top MeasureTheory.Measure.count_apply_eq_top

@[simp]
theorem count_apply_lt_top' (s_mble : MeasurableSet s) : count s < ∞ ↔ s.Finite :=
  calc
    count s < ∞ ↔ count s ≠ ∞ := lt_top_iff_ne_top
    _ ↔ ¬s.Infinite := (not_congr (count_apply_eq_top' s_mble))
    _ ↔ s.Finite := Classical.not_not
    
#align measure_theory.measure.count_apply_lt_top' MeasureTheory.Measure.count_apply_lt_top'

@[simp]
theorem count_apply_lt_top [MeasurableSingletonClass α] : count s < ∞ ↔ s.Finite :=
  calc
    count s < ∞ ↔ count s ≠ ∞ := lt_top_iff_ne_top
    _ ↔ ¬s.Infinite := (not_congr count_apply_eq_top)
    _ ↔ s.Finite := Classical.not_not
    
#align measure_theory.measure.count_apply_lt_top MeasureTheory.Measure.count_apply_lt_top

theorem empty_of_count_eq_zero' (s_mble : MeasurableSet s) (hsc : count s = 0) : s = ∅ :=
  by
  have hs : s.finite := by
    rw [← count_apply_lt_top' s_mble, hsc]
    exact WithTop.zero_lt_top
  simpa [count_apply_finite' hs s_mble] using hsc
#align measure_theory.measure.empty_of_count_eq_zero' MeasureTheory.Measure.empty_of_count_eq_zero'

theorem empty_of_count_eq_zero [MeasurableSingletonClass α] (hsc : count s = 0) : s = ∅ :=
  by
  have hs : s.finite := by
    rw [← count_apply_lt_top, hsc]
    exact WithTop.zero_lt_top
  simpa [count_apply_finite _ hs] using hsc
#align measure_theory.measure.empty_of_count_eq_zero MeasureTheory.Measure.empty_of_count_eq_zero

@[simp]
theorem count_eq_zero_iff' (s_mble : MeasurableSet s) : count s = 0 ↔ s = ∅ :=
  ⟨empty_of_count_eq_zero' s_mble, fun h => h.symm ▸ count_empty⟩
#align measure_theory.measure.count_eq_zero_iff' MeasureTheory.Measure.count_eq_zero_iff'

@[simp]
theorem count_eq_zero_iff [MeasurableSingletonClass α] : count s = 0 ↔ s = ∅ :=
  ⟨empty_of_count_eq_zero, fun h => h.symm ▸ count_empty⟩
#align measure_theory.measure.count_eq_zero_iff MeasureTheory.Measure.count_eq_zero_iff

theorem count_ne_zero' (hs' : s.Nonempty) (s_mble : MeasurableSet s) : count s ≠ 0 :=
  by
  rw [Ne.def, count_eq_zero_iff' s_mble]
  exact hs'.ne_empty
#align measure_theory.measure.count_ne_zero' MeasureTheory.Measure.count_ne_zero'

theorem count_ne_zero [MeasurableSingletonClass α] (hs' : s.Nonempty) : count s ≠ 0 :=
  by
  rw [Ne.def, count_eq_zero_iff]
  exact hs'.ne_empty
#align measure_theory.measure.count_ne_zero MeasureTheory.Measure.count_ne_zero

@[simp]
theorem count_singleton' {a : α} (ha : MeasurableSet ({a} : Set α)) : count ({a} : Set α) = 1 :=
  by
  rw [count_apply_finite' (Set.finite_singleton a) ha, Set.Finite.toFinset]
  simp
#align measure_theory.measure.count_singleton' MeasureTheory.Measure.count_singleton'

@[simp]
theorem count_singleton [MeasurableSingletonClass α] (a : α) : count ({a} : Set α) = 1 :=
  count_singleton' (measurableSet_singleton a)
#align measure_theory.measure.count_singleton MeasureTheory.Measure.count_singleton

theorem count_injective_image' {f : β → α} (hf : Function.Injective f) {s : Set β}
    (s_mble : MeasurableSet s) (fs_mble : MeasurableSet (f '' s)) : count (f '' s) = count s :=
  by
  by_cases hs : s.finite
  · lift s to Finset β using hs
    rw [← Finset.coe_image, count_apply_finset' _, count_apply_finset' s_mble,
      s.card_image_of_injective hf]
    simpa only [Finset.coe_image] using fs_mble
  rw [count_apply_infinite hs]
  rw [← finite_image_iff <| hf.inj_on _] at hs
  rw [count_apply_infinite hs]
#align measure_theory.measure.count_injective_image' MeasureTheory.Measure.count_injective_image'

theorem count_injective_image [MeasurableSingletonClass α] [MeasurableSingletonClass β] {f : β → α}
    (hf : Function.Injective f) (s : Set β) : count (f '' s) = count s :=
  by
  by_cases hs : s.finite
  · exact count_injective_image' hf hs.measurable_set (finite.image f hs).MeasurableSet
  rw [count_apply_infinite hs]
  rw [← finite_image_iff <| hf.inj_on _] at hs
  rw [count_apply_infinite hs]
#align measure_theory.measure.count_injective_image MeasureTheory.Measure.count_injective_image

end Count

/-! ### Absolute continuity -/


/-- We say that `μ` is absolutely continuous with respect to `ν`, or that `μ` is dominated by `ν`,
  if `ν(A) = 0` implies that `μ(A) = 0`. -/
def AbsolutelyContinuous {m0 : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  ∀ ⦃s : Set α⦄, ν s = 0 → μ s = 0
#align measure_theory.measure.absolutely_continuous MeasureTheory.Measure.AbsolutelyContinuous

-- mathport name: measure.absolutely_continuous
scoped[MeasureTheory] infixl:50 " ≪ " => MeasureTheory.Measure.AbsolutelyContinuous

theorem absolutelyContinuousOfLe (h : μ ≤ ν) : μ ≪ ν := fun s hs =>
  nonpos_iff_eq_zero.1 <| hs ▸ le_iff'.1 h s
#align measure_theory.measure.absolutely_continuous_of_le MeasureTheory.Measure.absolutelyContinuousOfLe

alias absolutely_continuous_of_le ← _root_.has_le.le.absolutely_continuous
#align has_le.le.absolutely_continuous LE.le.absolutelyContinuous

theorem absolutelyContinuousOfEq (h : μ = ν) : μ ≪ ν :=
  h.le.AbsolutelyContinuous
#align measure_theory.measure.absolutely_continuous_of_eq MeasureTheory.Measure.absolutelyContinuousOfEq

alias absolutely_continuous_of_eq ← _root_.eq.absolutely_continuous
#align eq.absolutely_continuous Eq.absolutelyContinuous

namespace AbsolutelyContinuous

theorem mk (h : ∀ ⦃s : Set α⦄, MeasurableSet s → ν s = 0 → μ s = 0) : μ ≪ ν :=
  by
  intro s hs
  rcases exists_measurable_superset_of_null hs with ⟨t, h1t, h2t, h3t⟩
  exact measure_mono_null h1t (h h2t h3t)
#align measure_theory.measure.absolutely_continuous.mk MeasureTheory.Measure.AbsolutelyContinuous.mk

@[refl]
protected theorem refl {m0 : MeasurableSpace α} (μ : Measure α) : μ ≪ μ :=
  rfl.AbsolutelyContinuous
#align measure_theory.measure.absolutely_continuous.refl MeasureTheory.Measure.AbsolutelyContinuous.refl

protected theorem rfl : μ ≪ μ := fun s hs => hs
#align measure_theory.measure.absolutely_continuous.rfl MeasureTheory.Measure.AbsolutelyContinuous.rfl

instance [MeasurableSpace α] : IsRefl (Measure α) (· ≪ ·) :=
  ⟨fun μ => AbsolutelyContinuous.rfl⟩

@[trans]
protected theorem trans (h1 : μ₁ ≪ μ₂) (h2 : μ₂ ≪ μ₃) : μ₁ ≪ μ₃ := fun s hs => h1 <| h2 hs
#align measure_theory.measure.absolutely_continuous.trans MeasureTheory.Measure.AbsolutelyContinuous.trans

@[mono]
protected theorem map (h : μ ≪ ν) {f : α → β} (hf : Measurable f) : μ.map f ≪ ν.map f :=
  AbsolutelyContinuous.mk fun s hs => by simpa [hf, hs] using @h _
#align measure_theory.measure.absolutely_continuous.map MeasureTheory.Measure.AbsolutelyContinuous.map

protected theorem smul [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (h : μ ≪ ν)
    (c : R) : c • μ ≪ ν := fun s hνs => by simp only [h hνs, smul_eq_mul, smul_apply, smul_zero]
#align measure_theory.measure.absolutely_continuous.smul MeasureTheory.Measure.AbsolutelyContinuous.smul

end AbsolutelyContinuous

theorem absolutelyContinuousOfLeSmul {μ' : Measure α} {c : ℝ≥0∞} (hμ'_le : μ' ≤ c • μ) : μ' ≪ μ :=
  (Measure.absolutelyContinuousOfLe hμ'_le).trans (Measure.AbsolutelyContinuous.rfl.smul c)
#align measure_theory.measure.absolutely_continuous_of_le_smul MeasureTheory.Measure.absolutelyContinuousOfLeSmul

theorem ae_le_iff_absolutelyContinuous : μ.ae ≤ ν.ae ↔ μ ≪ ν :=
  ⟨fun h s => by
    rw [measure_zero_iff_ae_nmem, measure_zero_iff_ae_nmem]
    exact fun hs => h hs, fun h s hs => h hs⟩
#align measure_theory.measure.ae_le_iff_absolutely_continuous MeasureTheory.Measure.ae_le_iff_absolutelyContinuous

alias ae_le_iff_absolutely_continuous ↔
  _root_.has_le.le.absolutely_continuous_of_ae absolutely_continuous.ae_le
#align has_le.le.absolutely_continuous_of_ae LE.le.absolutelyContinuousOfAe
#align measure_theory.measure.absolutely_continuous.ae_le MeasureTheory.Measure.AbsolutelyContinuous.ae_le

alias absolutely_continuous.ae_le ← ae_mono'
#align measure_theory.measure.ae_mono' MeasureTheory.Measure.ae_mono'

theorem AbsolutelyContinuous.ae_eq (h : μ ≪ ν) {f g : α → δ} (h' : f =ᵐ[ν] g) : f =ᵐ[μ] g :=
  h.ae_le h'
#align measure_theory.measure.absolutely_continuous.ae_eq MeasureTheory.Measure.AbsolutelyContinuous.ae_eq

/-! ### Quasi measure preserving maps (a.k.a. non-singular maps) -/


/-- A map `f : α → β` is said to be *quasi measure preserving* (a.k.a. non-singular) w.r.t. measures
`μa` and `μb` if it is measurable and `μb s = 0` implies `μa (f ⁻¹' s) = 0`. -/
@[protect_proj]
structure QuasiMeasurePreserving {m0 : MeasurableSpace α} (f : α → β)
  (μa : Measure α := by exact MeasureTheory.MeasureSpace.volume)
  (μb : Measure β := by exact MeasureTheory.MeasureSpace.volume) : Prop where
  Measurable : Measurable f
  AbsolutelyContinuous : μa.map f ≪ μb
#align measure_theory.measure.quasi_measure_preserving MeasureTheory.Measure.QuasiMeasurePreserving

namespace QuasiMeasurePreserving

protected theorem id {m0 : MeasurableSpace α} (μ : Measure α) : QuasiMeasurePreserving id μ μ :=
  ⟨measurable_id, map_id.AbsolutelyContinuous⟩
#align measure_theory.measure.quasi_measure_preserving.id MeasureTheory.Measure.QuasiMeasurePreserving.id

variable {μa μa' : Measure α} {μb μb' : Measure β} {μc : Measure γ} {f : α → β}

protected theorem Measurable.quasiMeasurePreserving {m0 : MeasurableSpace α} (hf : Measurable f)
    (μ : Measure α) : QuasiMeasurePreserving f μ (μ.map f) :=
  ⟨hf, AbsolutelyContinuous.rfl⟩
#align measurable.quasi_measure_preserving Measurable.quasiMeasurePreserving

theorem monoLeft (h : QuasiMeasurePreserving f μa μb) (ha : μa' ≪ μa) :
    QuasiMeasurePreserving f μa' μb :=
  ⟨h.1, (ha.map h.1).trans h.2⟩
#align measure_theory.measure.quasi_measure_preserving.mono_left MeasureTheory.Measure.QuasiMeasurePreserving.monoLeft

theorem monoRight (h : QuasiMeasurePreserving f μa μb) (ha : μb ≪ μb') :
    QuasiMeasurePreserving f μa μb' :=
  ⟨h.1, h.2.trans ha⟩
#align measure_theory.measure.quasi_measure_preserving.mono_right MeasureTheory.Measure.QuasiMeasurePreserving.monoRight

@[mono]
theorem mono (ha : μa' ≪ μa) (hb : μb ≪ μb') (h : QuasiMeasurePreserving f μa μb) :
    QuasiMeasurePreserving f μa' μb' :=
  (h.mono_left ha).mono_right hb
#align measure_theory.measure.quasi_measure_preserving.mono MeasureTheory.Measure.QuasiMeasurePreserving.mono

protected theorem comp {g : β → γ} {f : α → β} (hg : QuasiMeasurePreserving g μb μc)
    (hf : QuasiMeasurePreserving f μa μb) : QuasiMeasurePreserving (g ∘ f) μa μc :=
  ⟨hg.Measurable.comp hf.Measurable, by
    rw [← map_map hg.1 hf.1]
    exact (hf.2.map hg.1).trans hg.2⟩
#align measure_theory.measure.quasi_measure_preserving.comp MeasureTheory.Measure.QuasiMeasurePreserving.comp

protected theorem iterate {f : α → α} (hf : QuasiMeasurePreserving f μa μa) :
    ∀ n, QuasiMeasurePreserving (f^[n]) μa μa
  | 0 => QuasiMeasurePreserving.id μa
  | n + 1 => (iterate n).comp hf
#align measure_theory.measure.quasi_measure_preserving.iterate MeasureTheory.Measure.QuasiMeasurePreserving.iterate

protected theorem aeMeasurable (hf : QuasiMeasurePreserving f μa μb) : AeMeasurable f μa :=
  hf.1.AeMeasurable
#align measure_theory.measure.quasi_measure_preserving.ae_measurable MeasureTheory.Measure.QuasiMeasurePreserving.aeMeasurable

theorem ae_map_le (h : QuasiMeasurePreserving f μa μb) : (μa.map f).ae ≤ μb.ae :=
  h.2.ae_le
#align measure_theory.measure.quasi_measure_preserving.ae_map_le MeasureTheory.Measure.QuasiMeasurePreserving.ae_map_le

theorem tendsto_ae (h : QuasiMeasurePreserving f μa μb) : Tendsto f μa.ae μb.ae :=
  (tendsto_ae_map h.AeMeasurable).mono_right h.ae_map_le
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
  preimage_null_of_map_null h.AeMeasurable (h.2 hs)
#align measure_theory.measure.quasi_measure_preserving.preimage_null MeasureTheory.Measure.QuasiMeasurePreserving.preimage_null

theorem preimage_mono_ae {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s ≤ᵐ[μb] t) :
    f ⁻¹' s ≤ᵐ[μa] f ⁻¹' t :=
  eventually_map.mp <|
    Eventually.filter_mono (tendsto_ae_map hf.AeMeasurable) (Eventually.filter_mono hf.ae_map_le h)
#align measure_theory.measure.quasi_measure_preserving.preimage_mono_ae MeasureTheory.Measure.QuasiMeasurePreserving.preimage_mono_ae

theorem preimage_ae_eq {s t : Set β} (hf : QuasiMeasurePreserving f μa μb) (h : s =ᵐ[μb] t) :
    f ⁻¹' s =ᵐ[μa] f ⁻¹' t :=
  EventuallyLE.antisymm (hf.preimage_mono_ae h.le) (hf.preimage_mono_ae h.symm.le)
#align measure_theory.measure.quasi_measure_preserving.preimage_ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.preimage_ae_eq

theorem preimage_iterate_ae_eq {s : Set α} {f : α → α} (hf : QuasiMeasurePreserving f μ μ) (k : ℕ)
    (hs : f ⁻¹' s =ᵐ[μ] s) : f^[k] ⁻¹' s =ᵐ[μ] s :=
  by
  induction' k with k ih; · simp
  rw [iterate_succ, preimage_comp]
  exact eventually_eq.trans (hf.preimage_ae_eq ih) hs
#align measure_theory.measure.quasi_measure_preserving.preimage_iterate_ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.preimage_iterate_ae_eq

theorem image_zpow_ae_eq {s : Set α} {e : α ≃ α} (he : QuasiMeasurePreserving e μ μ)
    (he' : QuasiMeasurePreserving e.symm μ μ) (k : ℤ) (hs : e '' s =ᵐ[μ] s) :
    ⇑(e ^ k) '' s =ᵐ[μ] s := by
  rw [Equiv.image_eq_preimage]
  obtain ⟨k, rfl | rfl⟩ := k.eq_coe_or_neg
  · replace hs : ⇑e⁻¹ ⁻¹' s =ᵐ[μ] s
    · rwa [Equiv.image_eq_preimage] at hs
    replace he' : ⇑e⁻¹^[k] ⁻¹' s =ᵐ[μ] s := he'.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e⁻¹ k, inv_pow e k] at he'
  · rw [zpow_neg, zpow_ofNat]
    replace hs : e ⁻¹' s =ᵐ[μ] s
    · convert he.preimage_ae_eq hs.symm
      rw [Equiv.preimage_image]
    replace he : ⇑e^[k] ⁻¹' s =ᵐ[μ] s := he.preimage_iterate_ae_eq k hs
    rwa [Equiv.Perm.iterate_eq_pow e k] at he
#align measure_theory.measure.quasi_measure_preserving.image_zpow_ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.image_zpow_ae_eq

theorem limsup_preimage_iterate_ae_eq {f : α → α} (hf : QuasiMeasurePreserving f μ μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) :-- Need `@` below because of diamond; see gh issue #16932
        @limsup
        (Set α) ℕ _ (fun n => (preimage f^[n]) s) atTop =ᵐ[μ]
      s :=
  haveI : ∀ n, (preimage f^[n]) s =ᵐ[μ] s := by
    intro n
    induction' n with n ih
    · simp
    simpa only [iterate_succ', comp_app] using ae_eq_trans (hf.ae_eq ih) hs
  (limsup_ae_eq_of_forall_ae_eq (fun n => (preimage f^[n]) s) this).trans (ae_eq_refl _)
#align measure_theory.measure.quasi_measure_preserving.limsup_preimage_iterate_ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.limsup_preimage_iterate_ae_eq

theorem liminf_preimage_iterate_ae_eq {f : α → α} (hf : QuasiMeasurePreserving f μ μ)
    (hs : f ⁻¹' s =ᵐ[μ] s) :-- Need `@` below because of diamond; see gh issue #16932
        @liminf
        (Set α) ℕ _ (fun n => (preimage f^[n]) s) atTop =ᵐ[μ]
      s :=
  by
  -- Need `@` below because of diamond; see gh issue #16932
  rw [← ae_eq_set_compl_compl, @Filter.liminf_compl (Set α)]
  rw [← ae_eq_set_compl_compl, ← preimage_compl] at hs
  convert hf.limsup_preimage_iterate_ae_eq hs
  ext1 n
  simp only [← Set.preimage_iterate_eq, comp_app, preimage_compl]
#align measure_theory.measure.quasi_measure_preserving.liminf_preimage_iterate_ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.liminf_preimage_iterate_ae_eq

/-- By replacing a measurable set that is almost invariant with the `limsup` of its preimages, we
obtain a measurable set that is almost equal and strictly invariant.

(The `liminf` would work just as well.) -/
theorem exists_preimage_eq_of_preimage_ae {f : α → α} (h : QuasiMeasurePreserving f μ μ)
    (hs : MeasurableSet s) (hs' : f ⁻¹' s =ᵐ[μ] s) :
    ∃ t : Set α, MeasurableSet t ∧ t =ᵐ[μ] s ∧ f ⁻¹' t = t :=
  ⟨limsup (fun n => (preimage f^[n]) s) atTop,
    MeasurableSet.measurableSet_limsup fun n =>
      @preimage_iterate_eq α f n ▸ h.Measurable.iterate n hs,
    h.limsup_preimage_iterate_ae_eq hs', (CompleteLatticeHom.setPreimage f).apply_limsup_iterate s⟩
#align measure_theory.measure.quasi_measure_preserving.exists_preimage_eq_of_preimage_ae MeasureTheory.Measure.QuasiMeasurePreserving.exists_preimage_eq_of_preimage_ae

open Pointwise

@[to_additive]
theorem smul_ae_eq_of_ae_eq {G α : Type _} [Group G] [MulAction G α] [MeasurableSpace α]
    {s t : Set α} {μ : Measure α} (g : G) (h_qmp : QuasiMeasurePreserving ((· • ·) g⁻¹ : α → α) μ μ)
    (h_ae_eq : s =ᵐ[μ] t) : (g • s : Set α) =ᵐ[μ] (g • t : Set α) := by
  simpa only [← preimage_smul_inv] using h_qmp.ae_eq h_ae_eq
#align measure_theory.measure.quasi_measure_preserving.smul_ae_eq_of_ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.smul_ae_eq_of_ae_eq
#align measure_theory.measure.quasi_measure_preserving.vadd_ae_eq_of_ae_eq MeasureTheory.Measure.QuasiMeasurePreserving.vadd_ae_eq_of_ae_eq

end QuasiMeasurePreserving

section Pointwise

open Pointwise

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (g «expr ≠ » (1 : G)) -/
@[to_additive]
theorem pairwise_aeDisjoint_of_aeDisjoint_forall_ne_one {G α : Type _} [Group G] [MulAction G α]
    [MeasurableSpace α] {μ : Measure α} {s : Set α}
    (h_ae_disjoint : ∀ (g) (_ : g ≠ (1 : G)), AeDisjoint μ (g • s) s)
    (h_qmp : ∀ g : G, QuasiMeasurePreserving ((· • ·) g : α → α) μ μ) :
    Pairwise (AeDisjoint μ on fun g : G => g • s) :=
  by
  intro g₁ g₂ hg
  let g := g₂⁻¹ * g₁
  replace hg : g ≠ 1
  · rw [Ne.def, inv_mul_eq_one]
    exact hg.symm
  have : (· • ·) g₂⁻¹ ⁻¹' (g • s ∩ s) = g₁ • s ∩ g₂ • s := by
    rw [preimage_eq_iff_eq_image (MulAction.bijective g₂⁻¹), image_smul, smul_set_inter, smul_smul,
      smul_smul, inv_mul_self, one_smul]
  change μ (g₁ • s ∩ g₂ • s) = 0
  exact this ▸ (h_qmp g₂⁻¹).preimage_null (h_ae_disjoint g hg)
#align measure_theory.measure.pairwise_ae_disjoint_of_ae_disjoint_forall_ne_one MeasureTheory.Measure.pairwise_aeDisjoint_of_aeDisjoint_forall_ne_one
#align measure_theory.measure.pairwise_ae_disjoint_of_ae_disjoint_forall_ne_zero MeasureTheory.Measure.pairwise_ae_disjoint_of_ae_disjoint_forall_ne_zero

end Pointwise

/-! ### The `cofinite` filter -/


/-- The filter of sets `s` such that `sᶜ` has finite measure. -/
def cofinite {m0 : MeasurableSpace α} (μ : Measure α) : Filter α
    where
  sets := { s | μ (sᶜ) < ∞ }
  univ_sets := by simp
  inter_sets s t hs ht := by
    simp only [compl_inter, mem_set_of_eq]
    calc
      μ (sᶜ ∪ tᶜ) ≤ μ (sᶜ) + μ (tᶜ) := measure_union_le _ _
      _ < ∞ := ENNReal.add_lt_top.2 ⟨hs, ht⟩
      
  sets_of_superset s t hs hst := lt_of_le_of_lt (measure_mono <| compl_subset_compl.2 hst) hs
#align measure_theory.measure.cofinite MeasureTheory.Measure.cofinite

theorem mem_cofinite : s ∈ μ.cofinite ↔ μ (sᶜ) < ∞ :=
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

/-- The preimage of a null measurable set under a (quasi) measure preserving map is a null
measurable set. -/
theorem NullMeasurableSet.preimage {ν : Measure β} {f : α → β} {t : Set β}
    (ht : NullMeasurableSet t ν) (hf : QuasiMeasurePreserving f μ ν) :
    NullMeasurableSet (f ⁻¹' t) μ :=
  ⟨f ⁻¹' toMeasurable ν t, hf.Measurable (measurableSet_toMeasurable _ _),
    hf.ae_eq ht.toMeasurable_ae_eq.symm⟩
#align measure_theory.null_measurable_set.preimage MeasureTheory.NullMeasurableSet.preimage

theorem NullMeasurableSet.monoAc (h : NullMeasurableSet s μ) (hle : ν ≪ μ) :
    NullMeasurableSet s ν :=
  h.Preimage <| (QuasiMeasurePreserving.id μ).mono_left hle
#align measure_theory.null_measurable_set.mono_ac MeasureTheory.NullMeasurableSet.monoAc

theorem NullMeasurableSet.mono (h : NullMeasurableSet s μ) (hle : ν ≤ μ) : NullMeasurableSet s ν :=
  h.monoAc hle.AbsolutelyContinuous
#align measure_theory.null_measurable_set.mono MeasureTheory.NullMeasurableSet.mono

theorem AeDisjoint.preimage {ν : Measure β} {f : α → β} {s t : Set β} (ht : AeDisjoint ν s t)
    (hf : QuasiMeasurePreserving f μ ν) : AeDisjoint μ (f ⁻¹' s) (f ⁻¹' t) :=
  hf.preimage_null ht
#align measure_theory.ae_disjoint.preimage MeasureTheory.AeDisjoint.preimage

@[simp]
theorem ae_eq_bot : μ.ae = ⊥ ↔ μ = 0 := by
  rw [← empty_mem_iff_bot, mem_ae_iff, compl_empty, measure_univ_eq_zero]
#align measure_theory.ae_eq_bot MeasureTheory.ae_eq_bot

@[simp]
theorem ae_neBot : μ.ae.ne_bot ↔ μ ≠ 0 :=
  neBot_iff.trans (not_congr ae_eq_bot)
#align measure_theory.ae_ne_bot MeasureTheory.ae_neBot

@[simp]
theorem ae_zero {m0 : MeasurableSpace α} : (0 : Measure α).ae = ⊥ :=
  ae_eq_bot.2 rfl
#align measure_theory.ae_zero MeasureTheory.ae_zero

@[mono]
theorem ae_mono (h : μ ≤ ν) : μ.ae ≤ ν.ae :=
  h.AbsolutelyContinuous.ae_le
#align measure_theory.ae_mono MeasureTheory.ae_mono

theorem mem_ae_map_iff {f : α → β} (hf : AeMeasurable f μ) {s : Set β} (hs : MeasurableSet s) :
    s ∈ (μ.map f).ae ↔ f ⁻¹' s ∈ μ.ae := by
  simp only [mem_ae_iff, map_apply_of_ae_measurable hf hs.compl, preimage_compl]
#align measure_theory.mem_ae_map_iff MeasureTheory.mem_ae_map_iff

theorem mem_ae_of_mem_ae_map {f : α → β} (hf : AeMeasurable f μ) {s : Set β}
    (hs : s ∈ (μ.map f).ae) : f ⁻¹' s ∈ μ.ae :=
  (tendsto_ae_map hf).Eventually hs
#align measure_theory.mem_ae_of_mem_ae_map MeasureTheory.mem_ae_of_mem_ae_map

theorem ae_map_iff {f : α → β} (hf : AeMeasurable f μ) {p : β → Prop}
    (hp : MeasurableSet { x | p x }) : (∀ᵐ y ∂μ.map f, p y) ↔ ∀ᵐ x ∂μ, p (f x) :=
  mem_ae_map_iff hf hp
#align measure_theory.ae_map_iff MeasureTheory.ae_map_iff

theorem ae_of_ae_map {f : α → β} (hf : AeMeasurable f μ) {p : β → Prop} (h : ∀ᵐ y ∂μ.map f, p y) :
    ∀ᵐ x ∂μ, p (f x) :=
  mem_ae_of_mem_ae_map hf h
#align measure_theory.ae_of_ae_map MeasureTheory.ae_of_ae_map

theorem ae_map_mem_range {m0 : MeasurableSpace α} (f : α → β) (hf : MeasurableSet (range f))
    (μ : Measure α) : ∀ᵐ x ∂μ.map f, x ∈ range f :=
  by
  by_cases h : AeMeasurable f μ
  · change range f ∈ (μ.map f).ae
    rw [mem_ae_map_iff h hf]
    apply eventually_of_forall
    exact mem_range_self
  · simp [map_of_not_ae_measurable h]
#align measure_theory.ae_map_mem_range MeasureTheory.ae_map_mem_range

@[simp]
theorem ae_restrict_unionᵢ_eq [Countable ι] (s : ι → Set α) :
    (μ.restrict (⋃ i, s i)).ae = ⨆ i, (μ.restrict (s i)).ae :=
  le_antisymm ((ae_sum_eq fun i => μ.restrict (s i)) ▸ ae_mono restrict_unionᵢ_le) <|
    supᵢ_le fun i => ae_mono <| restrict_mono (subset_unionᵢ s i) le_rfl
#align measure_theory.ae_restrict_Union_eq MeasureTheory.ae_restrict_unionᵢ_eq

@[simp]
theorem ae_restrict_union_eq (s t : Set α) :
    (μ.restrict (s ∪ t)).ae = (μ.restrict s).ae ⊔ (μ.restrict t).ae := by
  simp [union_eq_Union, supᵢ_bool_eq]
#align measure_theory.ae_restrict_union_eq MeasureTheory.ae_restrict_union_eq

theorem ae_restrict_bUnion_eq (s : ι → Set α) {t : Set ι} (ht : t.Countable) :
    (μ.restrict (⋃ i ∈ t, s i)).ae = ⨆ i ∈ t, (μ.restrict (s i)).ae :=
  by
  haveI := ht.to_subtype
  rw [bUnion_eq_Union, ae_restrict_Union_eq, ← supᵢ_subtype'']
#align measure_theory.ae_restrict_bUnion_eq MeasureTheory.ae_restrict_bUnion_eq

theorem ae_restrict_bUnion_finset_eq (s : ι → Set α) (t : Finset ι) :
    (μ.restrict (⋃ i ∈ t, s i)).ae = ⨆ i ∈ t, (μ.restrict (s i)).ae :=
  ae_restrict_bUnion_eq s t.countable_toSet
#align measure_theory.ae_restrict_bUnion_finset_eq MeasureTheory.ae_restrict_bUnion_finset_eq

theorem ae_restrict_unionᵢ_iff [Countable ι] (s : ι → Set α) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (⋃ i, s i), p x) ↔ ∀ i, ∀ᵐ x ∂μ.restrict (s i), p x := by simp
#align measure_theory.ae_restrict_Union_iff MeasureTheory.ae_restrict_unionᵢ_iff

theorem ae_restrict_union_iff (s t : Set α) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (s ∪ t), p x) ↔ (∀ᵐ x ∂μ.restrict s, p x) ∧ ∀ᵐ x ∂μ.restrict t, p x := by simp
#align measure_theory.ae_restrict_union_iff MeasureTheory.ae_restrict_union_iff

theorem ae_restrict_bUnion_iff (s : ι → Set α) {t : Set ι} (ht : t.Countable) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (⋃ i ∈ t, s i), p x) ↔ ∀ i ∈ t, ∀ᵐ x ∂μ.restrict (s i), p x := by
  simp_rw [Filter.Eventually, ae_restrict_bUnion_eq s ht, mem_supr]
#align measure_theory.ae_restrict_bUnion_iff MeasureTheory.ae_restrict_bUnion_iff

@[simp]
theorem ae_restrict_bUnion_finset_iff (s : ι → Set α) (t : Finset ι) (p : α → Prop) :
    (∀ᵐ x ∂μ.restrict (⋃ i ∈ t, s i), p x) ↔ ∀ i ∈ t, ∀ᵐ x ∂μ.restrict (s i), p x := by
  simp_rw [Filter.Eventually, ae_restrict_bUnion_finset_eq s, mem_supr]
#align measure_theory.ae_restrict_bUnion_finset_iff MeasureTheory.ae_restrict_bUnion_finset_iff

theorem ae_eq_restrict_unionᵢ_iff [Countable ι] (s : ι → Set α) (f g : α → δ) :
    f =ᵐ[μ.restrict (⋃ i, s i)] g ↔ ∀ i, f =ᵐ[μ.restrict (s i)] g := by
  simp_rw [eventually_eq, ae_restrict_Union_eq, eventually_supr]
#align measure_theory.ae_eq_restrict_Union_iff MeasureTheory.ae_eq_restrict_unionᵢ_iff

theorem ae_eq_restrict_bUnion_iff (s : ι → Set α) {t : Set ι} (ht : t.Countable) (f g : α → δ) :
    f =ᵐ[μ.restrict (⋃ i ∈ t, s i)] g ↔ ∀ i ∈ t, f =ᵐ[μ.restrict (s i)] g := by
  simp_rw [ae_restrict_bUnion_eq s ht, eventually_eq, eventually_supr]
#align measure_theory.ae_eq_restrict_bUnion_iff MeasureTheory.ae_eq_restrict_bUnion_iff

theorem ae_eq_restrict_bUnion_finset_iff (s : ι → Set α) (t : Finset ι) (f g : α → δ) :
    f =ᵐ[μ.restrict (⋃ i ∈ t, s i)] g ↔ ∀ i ∈ t, f =ᵐ[μ.restrict (s i)] g :=
  ae_eq_restrict_bUnion_iff s t.countable_toSet f g
#align measure_theory.ae_eq_restrict_bUnion_finset_iff MeasureTheory.ae_eq_restrict_bUnion_finset_iff

theorem ae_restrict_uIoc_eq [LinearOrder α] (a b : α) :
    (μ.restrict (Ι a b)).ae = (μ.restrict (Ioc a b)).ae ⊔ (μ.restrict (Ioc b a)).ae := by
  simp only [uIoc_eq_union, ae_restrict_union_eq]
#align measure_theory.ae_restrict_uIoc_eq MeasureTheory.ae_restrict_uIoc_eq

/-- See also `measure_theory.ae_uIoc_iff`. -/
theorem ae_restrict_uIoc_iff [LinearOrder α] {a b : α} {P : α → Prop} :
    (∀ᵐ x ∂μ.restrict (Ι a b), P x) ↔
      (∀ᵐ x ∂μ.restrict (Ioc a b), P x) ∧ ∀ᵐ x ∂μ.restrict (Ioc b a), P x :=
  by rw [ae_restrict_uIoc_eq, eventually_sup]
#align measure_theory.ae_restrict_uIoc_iff MeasureTheory.ae_restrict_uIoc_iff

theorem ae_restrict_iff {p : α → Prop} (hp : MeasurableSet { x | p x }) :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x :=
  by
  simp only [ae_iff, ← compl_set_of, restrict_apply hp.compl]
  congr with x; simp [and_comm']
#align measure_theory.ae_restrict_iff MeasureTheory.ae_restrict_iff

theorem ae_imp_of_ae_restrict {s : Set α} {p : α → Prop} (h : ∀ᵐ x ∂μ.restrict s, p x) :
    ∀ᵐ x ∂μ, x ∈ s → p x := by
  simp only [ae_iff] at h⊢
  simpa [set_of_and, inter_comm] using measure_inter_eq_zero_of_restrict h
#align measure_theory.ae_imp_of_ae_restrict MeasureTheory.ae_imp_of_ae_restrict

theorem ae_restrict_iff' {p : α → Prop} (hs : MeasurableSet s) :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x :=
  by
  simp only [ae_iff, ← compl_set_of, restrict_apply_eq_zero' hs]
  congr with x; simp [and_comm']
#align measure_theory.ae_restrict_iff' MeasureTheory.ae_restrict_iff'

theorem Filter.EventuallyEq.restrict {f g : α → δ} {s : Set α} (hfg : f =ᵐ[μ] g) :
    f =ᵐ[μ.restrict s] g :=
  by
  -- note that we cannot use `ae_restrict_iff` since we do not require measurability
  refine' hfg.filter_mono _
  rw [measure.ae_le_iff_absolutely_continuous]
  exact measure.absolutely_continuous_of_le measure.restrict_le_self
#align filter.eventually_eq.restrict Filter.EventuallyEq.restrict

theorem ae_restrict_mem (hs : MeasurableSet s) : ∀ᵐ x ∂μ.restrict s, x ∈ s :=
  (ae_restrict_iff' hs).2 (Filter.eventually_of_forall fun x => id)
#align measure_theory.ae_restrict_mem MeasureTheory.ae_restrict_mem

theorem ae_restrict_mem₀ (hs : NullMeasurableSet s μ) : ∀ᵐ x ∂μ.restrict s, x ∈ s :=
  by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, hts, htm, ht_eq⟩
  rw [← restrict_congr_set ht_eq]
  exact (ae_restrict_mem htm).mono hts
#align measure_theory.ae_restrict_mem₀ MeasureTheory.ae_restrict_mem₀

theorem ae_restrict_of_ae {s : Set α} {p : α → Prop} (h : ∀ᵐ x ∂μ, p x) : ∀ᵐ x ∂μ.restrict s, p x :=
  Eventually.filter_mono (ae_mono Measure.restrict_le_self) h
#align measure_theory.ae_restrict_of_ae MeasureTheory.ae_restrict_of_ae

theorem ae_restrict_iff'₀ {p : α → Prop} (hs : NullMeasurableSet s μ) :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ, x ∈ s → p x :=
  by
  refine' ⟨fun h => ae_imp_of_ae_restrict h, fun h => _⟩
  filter_upwards [ae_restrict_mem₀ hs, ae_restrict_of_ae h]with x hx h'x using h'x hx
#align measure_theory.ae_restrict_iff'₀ MeasureTheory.ae_restrict_iff'₀

theorem ae_restrict_of_ae_restrict_of_subset {s t : Set α} {p : α → Prop} (hst : s ⊆ t)
    (h : ∀ᵐ x ∂μ.restrict t, p x) : ∀ᵐ x ∂μ.restrict s, p x :=
  h.filter_mono (ae_mono <| Measure.restrict_mono hst (le_refl μ))
#align measure_theory.ae_restrict_of_ae_restrict_of_subset MeasureTheory.ae_restrict_of_ae_restrict_of_subset

theorem ae_of_ae_restrict_of_ae_restrict_compl (t : Set α) {p : α → Prop}
    (ht : ∀ᵐ x ∂μ.restrict t, p x) (htc : ∀ᵐ x ∂μ.restrict (tᶜ), p x) : ∀ᵐ x ∂μ, p x :=
  nonpos_iff_eq_zero.1 <|
    calc
      μ { x | ¬p x } = μ ({ x | ¬p x } ∩ t ∪ { x | ¬p x } ∩ tᶜ) := by
        rw [← inter_union_distrib_left, union_compl_self, inter_univ]
      _ ≤ μ ({ x | ¬p x } ∩ t) + μ ({ x | ¬p x } ∩ tᶜ) := (measure_union_le _ _)
      _ ≤ μ.restrict t { x | ¬p x } + μ.restrict (tᶜ) { x | ¬p x } :=
        (add_le_add (le_restrict_apply _ _) (le_restrict_apply _ _))
      _ = 0 := by rw [ae_iff.1 ht, ae_iff.1 htc, zero_add]
      
#align measure_theory.ae_of_ae_restrict_of_ae_restrict_compl MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl

theorem mem_map_restrict_ae_iff {β} {s : Set α} {t : Set β} {f : α → β} (hs : MeasurableSet s) :
    t ∈ Filter.map f (μ.restrict s).ae ↔ μ ((f ⁻¹' t)ᶜ ∩ s) = 0 := by
  rw [mem_map, mem_ae_iff, measure.restrict_apply' hs]
#align measure_theory.mem_map_restrict_ae_iff MeasureTheory.mem_map_restrict_ae_iff

theorem ae_smul_measure {p : α → Prop} [Monoid R] [DistribMulAction R ℝ≥0∞]
    [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (h : ∀ᵐ x ∂μ, p x) (c : R) : ∀ᵐ x ∂c • μ, p x :=
  ae_iff.2 <| by rw [smul_apply, ae_iff.1 h, smul_zero]
#align measure_theory.ae_smul_measure MeasureTheory.ae_smul_measure

theorem ae_add_measure_iff {p : α → Prop} {ν} :
    (∀ᵐ x ∂μ + ν, p x) ↔ (∀ᵐ x ∂μ, p x) ∧ ∀ᵐ x ∂ν, p x :=
  add_eq_zero_iff
#align measure_theory.ae_add_measure_iff MeasureTheory.ae_add_measure_iff

theorem ae_eq_comp' {ν : Measure β} {f : α → β} {g g' : β → δ} (hf : AeMeasurable f μ)
    (h : g =ᵐ[ν] g') (h2 : μ.map f ≪ ν) : g ∘ f =ᵐ[μ] g' ∘ f :=
  (tendsto_ae_map hf).mono_right h2.ae_le h
#align measure_theory.ae_eq_comp' MeasureTheory.ae_eq_comp'

theorem Measure.QuasiMeasurePreserving.ae_eq_comp {ν : Measure β} {f : α → β} {g g' : β → δ}
    (hf : QuasiMeasurePreserving f μ ν) (h : g =ᵐ[ν] g') : g ∘ f =ᵐ[μ] g' ∘ f :=
  ae_eq_comp' hf.AeMeasurable h hf.AbsolutelyContinuous
#align measure_theory.measure.quasi_measure_preserving.ae_eq_comp MeasureTheory.Measure.QuasiMeasurePreserving.ae_eq_comp

theorem ae_eq_comp {f : α → β} {g g' : β → δ} (hf : AeMeasurable f μ) (h : g =ᵐ[μ.map f] g') :
    g ∘ f =ᵐ[μ] g' ∘ f :=
  ae_eq_comp' hf h AbsolutelyContinuous.rfl
#align measure_theory.ae_eq_comp MeasureTheory.ae_eq_comp

theorem sub_ae_eq_zero {β} [AddGroup β] (f g : α → β) : f - g =ᵐ[μ] 0 ↔ f =ᵐ[μ] g :=
  by
  refine' ⟨fun h => h.mono fun x hx => _, fun h => h.mono fun x hx => _⟩
  · rwa [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hx
  · rwa [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
#align measure_theory.sub_ae_eq_zero MeasureTheory.sub_ae_eq_zero

theorem le_ae_restrict : μ.ae ⊓ 𝓟 s ≤ (μ.restrict s).ae := fun s hs =>
  eventually_inf_principal.2 (ae_imp_of_ae_restrict hs)
#align measure_theory.le_ae_restrict MeasureTheory.le_ae_restrict

@[simp]
theorem ae_restrict_eq (hs : MeasurableSet s) : (μ.restrict s).ae = μ.ae ⊓ 𝓟 s :=
  by
  ext t
  simp only [mem_inf_principal, mem_ae_iff, restrict_apply_eq_zero' hs, compl_set_of, not_imp,
    and_comm' (_ ∈ s)]
  rfl
#align measure_theory.ae_restrict_eq MeasureTheory.ae_restrict_eq

@[simp]
theorem ae_restrict_eq_bot {s} : (μ.restrict s).ae = ⊥ ↔ μ s = 0 :=
  ae_eq_bot.trans restrict_eq_zero
#align measure_theory.ae_restrict_eq_bot MeasureTheory.ae_restrict_eq_bot

@[simp]
theorem ae_restrict_neBot {s} : (μ.restrict s).ae.ne_bot ↔ 0 < μ s :=
  neBot_iff.trans <| (not_congr ae_restrict_eq_bot).trans pos_iff_ne_zero.symm
#align measure_theory.ae_restrict_ne_bot MeasureTheory.ae_restrict_neBot

theorem self_mem_ae_restrict {s} (hs : MeasurableSet s) : s ∈ (μ.restrict s).ae := by
  simp only [ae_restrict_eq hs, exists_prop, mem_principal, mem_inf_iff] <;>
    exact ⟨_, univ_mem, s, subset.rfl, (univ_inter s).symm⟩
#align measure_theory.self_mem_ae_restrict MeasureTheory.self_mem_ae_restrict

/-- If two measurable sets are ae_eq then any proposition that is almost everywhere true on one
is almost everywhere true on the other -/
theorem ae_restrict_of_ae_eq_of_ae_restrict {s t} (hst : s =ᵐ[μ] t) {p : α → Prop} :
    (∀ᵐ x ∂μ.restrict s, p x) → ∀ᵐ x ∂μ.restrict t, p x := by simp [measure.restrict_congr_set hst]
#align measure_theory.ae_restrict_of_ae_eq_of_ae_restrict MeasureTheory.ae_restrict_of_ae_eq_of_ae_restrict

/-- If two measurable sets are ae_eq then any proposition that is almost everywhere true on one
is almost everywhere true on the other -/
theorem ae_restrict_congr_set {s t} (hst : s =ᵐ[μ] t) {p : α → Prop} :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂μ.restrict t, p x :=
  ⟨ae_restrict_of_ae_eq_of_ae_restrict hst, ae_restrict_of_ae_eq_of_ae_restrict hst.symm⟩
#align measure_theory.ae_restrict_congr_set MeasureTheory.ae_restrict_congr_set

/-- A version of the **Borel-Cantelli lemma**: if `pᵢ` is a sequence of predicates such that
`∑ μ {x | pᵢ x}` is finite, then the measure of `x` such that `pᵢ x` holds frequently as `i → ∞` (or
equivalently, `pᵢ x` holds for infinitely many `i`) is equal to zero. -/
theorem measure_setOf_frequently_eq_zero {p : ℕ → α → Prop} (hp : (∑' i, μ { x | p i x }) ≠ ∞) :
    μ { x | ∃ᶠ n in atTop, p n x } = 0 := by
  simpa only [limsup_eq_infi_supr_of_nat, frequently_at_top, set_of_forall, set_of_exists] using
    measure_limsup_eq_zero hp
#align measure_theory.measure_set_of_frequently_eq_zero MeasureTheory.measure_setOf_frequently_eq_zero

/-- A version of the **Borel-Cantelli lemma**: if `sᵢ` is a sequence of sets such that
`∑ μ sᵢ` exists, then for almost all `x`, `x` does not belong to almost all `sᵢ`. -/
theorem ae_eventually_not_mem {s : ℕ → Set α} (hs : (∑' i, μ (s i)) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ s n :=
  measure_setOf_frequently_eq_zero hs
#align measure_theory.ae_eventually_not_mem MeasureTheory.ae_eventually_not_mem

section Intervals

theorem bsupr_measure_Iic [Preorder α] {s : Set α} (hsc : s.Countable)
    (hst : ∀ x : α, ∃ y ∈ s, x ≤ y) (hdir : DirectedOn (· ≤ ·) s) : (⨆ x ∈ s, μ (Iic x)) = μ univ :=
  by
  rw [← measure_bUnion_eq_supr hsc]
  · congr
    exact Union₂_eq_univ_iff.2 hst
  · exact directedOn_iff_directed.2 (hdir.directed_coe.mono_comp _ fun x y => Iic_subset_Iic.2)
#align measure_theory.bsupr_measure_Iic MeasureTheory.bsupr_measure_Iic

variable [PartialOrder α] {a b : α}

theorem Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ[μ] Iic a := by
  rw [← Iic_diff_right, diff_ae_eq_self, measure_mono_null (Set.inter_subset_right _ _) ha]
#align measure_theory.Iio_ae_eq_Iic' MeasureTheory.Iio_ae_eq_Iic'

theorem Ioi_ae_eq_Ici' (ha : μ {a} = 0) : Ioi a =ᵐ[μ] Ici a :=
  @Iio_ae_eq_Iic' αᵒᵈ ‹_› ‹_› _ _ ha
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

section Dirac

variable [MeasurableSpace α]

theorem mem_ae_dirac_iff {a : α} (hs : MeasurableSet s) : s ∈ (dirac a).ae ↔ a ∈ s := by
  by_cases a ∈ s <;> simp [mem_ae_iff, dirac_apply', hs.compl, indicator_apply, *]
#align measure_theory.mem_ae_dirac_iff MeasureTheory.mem_ae_dirac_iff

theorem ae_dirac_iff {a : α} {p : α → Prop} (hp : MeasurableSet { x | p x }) :
    (∀ᵐ x ∂dirac a, p x) ↔ p a :=
  mem_ae_dirac_iff hp
#align measure_theory.ae_dirac_iff MeasureTheory.ae_dirac_iff

@[simp]
theorem ae_dirac_eq [MeasurableSingletonClass α] (a : α) : (dirac a).ae = pure a :=
  by
  ext s
  simp [mem_ae_iff, imp_false]
#align measure_theory.ae_dirac_eq MeasureTheory.ae_dirac_eq

theorem ae_eq_dirac' [MeasurableSingletonClass β] {a : α} {f : α → β} (hf : Measurable f) :
    f =ᵐ[dirac a] const α (f a) :=
  (ae_dirac_iff <| show MeasurableSet (f ⁻¹' {f a}) from hf <| measurableSet_singleton _).2 rfl
#align measure_theory.ae_eq_dirac' MeasureTheory.ae_eq_dirac'

theorem ae_eq_dirac [MeasurableSingletonClass α] {a : α} (f : α → δ) :
    f =ᵐ[dirac a] const α (f a) := by simp [Filter.EventuallyEq]
#align measure_theory.ae_eq_dirac MeasureTheory.ae_eq_dirac

end Dirac

section IsFiniteMeasure

include m0

/-- A measure `μ` is called finite if `μ univ < ∞`. -/
class IsFiniteMeasure (μ : Measure α) : Prop where
  measure_univ_lt_top : μ univ < ∞
#align measure_theory.is_finite_measure MeasureTheory.IsFiniteMeasure

theorem not_isFiniteMeasure_iff : ¬IsFiniteMeasure μ ↔ μ Set.univ = ∞ :=
  by
  refine' ⟨fun h => _, fun h => fun h' => h'.measure_univ_lt_top.ne h⟩
  by_contra h'
  exact h ⟨lt_top_iff_ne_top.mpr h'⟩
#align measure_theory.not_is_finite_measure_iff MeasureTheory.not_isFiniteMeasure_iff

instance Restrict.isFiniteMeasure (μ : Measure α) [hs : Fact (μ s < ∞)] :
    IsFiniteMeasure (μ.restrict s) :=
  ⟨by simp [hs.elim]⟩
#align measure_theory.restrict.is_finite_measure MeasureTheory.Restrict.isFiniteMeasure

theorem measure_lt_top (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s < ∞ :=
  (measure_mono (subset_univ s)).trans_lt IsFiniteMeasure.measure_univ_lt_top
#align measure_theory.measure_lt_top MeasureTheory.measure_lt_top

instance isFiniteMeasureRestrict (μ : Measure α) (s : Set α) [h : IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.restrict s) :=
  ⟨by simp [measure_lt_top μ s]⟩
#align measure_theory.is_finite_measure_restrict MeasureTheory.isFiniteMeasureRestrict

theorem measure_ne_top (μ : Measure α) [IsFiniteMeasure μ] (s : Set α) : μ s ≠ ∞ :=
  ne_of_lt (measure_lt_top μ s)
#align measure_theory.measure_ne_top MeasureTheory.measure_ne_top

theorem measure_compl_le_add_of_le_add [IsFiniteMeasure μ] (hs : MeasurableSet s)
    (ht : MeasurableSet t) {ε : ℝ≥0∞} (h : μ s ≤ μ t + ε) : μ (tᶜ) ≤ μ (sᶜ) + ε :=
  by
  rw [measure_compl ht (measure_ne_top μ _), measure_compl hs (measure_ne_top μ _),
    tsub_le_iff_right]
  calc
    μ univ = μ univ - μ s + μ s := (tsub_add_cancel_of_le <| measure_mono s.subset_univ).symm
    _ ≤ μ univ - μ s + (μ t + ε) := (add_le_add_left h _)
    _ = _ := by rw [add_right_comm, add_assoc]
    
#align measure_theory.measure_compl_le_add_of_le_add MeasureTheory.measure_compl_le_add_of_le_add

theorem measure_compl_le_add_iff [IsFiniteMeasure μ] (hs : MeasurableSet s) (ht : MeasurableSet t)
    {ε : ℝ≥0∞} : μ (sᶜ) ≤ μ (tᶜ) + ε ↔ μ t ≤ μ s + ε :=
  ⟨fun h => compl_compl s ▸ compl_compl t ▸ measure_compl_le_add_of_le_add hs.compl ht.compl h,
    measure_compl_le_add_of_le_add ht hs⟩
#align measure_theory.measure_compl_le_add_iff MeasureTheory.measure_compl_le_add_iff

/-- The measure of the whole space with respect to a finite measure, considered as `ℝ≥0`. -/
def measureUnivNnreal (μ : Measure α) : ℝ≥0 :=
  (μ univ).toNNReal
#align measure_theory.measure_univ_nnreal MeasureTheory.measureUnivNnreal

@[simp]
theorem coe_measureUnivNnreal (μ : Measure α) [IsFiniteMeasure μ] :
    ↑(measureUnivNnreal μ) = μ univ :=
  ENNReal.coe_toNNReal (measure_ne_top μ univ)
#align measure_theory.coe_measure_univ_nnreal MeasureTheory.coe_measureUnivNnreal

instance isFiniteMeasureZero : IsFiniteMeasure (0 : Measure α) :=
  ⟨by simp⟩
#align measure_theory.is_finite_measure_zero MeasureTheory.isFiniteMeasureZero

instance (priority := 100) isFiniteMeasureOfIsEmpty [IsEmpty α] : IsFiniteMeasure μ :=
  by
  rw [eq_zero_of_is_empty μ]
  infer_instance
#align measure_theory.is_finite_measure_of_is_empty MeasureTheory.isFiniteMeasureOfIsEmpty

@[simp]
theorem measureUnivNnreal_zero : measureUnivNnreal (0 : Measure α) = 0 :=
  rfl
#align measure_theory.measure_univ_nnreal_zero MeasureTheory.measureUnivNnreal_zero

omit m0

instance isFiniteMeasureAdd [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteMeasure (μ + ν)
    where measure_univ_lt_top :=
    by
    rw [measure.coe_add, Pi.add_apply, ENNReal.add_lt_top]
    exact ⟨measure_lt_top _ _, measure_lt_top _ _⟩
#align measure_theory.is_finite_measure_add MeasureTheory.isFiniteMeasureAdd

instance isFiniteMeasureSmulNnreal [IsFiniteMeasure μ] {r : ℝ≥0} : IsFiniteMeasure (r • μ)
    where measure_univ_lt_top := ENNReal.mul_lt_top ENNReal.coe_ne_top (measure_ne_top _ _)
#align measure_theory.is_finite_measure_smul_nnreal MeasureTheory.isFiniteMeasureSmulNnreal

instance isFiniteMeasureSmulOfNnrealTower {R} [SMul R ℝ≥0] [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0 ℝ≥0∞]
    [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [IsFiniteMeasure μ] {r : R} : IsFiniteMeasure (r • μ) :=
  by
  rw [← smul_one_smul ℝ≥0 r μ]
  infer_instance
#align measure_theory.is_finite_measure_smul_of_nnreal_tower MeasureTheory.isFiniteMeasureSmulOfNnrealTower

theorem isFiniteMeasureOfLe (μ : Measure α) [IsFiniteMeasure μ] (h : ν ≤ μ) : IsFiniteMeasure ν :=
  { measure_univ_lt_top := lt_of_le_of_lt (h Set.univ MeasurableSet.univ) (measure_lt_top _ _) }
#align measure_theory.is_finite_measure_of_le MeasureTheory.isFiniteMeasureOfLe

@[instance]
theorem Measure.isFiniteMeasureMap {m : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → β) : IsFiniteMeasure (μ.map f) :=
  by
  by_cases hf : AeMeasurable f μ
  · constructor
    rw [map_apply_of_ae_measurable hf MeasurableSet.univ]
    exact measure_lt_top μ _
  · rw [map_of_not_ae_measurable hf]
    exact MeasureTheory.isFiniteMeasureZero
#align measure_theory.measure.is_finite_measure_map MeasureTheory.Measure.isFiniteMeasureMap

@[simp]
theorem measureUnivNnreal_eq_zero [IsFiniteMeasure μ] : measureUnivNnreal μ = 0 ↔ μ = 0 :=
  by
  rw [← MeasureTheory.Measure.measure_univ_eq_zero, ← coe_measure_univ_nnreal]
  norm_cast
#align measure_theory.measure_univ_nnreal_eq_zero MeasureTheory.measureUnivNnreal_eq_zero

theorem measureUnivNnreal_pos [IsFiniteMeasure μ] (hμ : μ ≠ 0) : 0 < measureUnivNnreal μ :=
  by
  contrapose! hμ
  simpa [measure_univ_nnreal_eq_zero, le_zero_iff] using hμ
#align measure_theory.measure_univ_nnreal_pos MeasureTheory.measureUnivNnreal_pos

/-- `le_of_add_le_add_left` is normally applicable to `ordered_cancel_add_comm_monoid`,
but it holds for measures with the additional assumption that μ is finite. -/
theorem Measure.le_of_add_le_add_left [IsFiniteMeasure μ] (A2 : μ + ν₁ ≤ μ + ν₂) : ν₁ ≤ ν₂ :=
  fun S B1 => ENNReal.le_of_add_le_add_left (MeasureTheory.measure_ne_top μ S) (A2 S B1)
#align measure_theory.measure.le_of_add_le_add_left MeasureTheory.Measure.le_of_add_le_add_left

theorem summable_measure_toReal [hμ : IsFiniteMeasure μ] {f : ℕ → Set α}
    (hf₁ : ∀ i : ℕ, MeasurableSet (f i)) (hf₂ : Pairwise (Disjoint on f)) :
    Summable fun x => (μ (f x)).toReal :=
  by
  apply ENNReal.summable_toReal
  rw [← MeasureTheory.measure_unionᵢ hf₂ hf₁]
  exact ne_of_lt (measure_lt_top _ _)
#align measure_theory.summable_measure_to_real MeasureTheory.summable_measure_toReal

theorem ae_eq_univ_iff_measure_eq [IsFiniteMeasure μ] (hs : NullMeasurableSet s μ) :
    s =ᵐ[μ] univ ↔ μ s = μ univ :=
  by
  refine' ⟨measure_congr, fun h => _⟩
  obtain ⟨t, -, ht₁, ht₂⟩ := hs.exists_measurable_subset_ae_eq
  exact
    ht₂.symm.trans
      (ae_eq_of_subset_of_measure_ge (subset_univ t) (Eq.le ((measure_congr ht₂).trans h).symm) ht₁
        (measure_ne_top μ univ))
#align measure_theory.ae_eq_univ_iff_measure_eq MeasureTheory.ae_eq_univ_iff_measure_eq

theorem ae_iff_measure_eq [IsFiniteMeasure μ] {p : α → Prop}
    (hp : NullMeasurableSet { a | p a } μ) : (∀ᵐ a ∂μ, p a) ↔ μ { a | p a } = μ univ := by
  rw [← ae_eq_univ_iff_measure_eq hp, eventually_eq_univ, eventually_iff]
#align measure_theory.ae_iff_measure_eq MeasureTheory.ae_iff_measure_eq

theorem ae_mem_iff_measure_eq [IsFiniteMeasure μ] {s : Set α} (hs : NullMeasurableSet s μ) :
    (∀ᵐ a ∂μ, a ∈ s) ↔ μ s = μ univ :=
  ae_iff_measure_eq hs
#align measure_theory.ae_mem_iff_measure_eq MeasureTheory.ae_mem_iff_measure_eq

instance [Finite α] [MeasurableSpace α] : IsFiniteMeasure (Measure.count : Measure α) :=
  ⟨by
    cases nonempty_fintype α
    simpa [measure.count_apply, tsum_fintype] using (ENNReal.nat_ne_top _).lt_top⟩

end IsFiniteMeasure

section IsProbabilityMeasure

include m0

/-- A measure `μ` is called a probability measure if `μ univ = 1`. -/
class IsProbabilityMeasure (μ : Measure α) : Prop where
  measure_univ : μ univ = 1
#align measure_theory.is_probability_measure MeasureTheory.IsProbabilityMeasure

export IsProbabilityMeasure (measure_univ)

attribute [simp] is_probability_measure.measure_univ

instance (priority := 100) IsProbabilityMeasure.toIsFiniteMeasure (μ : Measure α)
    [IsProbabilityMeasure μ] : IsFiniteMeasure μ :=
  ⟨by simp only [measure_univ, ENNReal.one_lt_top]⟩
#align measure_theory.is_probability_measure.to_is_finite_measure MeasureTheory.IsProbabilityMeasure.toIsFiniteMeasure

theorem IsProbabilityMeasure.ne_zero (μ : Measure α) [IsProbabilityMeasure μ] : μ ≠ 0 :=
  mt measure_univ_eq_zero.2 <| by simp [measure_univ]
#align measure_theory.is_probability_measure.ne_zero MeasureTheory.IsProbabilityMeasure.ne_zero

instance (priority := 200) IsProbabilityMeasure.ae_neBot [IsProbabilityMeasure μ] : NeBot μ.ae :=
  ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
#align measure_theory.is_probability_measure.ae_ne_bot MeasureTheory.IsProbabilityMeasure.ae_neBot

omit m0

instance Measure.dirac.isProbabilityMeasure [MeasurableSpace α] {x : α} :
    IsProbabilityMeasure (dirac x) :=
  ⟨dirac_apply_of_mem <| mem_univ x⟩
#align measure_theory.measure.dirac.is_probability_measure MeasureTheory.Measure.dirac.isProbabilityMeasure

theorem prob_add_prob_compl [IsProbabilityMeasure μ] (h : MeasurableSet s) : μ s + μ (sᶜ) = 1 :=
  (measure_add_measure_compl h).trans measure_univ
#align measure_theory.prob_add_prob_compl MeasureTheory.prob_add_prob_compl

theorem prob_le_one [IsProbabilityMeasure μ] : μ s ≤ 1 :=
  (measure_mono <| Set.subset_univ _).trans_eq measure_univ
#align measure_theory.prob_le_one MeasureTheory.prob_le_one

theorem isProbabilityMeasureSmul [IsFiniteMeasure μ] (h : μ ≠ 0) :
    IsProbabilityMeasure ((μ univ)⁻¹ • μ) :=
  by
  constructor
  rw [smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel]
  · rwa [Ne, measure_univ_eq_zero]
  · exact measure_ne_top _ _
#align measure_theory.is_probability_measure_smul MeasureTheory.isProbabilityMeasureSmul

theorem isProbabilityMeasureMap [IsProbabilityMeasure μ] {f : α → β} (hf : AeMeasurable f μ) :
    IsProbabilityMeasure (map f μ) :=
  ⟨by simp [map_apply_of_ae_measurable, hf]⟩
#align measure_theory.is_probability_measure_map MeasureTheory.isProbabilityMeasureMap

@[simp]
theorem one_le_prob_iff [IsProbabilityMeasure μ] : 1 ≤ μ s ↔ μ s = 1 :=
  ⟨fun h => le_antisymm prob_le_one h, fun h => h ▸ le_refl _⟩
#align measure_theory.one_le_prob_iff MeasureTheory.one_le_prob_iff

/-- Note that this is not quite as useful as it looks because the measure takes values in `ℝ≥0∞`.
Thus the subtraction appearing is the truncated subtraction of `ℝ≥0∞`, rather than the
better-behaved subtraction of `ℝ`. -/
theorem prob_compl_eq_one_sub [IsProbabilityMeasure μ] (hs : MeasurableSet s) : μ (sᶜ) = 1 - μ s :=
  by simpa only [measure_univ] using measure_compl hs (measure_lt_top μ s).Ne
#align measure_theory.prob_compl_eq_one_sub MeasureTheory.prob_compl_eq_one_sub

@[simp]
theorem prob_compl_eq_zero_iff [IsProbabilityMeasure μ] (hs : MeasurableSet s) :
    μ (sᶜ) = 0 ↔ μ s = 1 := by
  simp only [prob_compl_eq_one_sub hs, tsub_eq_zero_iff_le, one_le_prob_iff]
#align measure_theory.prob_compl_eq_zero_iff MeasureTheory.prob_compl_eq_zero_iff

@[simp]
theorem prob_compl_eq_one_iff [IsProbabilityMeasure μ] (hs : MeasurableSet s) :
    μ (sᶜ) = 1 ↔ μ s = 0 := by rwa [← prob_compl_eq_zero_iff hs.compl, compl_compl]
#align measure_theory.prob_compl_eq_one_iff MeasureTheory.prob_compl_eq_one_iff

end IsProbabilityMeasure

section NoAtoms

/-- Measure `μ` *has no atoms* if the measure of each singleton is zero.

NB: Wikipedia assumes that for any measurable set `s` with positive `μ`-measure,
there exists a measurable `t ⊆ s` such that `0 < μ t < μ s`. While this implies `μ {x} = 0`,
the converse is not true. -/
class HasNoAtoms {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  measure_singleton : ∀ x, μ {x} = 0
#align measure_theory.has_no_atoms MeasureTheory.HasNoAtoms

export HasNoAtoms (measure_singleton)

attribute [simp] measure_singleton

variable [HasNoAtoms μ]

theorem Set.Subsingleton.measure_zero {α : Type _} {m : MeasurableSpace α} {s : Set α}
    (hs : s.Subsingleton) (μ : Measure α) [HasNoAtoms μ] : μ s = 0 :=
  hs.inductionOn measure_empty measure_singleton
#align set.subsingleton.measure_zero Set.Subsingleton.measure_zero

theorem Measure.restrict_singleton' {a : α} : μ.restrict {a} = 0 := by
  simp only [measure_singleton, measure.restrict_eq_zero]
#align measure_theory.measure.restrict_singleton' MeasureTheory.Measure.restrict_singleton'

instance (s : Set α) : HasNoAtoms (μ.restrict s) :=
  by
  refine' ⟨fun x => _⟩
  obtain ⟨t, hxt, ht1, ht2⟩ := exists_measurable_superset_of_null (measure_singleton x : μ {x} = 0)
  apply measure_mono_null hxt
  rw [measure.restrict_apply ht1]
  apply measure_mono_null (inter_subset_left t s) ht2

theorem Set.Countable.measure_zero {α : Type _} {m : MeasurableSpace α} {s : Set α}
    (h : s.Countable) (μ : Measure α) [HasNoAtoms μ] : μ s = 0 :=
  by
  rw [← bUnion_of_singleton s, ← nonpos_iff_eq_zero]
  refine' le_trans (measure_bUnion_le h _) _
  simp
#align set.countable.measure_zero Set.Countable.measure_zero

theorem Set.Countable.ae_not_mem {α : Type _} {m : MeasurableSpace α} {s : Set α} (h : s.Countable)
    (μ : Measure α) [HasNoAtoms μ] : ∀ᵐ x ∂μ, x ∉ s := by
  simpa only [ae_iff, Classical.not_not] using h.measure_zero μ
#align set.countable.ae_not_mem Set.Countable.ae_not_mem

theorem Set.Finite.measure_zero {α : Type _} {m : MeasurableSpace α} {s : Set α} (h : s.Finite)
    (μ : Measure α) [HasNoAtoms μ] : μ s = 0 :=
  h.Countable.measure_zero μ
#align set.finite.measure_zero Set.Finite.measure_zero

theorem Finset.measure_zero {α : Type _} {m : MeasurableSpace α} (s : Finset α) (μ : Measure α)
    [HasNoAtoms μ] : μ s = 0 :=
  s.finite_toSet.measure_zero μ
#align finset.measure_zero Finset.measure_zero

theorem insert_ae_eq_self (a : α) (s : Set α) : (insert a s : Set α) =ᵐ[μ] s :=
  union_ae_eq_right.2 <| measure_mono_null (diff_subset _ _) (measure_singleton _)
#align measure_theory.insert_ae_eq_self MeasureTheory.insert_ae_eq_self

section

variable [PartialOrder α] {a b : α}

theorem Iio_ae_eq_Iic : Iio a =ᵐ[μ] Iic a :=
  Iio_ae_eq_Iic' (measure_singleton a)
#align measure_theory.Iio_ae_eq_Iic MeasureTheory.Iio_ae_eq_Iic

theorem Ioi_ae_eq_Ici : Ioi a =ᵐ[μ] Ici a :=
  Ioi_ae_eq_Ici' (measure_singleton a)
#align measure_theory.Ioi_ae_eq_Ici MeasureTheory.Ioi_ae_eq_Ici

theorem Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b :=
  Ioo_ae_eq_Ioc' (measure_singleton b)
#align measure_theory.Ioo_ae_eq_Ioc MeasureTheory.Ioo_ae_eq_Ioc

theorem Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b :=
  Ioc_ae_eq_Icc' (measure_singleton a)
#align measure_theory.Ioc_ae_eq_Icc MeasureTheory.Ioc_ae_eq_Icc

theorem Ioo_ae_eq_Ico : Ioo a b =ᵐ[μ] Ico a b :=
  Ioo_ae_eq_Ico' (measure_singleton a)
#align measure_theory.Ioo_ae_eq_Ico MeasureTheory.Ioo_ae_eq_Ico

theorem Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b :=
  Ioo_ae_eq_Icc' (measure_singleton a) (measure_singleton b)
#align measure_theory.Ioo_ae_eq_Icc MeasureTheory.Ioo_ae_eq_Icc

theorem Ico_ae_eq_Icc : Ico a b =ᵐ[μ] Icc a b :=
  Ico_ae_eq_Icc' (measure_singleton b)
#align measure_theory.Ico_ae_eq_Icc MeasureTheory.Ico_ae_eq_Icc

theorem Ico_ae_eq_Ioc : Ico a b =ᵐ[μ] Ioc a b :=
  Ico_ae_eq_Ioc' (measure_singleton a) (measure_singleton b)
#align measure_theory.Ico_ae_eq_Ioc MeasureTheory.Ico_ae_eq_Ioc

end

open Interval

theorem uIoc_ae_eq_interval [LinearOrder α] {a b : α} : Ι a b =ᵐ[μ] [a, b] :=
  Ioc_ae_eq_Icc
#align measure_theory.uIoc_ae_eq_interval MeasureTheory.uIoc_ae_eq_interval

end NoAtoms

theorem ite_ae_eq_of_measure_zero {γ} (f : α → γ) (g : α → γ) (s : Set α) (hs_zero : μ s = 0) :
    (fun x => ite (x ∈ s) (f x) (g x)) =ᵐ[μ] g :=
  by
  have h_ss : sᶜ ⊆ { a : α | ite (a ∈ s) (f a) (g a) = g a } := fun x hx => by
    simp [(Set.mem_compl_iff _ _).mp hx]
  refine' measure_mono_null _ hs_zero
  nth_rw 1 [← compl_compl s]
  rwa [Set.compl_subset_compl]
#align measure_theory.ite_ae_eq_of_measure_zero MeasureTheory.ite_ae_eq_of_measure_zero

theorem ite_ae_eq_of_measure_compl_zero {γ} (f : α → γ) (g : α → γ) (s : Set α)
    (hs_zero : μ (sᶜ) = 0) : (fun x => ite (x ∈ s) (f x) (g x)) =ᵐ[μ] f :=
  by
  filter_upwards [hs_zero]
  intros
  split_ifs
  rfl
#align measure_theory.ite_ae_eq_of_measure_compl_zero MeasureTheory.ite_ae_eq_of_measure_compl_zero

namespace Measure

/-- A measure is called finite at filter `f` if it is finite at some set `s ∈ f`.
Equivalently, it is eventually finite at `s` in `f.small_sets`. -/
def FiniteAtFilter {m0 : MeasurableSpace α} (μ : Measure α) (f : Filter α) : Prop :=
  ∃ s ∈ f, μ s < ∞
#align measure_theory.measure.finite_at_filter MeasureTheory.Measure.FiniteAtFilter

theorem finiteAtFilterOfFinite {m0 : MeasurableSpace α} (μ : Measure α) [IsFiniteMeasure μ]
    (f : Filter α) : μ.FiniteAtFilter f :=
  ⟨univ, univ_mem, measure_lt_top μ univ⟩
#align measure_theory.measure.finite_at_filter_of_finite MeasureTheory.Measure.finiteAtFilterOfFinite

theorem FiniteAtFilter.exists_mem_basis {f : Filter α} (hμ : FiniteAtFilter μ f) {p : ι → Prop}
    {s : ι → Set α} (hf : f.HasBasis p s) : ∃ (i : _)(hi : p i), μ (s i) < ∞ :=
  (hf.exists_iff fun s t hst ht => (measure_mono hst).trans_lt ht).1 hμ
#align measure_theory.measure.finite_at_filter.exists_mem_basis MeasureTheory.Measure.FiniteAtFilter.exists_mem_basis

theorem finiteAtBot {m0 : MeasurableSpace α} (μ : Measure α) : μ.FiniteAtFilter ⊥ :=
  ⟨∅, mem_bot, by simp only [measure_empty, WithTop.zero_lt_top]⟩
#align measure_theory.measure.finite_at_bot MeasureTheory.Measure.finiteAtBot

/-- `μ` has finite spanning sets in `C` if there is a countable sequence of sets in `C` that have
  finite measures. This structure is a type, which is useful if we want to record extra properties
  about the sets, such as that they are monotone.
  `sigma_finite` is defined in terms of this: `μ` is σ-finite if there exists a sequence of
  finite spanning sets in the collection of all measurable sets. -/
@[protect_proj, nolint has_nonempty_instance]
structure FiniteSpanningSetsIn {m0 : MeasurableSpace α} (μ : Measure α) (C : Set (Set α)) where
  Set : ℕ → Set α
  set_mem : ∀ i, Set i ∈ C
  Finite : ∀ i, μ (Set i) < ∞
  spanning : (⋃ i, Set i) = univ
#align measure_theory.measure.finite_spanning_sets_in MeasureTheory.Measure.FiniteSpanningSetsIn

end Measure

open Measure

/-- A measure `μ` is called σ-finite if there is a countable collection of sets
 `{ A i | i ∈ ℕ }` such that `μ (A i) < ∞` and `⋃ i, A i = s`. -/
class SigmaFinite {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  out' : Nonempty (μ.FiniteSpanningSetsIn univ)
#align measure_theory.sigma_finite MeasureTheory.SigmaFinite

theorem sigmaFinite_iff : SigmaFinite μ ↔ Nonempty (μ.FiniteSpanningSetsIn univ) :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
#align measure_theory.sigma_finite_iff MeasureTheory.sigmaFinite_iff

theorem SigmaFinite.out (h : SigmaFinite μ) : Nonempty (μ.FiniteSpanningSetsIn univ) :=
  h.1
#align measure_theory.sigma_finite.out MeasureTheory.SigmaFinite.out

include m0

/-- If `μ` is σ-finite it has finite spanning sets in the collection of all measurable sets. -/
def Measure.toFiniteSpanningSetsIn (μ : Measure α) [h : SigmaFinite μ] :
    μ.FiniteSpanningSetsIn { s | MeasurableSet s }
    where
  Set n := toMeasurable μ (h.out.some.Set n)
  set_mem n := measurableSet_toMeasurable _ _
  Finite n := by
    rw [measure_to_measurable]
    exact h.out.some.finite n
  spanning := eq_univ_of_subset (unionᵢ_mono fun n => subset_toMeasurable _ _) h.out.some.spanning
#align measure_theory.measure.to_finite_spanning_sets_in MeasureTheory.Measure.toFiniteSpanningSetsIn

/-- A noncomputable way to get a monotone collection of sets that span `univ` and have finite
  measure using `classical.some`. This definition satisfies monotonicity in addition to all other
  properties in `sigma_finite`. -/
def spanningSets (μ : Measure α) [SigmaFinite μ] (i : ℕ) : Set α :=
  Accumulate μ.toFiniteSpanningSetsIn.Set i
#align measure_theory.spanning_sets MeasureTheory.spanningSets

theorem monotone_spanningSets (μ : Measure α) [SigmaFinite μ] : Monotone (spanningSets μ) :=
  monotone_accumulate
#align measure_theory.monotone_spanning_sets MeasureTheory.monotone_spanningSets

theorem measurable_spanningSets (μ : Measure α) [SigmaFinite μ] (i : ℕ) :
    MeasurableSet (spanningSets μ i) :=
  MeasurableSet.unionᵢ fun j => MeasurableSet.unionᵢ fun hij => μ.toFiniteSpanningSetsIn.set_mem j
#align measure_theory.measurable_spanning_sets MeasureTheory.measurable_spanningSets

theorem measure_spanningSets_lt_top (μ : Measure α) [SigmaFinite μ] (i : ℕ) :
    μ (spanningSets μ i) < ∞ :=
  measure_bUnion_lt_top (finite_le_nat i) fun j _ => (μ.toFiniteSpanningSetsIn.Finite j).Ne
#align measure_theory.measure_spanning_sets_lt_top MeasureTheory.measure_spanningSets_lt_top

theorem unionᵢ_spanningSets (μ : Measure α) [SigmaFinite μ] : (⋃ i : ℕ, spanningSets μ i) = univ :=
  by simp_rw [spanning_sets, Union_accumulate, μ.to_finite_spanning_sets_in.spanning]
#align measure_theory.Union_spanning_sets MeasureTheory.unionᵢ_spanningSets

theorem isCountablySpanning_spanningSets (μ : Measure α) [SigmaFinite μ] :
    IsCountablySpanning (range (spanningSets μ)) :=
  ⟨spanningSets μ, mem_range_self, unionᵢ_spanningSets μ⟩
#align measure_theory.is_countably_spanning_spanning_sets MeasureTheory.isCountablySpanning_spanningSets

/-- `spanning_sets_index μ x` is the least `n : ℕ` such that `x ∈ spanning_sets μ n`. -/
def spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) : ℕ :=
  Nat.find <| unionᵢ_eq_univ_iff.1 (unionᵢ_spanningSets μ) x
#align measure_theory.spanning_sets_index MeasureTheory.spanningSetsIndex

theorem measurable_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] :
    Measurable (spanningSetsIndex μ) :=
  measurable_find _ <| measurable_spanningSets μ
#align measure_theory.measurable_spanning_sets_index MeasureTheory.measurable_spanningSetsIndex

theorem preimage_spanningSetsIndex_singleton (μ : Measure α) [SigmaFinite μ] (n : ℕ) :
    spanningSetsIndex μ ⁻¹' {n} = disjointed (spanningSets μ) n :=
  preimage_find_eq_disjointed _ _ _
#align measure_theory.preimage_spanning_sets_index_singleton MeasureTheory.preimage_spanningSetsIndex_singleton

theorem spanningSetsIndex_eq_iff (μ : Measure α) [SigmaFinite μ] {x : α} {n : ℕ} :
    spanningSetsIndex μ x = n ↔ x ∈ disjointed (spanningSets μ) n := by
  convert Set.ext_iff.1 (preimage_spanning_sets_index_singleton μ n) x
#align measure_theory.spanning_sets_index_eq_iff MeasureTheory.spanningSetsIndex_eq_iff

theorem mem_disjointed_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) :
    x ∈ disjointed (spanningSets μ) (spanningSetsIndex μ x) :=
  (spanningSetsIndex_eq_iff μ).1 rfl
#align measure_theory.mem_disjointed_spanning_sets_index MeasureTheory.mem_disjointed_spanningSetsIndex

theorem mem_spanningSetsIndex (μ : Measure α) [SigmaFinite μ] (x : α) :
    x ∈ spanningSets μ (spanningSetsIndex μ x) :=
  disjointed_subset _ _ (mem_disjointed_spanningSetsIndex μ x)
#align measure_theory.mem_spanning_sets_index MeasureTheory.mem_spanningSetsIndex

theorem mem_spanningSets_of_index_le (μ : Measure α) [SigmaFinite μ] (x : α) {n : ℕ}
    (hn : spanningSetsIndex μ x ≤ n) : x ∈ spanningSets μ n :=
  monotone_spanningSets μ hn (mem_spanningSetsIndex μ x)
#align measure_theory.mem_spanning_sets_of_index_le MeasureTheory.mem_spanningSets_of_index_le

theorem eventually_mem_spanningSets (μ : Measure α) [SigmaFinite μ] (x : α) :
    ∀ᶠ n in atTop, x ∈ spanningSets μ n :=
  eventually_atTop.2 ⟨spanningSetsIndex μ x, fun b => mem_spanningSets_of_index_le μ x⟩
#align measure_theory.eventually_mem_spanning_sets MeasureTheory.eventually_mem_spanningSets

omit m0

namespace Measure

theorem supᵢ_restrict_spanningSets [SigmaFinite μ] (hs : MeasurableSet s) :
    (⨆ i, μ.restrict (spanningSets μ i) s) = μ s :=
  calc
    (⨆ i, μ.restrict (spanningSets μ i) s) = μ.restrict (⋃ i, spanningSets μ i) s :=
      (restrict_unionᵢ_apply_eq_supᵢ (directed_of_sup (monotone_spanningSets μ)) hs).symm
    _ = μ s := by rw [Union_spanning_sets, restrict_univ]
    
#align measure_theory.measure.supr_restrict_spanning_sets MeasureTheory.Measure.supᵢ_restrict_spanningSets

/-- In a σ-finite space, any measurable set of measure `> r` contains a measurable subset of
finite measure `> r`. -/
theorem exists_subset_measure_lt_top [SigmaFinite μ] {r : ℝ≥0∞} (hs : MeasurableSet s)
    (h's : r < μ s) : ∃ t, MeasurableSet t ∧ t ⊆ s ∧ r < μ t ∧ μ t < ∞ :=
  by
  rw [← supr_restrict_spanning_sets hs,
    @lt_supᵢ_iff _ _ _ r fun i : ℕ => μ.restrict (spanning_sets μ i) s] at h's
  rcases h's with ⟨n, hn⟩
  simp only [restrict_apply hs] at hn
  refine'
    ⟨s ∩ spanning_sets μ n, hs.inter (measurable_spanning_sets _ _), inter_subset_left _ _, hn, _⟩
  exact (measure_mono (inter_subset_right _ _)).trans_lt (measure_spanning_sets_lt_top _ _)
#align measure_theory.measure.exists_subset_measure_lt_top MeasureTheory.Measure.exists_subset_measure_lt_top

/-- A set in a σ-finite space has zero measure if and only if its intersection with
all members of the countable family of finite measure spanning sets has zero measure. -/
theorem forall_measure_inter_spanningSets_eq_zero [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] (s : Set α) : (∀ n, μ (s ∩ spanningSets μ n) = 0) ↔ μ s = 0 :=
  by
  nth_rw 1 [show s = ⋃ n, s ∩ spanning_sets μ n by
      rw [← inter_Union, Union_spanning_sets, inter_univ]]
  rw [measure_Union_null_iff]
#align measure_theory.measure.forall_measure_inter_spanning_sets_eq_zero MeasureTheory.Measure.forall_measure_inter_spanningSets_eq_zero

/-- A set in a σ-finite space has positive measure if and only if its intersection with
some member of the countable family of finite measure spanning sets has positive measure. -/
theorem exists_measure_inter_spanningSets_pos [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    (s : Set α) : (∃ n, 0 < μ (s ∩ spanningSets μ n)) ↔ 0 < μ s :=
  by
  rw [← not_iff_not]
  simp only [not_exists, not_lt, nonpos_iff_eq_zero]
  exact forall_measure_inter_spanning_sets_eq_zero s
#align measure_theory.measure.exists_measure_inter_spanning_sets_pos MeasureTheory.Measure.exists_measure_inter_spanningSets_pos

/-- If the union of disjoint measurable sets has finite measure, then there are only
finitely many members of the union whose measure exceeds any given positive number. -/
theorem finite_const_le_meas_of_disjoint_unionᵢ {ι : Type _} [MeasurableSpace α] (μ : Measure α)
    {ε : ℝ≥0∞} (ε_pos : 0 < ε) {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) (Union_As_finite : μ (⋃ i, As i) ≠ ∞) :
    Set.Finite { i : ι | ε ≤ μ (As i) } := by
  by_contra con
  have aux :=
    lt_of_le_of_lt (tsum_meas_le_meas_Union_of_disjoint μ As_mble As_disj)
      (lt_top_iff_ne_top.mpr Union_As_finite)
  exact Con (ENNReal.finite_const_le_of_tsum_ne_top aux.ne ε_pos.ne.symm)
#align measure_theory.measure.finite_const_le_meas_of_disjoint_Union MeasureTheory.Measure.finite_const_le_meas_of_disjoint_unionᵢ

/-- If the union of disjoint measurable sets has finite measure, then there are only
countably many members of the union whose measure is positive. -/
theorem countable_meas_pos_of_disjoint_of_meas_unionᵢ_ne_top {ι : Type _} [MeasurableSpace α]
    (μ : Measure α) {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) (Union_As_finite : μ (⋃ i, As i) ≠ ∞) :
    Set.Countable { i : ι | 0 < μ (As i) } :=
  by
  set posmeas := { i : ι | 0 < μ (As i) } with posmeas_def
  rcases exists_seq_strictAnti_tendsto' (zero_lt_one : (0 : ℝ≥0∞) < 1) with
    ⟨as, as_decr, as_mem, as_lim⟩
  set fairmeas := fun n : ℕ => { i : ι | as n ≤ μ (As i) } with fairmeas_def
  have countable_union : posmeas = ⋃ n, fairmeas n :=
    by
    have fairmeas_eq : ∀ n, fairmeas n = (fun i => μ (As i)) ⁻¹' Ici (as n) := fun n => by
      simpa only [fairmeas_def]
    simpa only [fairmeas_eq, posmeas_def, ← preimage_Union,
      unionᵢ_Ici_eq_Ioi_of_lt_of_tendsto (0 : ℝ≥0∞) (fun n => (as_mem n).1) as_lim]
  rw [countable_union]
  refine' countable_Union fun n => finite.countable _
  refine' finite_const_le_meas_of_disjoint_Union μ (as_mem n).1 As_mble As_disj Union_As_finite
#align measure_theory.measure.countable_meas_pos_of_disjoint_of_meas_Union_ne_top MeasureTheory.Measure.countable_meas_pos_of_disjoint_of_meas_unionᵢ_ne_top

/-- In a σ-finite space, among disjoint measurable sets, only countably many can have positive
measure. -/
theorem countable_meas_pos_of_disjoint_Union {ι : Type _} [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) : Set.Countable { i : ι | 0 < μ (As i) } :=
  by
  have obs : { i : ι | 0 < μ (As i) } ⊆ ⋃ n, { i : ι | 0 < μ (As i ∩ spanning_sets μ n) } :=
    by
    intro i i_in_nonzeroes
    by_contra con
    simp only [mem_Union, mem_set_of_eq, not_exists, not_lt, nonpos_iff_eq_zero] at *
    simpa [(forall_measure_inter_spanning_sets_eq_zero _).mp Con] using i_in_nonzeroes
  apply countable.mono obs
  refine' countable_Union fun n => countable_meas_pos_of_disjoint_of_meas_Union_ne_top μ _ _ _
  · exact fun i => MeasurableSet.inter (As_mble i) (measurable_spanning_sets μ n)
  ·
    exact fun i j i_ne_j b hbi hbj =>
      As_disj i_ne_j (hbi.trans (inter_subset_left _ _)) (hbj.trans (inter_subset_left _ _))
  · refine' (lt_of_le_of_lt (measure_mono _) (measure_spanning_sets_lt_top μ n)).Ne
    exact Union_subset fun i => inter_subset_right _ _
#align measure_theory.measure.countable_meas_pos_of_disjoint_Union MeasureTheory.Measure.countable_meas_pos_of_disjoint_Union

theorem countable_meas_level_set_pos {α β : Type _} [MeasurableSpace α] {μ : Measure α}
    [SigmaFinite μ] [MeasurableSpace β] [MeasurableSingletonClass β] {g : α → β}
    (g_mble : Measurable g) : Set.Countable { t : β | 0 < μ { a : α | g a = t } } :=
  haveI level_sets_disjoint : Pairwise (Disjoint on fun t : β => { a : α | g a = t }) :=
    fun s t hst => Disjoint.preimage g (disjoint_singleton.mpr hst)
  measure.countable_meas_pos_of_disjoint_Union
    (fun b => g_mble (‹MeasurableSingletonClass β›.measurableSet_singleton b)) level_sets_disjoint
#align measure_theory.measure.countable_meas_level_set_pos MeasureTheory.Measure.countable_meas_level_set_pos

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t' «expr ⊇ » t) -/
/-- If a set `t` is covered by a countable family of finite measure sets, then its measurable
superset `to_measurable μ t` (which has the same measure as `t`) satisfies,
for any measurable set `s`, the equality `μ (to_measurable μ t ∩ s) = μ (t ∩ s)`. -/
theorem measure_toMeasurable_inter_of_cover {s : Set α} (hs : MeasurableSet s) {t : Set α}
    {v : ℕ → Set α} (hv : t ⊆ ⋃ n, v n) (h'v : ∀ n, μ (t ∩ v n) ≠ ∞) :
    μ (toMeasurable μ t ∩ s) = μ (t ∩ s) :=
  by
  -- we show that there is a measurable superset of `t` satisfying the conclusion for any
  -- measurable set `s`. It is built on each member of a spanning family using `to_measurable`
  -- (which is well behaved for finite measure sets thanks to `measure_to_measurable_inter`), and
  -- the desired property passes to the union.
  have A :
    ∃ (t' : _)(_ : t' ⊇ t), MeasurableSet t' ∧ ∀ u, MeasurableSet u → μ (t' ∩ u) = μ (t ∩ u) :=
    by
    let w n := to_measurable μ (t ∩ v n)
    have hw : ∀ n, μ (w n) < ∞ := by
      intro n
      simp_rw [w, measure_to_measurable]
      exact (h'v n).lt_top
    set t' := ⋃ n, to_measurable μ (t ∩ disjointed w n) with ht'
    have tt' : t ⊆ t' :=
      calc
        t ⊆ ⋃ n, t ∩ disjointed w n :=
          by
          rw [← inter_Union, unionᵢ_disjointed, inter_Union]
          intro x hx
          rcases mem_Union.1 (hv hx) with ⟨n, hn⟩
          refine' mem_Union.2 ⟨n, _⟩
          have : x ∈ t ∩ v n := ⟨hx, hn⟩
          exact ⟨hx, subset_to_measurable μ _ this⟩
        _ ⊆ ⋃ n, to_measurable μ (t ∩ disjointed w n) :=
          Union_mono fun n => subset_to_measurable _ _
        
    refine' ⟨t', tt', MeasurableSet.unionᵢ fun n => measurable_set_to_measurable μ _, fun u hu => _⟩
    apply le_antisymm _ (measure_mono (inter_subset_inter tt' subset.rfl))
    calc
      μ (t' ∩ u) ≤ ∑' n, μ (to_measurable μ (t ∩ disjointed w n) ∩ u) :=
        by
        rw [ht', Union_inter]
        exact measure_Union_le _
      _ = ∑' n, μ (t ∩ disjointed w n ∩ u) := by
        congr 1
        ext1 n
        apply measure_to_measurable_inter hu
        apply ne_of_lt
        calc
          μ (t ∩ disjointed w n) ≤ μ (t ∩ w n) :=
            measure_mono (inter_subset_inter_right _ (disjointed_le w n))
          _ ≤ μ (w n) := (measure_mono (inter_subset_right _ _))
          _ < ∞ := hw n
          
      _ = ∑' n, μ.restrict (t ∩ u) (disjointed w n) :=
        by
        congr 1
        ext1 n
        rw [restrict_apply, inter_comm t _, inter_assoc]
        apply MeasurableSet.disjointed fun n => _
        exact measurable_set_to_measurable _ _
      _ = μ.restrict (t ∩ u) (⋃ n, disjointed w n) :=
        by
        rw [measure_Union]
        · exact disjoint_disjointed _
        · intro i
          apply MeasurableSet.disjointed fun n => _
          exact measurable_set_to_measurable _ _
      _ ≤ μ.restrict (t ∩ u) univ := (measure_mono (subset_univ _))
      _ = μ (t ∩ u) := by rw [restrict_apply MeasurableSet.univ, univ_inter]
      
  -- thanks to the definition of `to_measurable`, the previous property will also be shared
  -- by `to_measurable μ t`, which is enough to conclude the proof.
  rw [to_measurable]
  split_ifs with ht
  · apply measure_congr
    exact ae_eq_set_inter ht.some_spec.snd.2 (ae_eq_refl _)
  · exact A.some_spec.snd.2 s hs
#align measure_theory.measure.measure_to_measurable_inter_of_cover MeasureTheory.Measure.measure_toMeasurable_inter_of_cover

theorem restrict_toMeasurable_of_cover {s : Set α} {v : ℕ → Set α} (hv : s ⊆ ⋃ n, v n)
    (h'v : ∀ n, μ (s ∩ v n) ≠ ∞) : μ.restrict (toMeasurable μ s) = μ.restrict s :=
  ext fun t ht => by
    simp only [restrict_apply ht, inter_comm t, measure_to_measurable_inter_of_cover ht hv h'v]
#align measure_theory.measure.restrict_to_measurable_of_cover MeasureTheory.Measure.restrict_toMeasurable_of_cover

/-- The measurable superset `to_measurable μ t` of `t` (which has the same measure as `t`)
satisfies, for any measurable set `s`, the equality `μ (to_measurable μ t ∩ s) = μ (t ∩ s)`.
This only holds when `μ` is σ-finite. For a version without this assumption (but requiring
that `t` has finite measure), see `measure_to_measurable_inter`. -/
theorem measure_toMeasurable_inter_of_sigmaFinite [SigmaFinite μ] {s : Set α} (hs : MeasurableSet s)
    (t : Set α) : μ (toMeasurable μ t ∩ s) = μ (t ∩ s) :=
  by
  have : t ⊆ ⋃ n, spanning_sets μ n :=
    by
    rw [Union_spanning_sets]
    exact subset_univ _
  apply measure_to_measurable_inter_of_cover hs this fun n => ne_of_lt _
  calc
    μ (t ∩ spanning_sets μ n) ≤ μ (spanning_sets μ n) := measure_mono (inter_subset_right _ _)
    _ < ∞ := measure_spanning_sets_lt_top μ n
    
#align measure_theory.measure.measure_to_measurable_inter_of_sigma_finite MeasureTheory.Measure.measure_toMeasurable_inter_of_sigmaFinite

@[simp]
theorem restrict_toMeasurable_of_sigmaFinite [SigmaFinite μ] (s : Set α) :
    μ.restrict (toMeasurable μ s) = μ.restrict s :=
  ext fun t ht => by
    simp only [restrict_apply ht, inter_comm t, measure_to_measurable_inter_of_sigma_finite ht]
#align measure_theory.measure.restrict_to_measurable_of_sigma_finite MeasureTheory.Measure.restrict_toMeasurable_of_sigmaFinite

namespace FiniteSpanningSetsIn

variable {C D : Set (Set α)}

/-- If `μ` has finite spanning sets in `C` and `C ∩ {s | μ s < ∞} ⊆ D` then `μ` has finite spanning
sets in `D`. -/
protected def mono' (h : μ.FiniteSpanningSetsIn C) (hC : C ∩ { s | μ s < ∞ } ⊆ D) :
    μ.FiniteSpanningSetsIn D :=
  ⟨h.Set, fun i => hC ⟨h.set_mem i, h.Finite i⟩, h.Finite, h.spanning⟩
#align measure_theory.measure.finite_spanning_sets_in.mono' MeasureTheory.Measure.FiniteSpanningSetsIn.mono'

/-- If `μ` has finite spanning sets in `C` and `C ⊆ D` then `μ` has finite spanning sets in `D`. -/
protected def mono (h : μ.FiniteSpanningSetsIn C) (hC : C ⊆ D) : μ.FiniteSpanningSetsIn D :=
  h.mono' fun s hs => hC hs.1
#align measure_theory.measure.finite_spanning_sets_in.mono MeasureTheory.Measure.FiniteSpanningSetsIn.mono

/-- If `μ` has finite spanning sets in the collection of measurable sets `C`, then `μ` is σ-finite.
-/
protected theorem sigmaFinite (h : μ.FiniteSpanningSetsIn C) : SigmaFinite μ :=
  ⟨⟨h.mono <| subset_univ C⟩⟩
#align measure_theory.measure.finite_spanning_sets_in.sigma_finite MeasureTheory.Measure.FiniteSpanningSetsIn.sigmaFinite

/-- An extensionality for measures. It is `ext_of_generate_from_of_Union` formulated in terms of
`finite_spanning_sets_in`. -/
protected theorem ext {ν : Measure α} {C : Set (Set α)} (hA : ‹_› = generateFrom C)
    (hC : IsPiSystem C) (h : μ.FiniteSpanningSetsIn C) (h_eq : ∀ s ∈ C, μ s = ν s) : μ = ν :=
  ext_of_generateFrom_of_unionᵢ C _ hA hC h.spanning h.set_mem (fun i => (h.Finite i).Ne) h_eq
#align measure_theory.measure.finite_spanning_sets_in.ext MeasureTheory.Measure.FiniteSpanningSetsIn.ext

protected theorem isCountablySpanning (h : μ.FiniteSpanningSetsIn C) : IsCountablySpanning C :=
  ⟨h.Set, h.set_mem, h.spanning⟩
#align measure_theory.measure.finite_spanning_sets_in.is_countably_spanning MeasureTheory.Measure.FiniteSpanningSetsIn.isCountablySpanning

end FiniteSpanningSetsIn

theorem sigmaFiniteOfCountable {S : Set (Set α)} (hc : S.Countable) (hμ : ∀ s ∈ S, μ s < ∞)
    (hU : ⋃₀ S = univ) : SigmaFinite μ :=
  by
  obtain ⟨s, hμ, hs⟩ : ∃ s : ℕ → Set α, (∀ n, μ (s n) < ∞) ∧ (⋃ n, s n) = univ
  exact (@exists_seq_cover_iff_countable _ (fun x => μ x < ⊤) ⟨∅, by simp⟩).2 ⟨S, hc, hμ, hU⟩
  exact ⟨⟨⟨fun n => s n, fun n => trivial, hμ, hs⟩⟩⟩
#align measure_theory.measure.sigma_finite_of_countable MeasureTheory.Measure.sigmaFiniteOfCountable

/-- Given measures `μ`, `ν` where `ν ≤ μ`, `finite_spanning_sets_in.of_le` provides the induced
`finite_spanning_set` with respect to `ν` from a `finite_spanning_set` with respect to `μ`. -/
def FiniteSpanningSetsIn.ofLe (h : ν ≤ μ) {C : Set (Set α)} (S : μ.FiniteSpanningSetsIn C) :
    ν.FiniteSpanningSetsIn C where
  Set := S.Set
  set_mem := S.set_mem
  Finite n := lt_of_le_of_lt (le_iff'.1 h _) (S.Finite n)
  spanning := S.spanning
#align measure_theory.measure.finite_spanning_sets_in.of_le MeasureTheory.Measure.FiniteSpanningSetsIn.ofLe

theorem sigmaFiniteOfLe (μ : Measure α) [hs : SigmaFinite μ] (h : ν ≤ μ) : SigmaFinite ν :=
  ⟨hs.out.map <| FiniteSpanningSetsIn.ofLe h⟩
#align measure_theory.measure.sigma_finite_of_le MeasureTheory.Measure.sigmaFiniteOfLe

end Measure

/-- Every finite measure is σ-finite. -/
instance (priority := 100) IsFiniteMeasure.toSigmaFinite {m0 : MeasurableSpace α} (μ : Measure α)
    [IsFiniteMeasure μ] : SigmaFinite μ :=
  ⟨⟨⟨fun _ => univ, fun _ => trivial, fun _ => measure_lt_top μ _, unionᵢ_const _⟩⟩⟩
#align measure_theory.is_finite_measure.to_sigma_finite MeasureTheory.IsFiniteMeasure.toSigmaFinite

theorem sigmaFinite_bot_iff (μ : @Measure α ⊥) : SigmaFinite μ ↔ IsFiniteMeasure μ :=
  by
  refine'
    ⟨fun h => ⟨_⟩, fun h => by
      haveI := h
      infer_instance⟩
  haveI : sigma_finite μ := h
  let s := spanning_sets μ
  have hs_univ : (⋃ i, s i) = Set.univ := Union_spanning_sets μ
  have hs_meas : ∀ i, measurable_set[⊥] (s i) := measurable_spanning_sets μ
  simp_rw [MeasurableSpace.measurableSet_bot_iff] at hs_meas
  by_cases h_univ_empty : Set.univ = ∅
  · rw [h_univ_empty, measure_empty]
    exact ennreal.zero_ne_top.lt_top
  obtain ⟨i, hsi⟩ : ∃ i, s i = Set.univ :=
    by
    by_contra h_not_univ
    push_neg  at h_not_univ
    have h_empty : ∀ i, s i = ∅ := by simpa [h_not_univ] using hs_meas
    simp [h_empty] at hs_univ
    exact h_univ_empty hs_univ.symm
  rw [← hsi]
  exact measure_spanning_sets_lt_top μ i
#align measure_theory.sigma_finite_bot_iff MeasureTheory.sigmaFinite_bot_iff

include m0

instance Restrict.sigmaFinite (μ : Measure α) [SigmaFinite μ] (s : Set α) :
    SigmaFinite (μ.restrict s) :=
  by
  refine' ⟨⟨⟨spanning_sets μ, fun _ => trivial, fun i => _, Union_spanning_sets μ⟩⟩⟩
  rw [restrict_apply (measurable_spanning_sets μ i)]
  exact (measure_mono <| inter_subset_left _ _).trans_lt (measure_spanning_sets_lt_top μ i)
#align measure_theory.restrict.sigma_finite MeasureTheory.Restrict.sigmaFinite

instance Sum.sigmaFinite {ι} [Finite ι] (μ : ι → Measure α) [∀ i, SigmaFinite (μ i)] :
    SigmaFinite (Sum μ) := by
  cases nonempty_fintype ι
  have : ∀ n, MeasurableSet (⋂ i : ι, spanning_sets (μ i) n) := fun n =>
    MeasurableSet.interᵢ fun i => measurable_spanning_sets (μ i) n
  refine' ⟨⟨⟨fun n => ⋂ i, spanning_sets (μ i) n, fun _ => trivial, fun n => _, _⟩⟩⟩
  · rw [sum_apply _ (this n), tsum_fintype, ENNReal.sum_lt_top_iff]
    rintro i -
    exact (measure_mono <| Inter_subset _ i).trans_lt (measure_spanning_sets_lt_top (μ i) n)
  · rw [Union_Inter_of_monotone]
    simp_rw [Union_spanning_sets, Inter_univ]
    exact fun i => monotone_spanning_sets (μ i)
#align measure_theory.sum.sigma_finite MeasureTheory.Sum.sigmaFinite

instance Add.sigmaFinite (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] : SigmaFinite (μ + ν) :=
  by
  rw [← sum_cond]
  refine' @sum.sigma_finite _ _ _ _ _ (Bool.rec _ _) <;> simpa
#align measure_theory.add.sigma_finite MeasureTheory.Add.sigmaFinite

theorem SigmaFinite.ofMap (μ : Measure α) {f : α → β} (hf : AeMeasurable f μ)
    (h : SigmaFinite (μ.map f)) : SigmaFinite μ :=
  ⟨⟨⟨fun n => f ⁻¹' spanningSets (μ.map f) n, fun n => trivial, fun n => by
        simp only [← map_apply_of_ae_measurable hf, measurable_spanning_sets,
          measure_spanning_sets_lt_top],
        by rw [← preimage_Union, Union_spanning_sets, preimage_univ]⟩⟩⟩
#align measure_theory.sigma_finite.of_map MeasureTheory.SigmaFinite.ofMap

theorem MeasurableEquiv.sigmaFiniteMap {μ : Measure α} (f : α ≃ᵐ β) (h : SigmaFinite μ) :
    SigmaFinite (μ.map f) :=
  by
  refine' sigma_finite.of_map _ f.symm.measurable.ae_measurable _
  rwa [map_map f.symm.measurable f.measurable, f.symm_comp_self, measure.map_id]
#align measurable_equiv.sigma_finite_map MeasurableEquiv.sigmaFiniteMap

/-- Similar to `ae_of_forall_measure_lt_top_ae_restrict`, but where you additionally get the
  hypothesis that another σ-finite measure has finite values on `s`. -/
theorem ae_of_forall_measure_lt_top_ae_restrict' {μ : Measure α} (ν : Measure α) [SigmaFinite μ]
    [SigmaFinite ν] (P : α → Prop)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ν s < ∞ → ∀ᵐ x ∂μ.restrict s, P x) : ∀ᵐ x ∂μ, P x :=
  by
  have : ∀ n, ∀ᵐ x ∂μ, x ∈ spanning_sets (μ + ν) n → P x :=
    by
    intro n
    have := h (spanning_sets (μ + ν) n) (measurable_spanning_sets _ _) _ _
    exacts[(ae_restrict_iff' (measurable_spanning_sets _ _)).mp this,
      (self_le_add_right _ _).trans_lt (measure_spanning_sets_lt_top (μ + ν) _),
      (self_le_add_left _ _).trans_lt (measure_spanning_sets_lt_top (μ + ν) _)]
  filter_upwards [ae_all_iff.2 this]with _ hx using hx _ (mem_spanning_sets_index _ _)
#align measure_theory.ae_of_forall_measure_lt_top_ae_restrict' MeasureTheory.ae_of_forall_measure_lt_top_ae_restrict'

/-- To prove something for almost all `x` w.r.t. a σ-finite measure, it is sufficient to show that
  this holds almost everywhere in sets where the measure has finite value. -/
theorem ae_of_forall_measure_lt_top_ae_restrict {μ : Measure α} [SigmaFinite μ] (P : α → Prop)
    (h : ∀ s, MeasurableSet s → μ s < ∞ → ∀ᵐ x ∂μ.restrict s, P x) : ∀ᵐ x ∂μ, P x :=
  ae_of_forall_measure_lt_top_ae_restrict' μ P fun s hs h2s _ => h s hs h2s
#align measure_theory.ae_of_forall_measure_lt_top_ae_restrict MeasureTheory.ae_of_forall_measure_lt_top_ae_restrict

/-- A measure is called locally finite if it is finite in some neighborhood of each point. -/
class IsLocallyFiniteMeasure [TopologicalSpace α] (μ : Measure α) : Prop where
  finiteAtNhds : ∀ x, μ.FiniteAtFilter (𝓝 x)
#align measure_theory.is_locally_finite_measure MeasureTheory.IsLocallyFiniteMeasure

-- see Note [lower instance priority]
instance (priority := 100) IsFiniteMeasure.toIsLocallyFiniteMeasure [TopologicalSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] : IsLocallyFiniteMeasure μ :=
  ⟨fun x => finiteAtFilterOfFinite _ _⟩
#align measure_theory.is_finite_measure.to_is_locally_finite_measure MeasureTheory.IsFiniteMeasure.toIsLocallyFiniteMeasure

theorem Measure.finiteAtNhds [TopologicalSpace α] (μ : Measure α) [IsLocallyFiniteMeasure μ]
    (x : α) : μ.FiniteAtFilter (𝓝 x) :=
  IsLocallyFiniteMeasure.finiteAtNhds x
#align measure_theory.measure.finite_at_nhds MeasureTheory.Measure.finiteAtNhds

theorem Measure.smulFinite (μ : Measure α) [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ∞) :
    IsFiniteMeasure (c • μ) := by
  lift c to ℝ≥0 using hc
  exact MeasureTheory.isFiniteMeasureSmulNnreal
#align measure_theory.measure.smul_finite MeasureTheory.Measure.smulFinite

theorem Measure.exists_isOpen_measure_lt_top [TopologicalSpace α] (μ : Measure α)
    [IsLocallyFiniteMeasure μ] (x : α) : ∃ s : Set α, x ∈ s ∧ IsOpen s ∧ μ s < ∞ := by
  simpa only [exists_prop, and_assoc] using
    (μ.finite_at_nhds x).exists_mem_basis (nhds_basis_opens x)
#align measure_theory.measure.exists_is_open_measure_lt_top MeasureTheory.Measure.exists_isOpen_measure_lt_top

instance isLocallyFiniteMeasureSmulNnreal [TopologicalSpace α] (μ : Measure α)
    [IsLocallyFiniteMeasure μ] (c : ℝ≥0) : IsLocallyFiniteMeasure (c • μ) :=
  by
  refine' ⟨fun x => _⟩
  rcases μ.exists_is_open_measure_lt_top x with ⟨o, xo, o_open, μo⟩
  refine' ⟨o, o_open.mem_nhds xo, _⟩
  apply ENNReal.mul_lt_top _ μo.ne
  simp only [RingHom.toMonoidHom_eq_coe, [anonymous], ENNReal.coe_ne_top, ENNReal.coe_ofNNRealHom,
    Ne.def, not_false_iff]
#align measure_theory.is_locally_finite_measure_smul_nnreal MeasureTheory.isLocallyFiniteMeasureSmulNnreal

protected theorem Measure.isTopologicalBasis_isOpen_lt_top [TopologicalSpace α] (μ : Measure α)
    [IsLocallyFiniteMeasure μ] : TopologicalSpace.IsTopologicalBasis { s | IsOpen s ∧ μ s < ∞ } :=
  by
  refine' TopologicalSpace.isTopologicalBasis_of_open_of_nhds (fun s hs => hs.1) _
  intro x s xs hs
  rcases μ.exists_is_open_measure_lt_top x with ⟨v, xv, hv, μv⟩
  refine' ⟨v ∩ s, ⟨hv.inter hs, lt_of_le_of_lt _ μv⟩, ⟨xv, xs⟩, inter_subset_right _ _⟩
  exact measure_mono (inter_subset_left _ _)
#align measure_theory.measure.is_topological_basis_is_open_lt_top MeasureTheory.Measure.isTopologicalBasis_isOpen_lt_top

/-- A measure `μ` is finite on compacts if any compact set `K` satisfies `μ K < ∞`. -/
@[protect_proj]
class IsFiniteMeasureOnCompacts [TopologicalSpace α] (μ : Measure α) : Prop where
  lt_top_of_isCompact : ∀ ⦃K : Set α⦄, IsCompact K → μ K < ∞
#align measure_theory.is_finite_measure_on_compacts MeasureTheory.IsFiniteMeasureOnCompacts

/-- A compact subset has finite measure for a measure which is finite on compacts. -/
theorem IsCompact.measure_lt_top [TopologicalSpace α] {μ : Measure α} [IsFiniteMeasureOnCompacts μ]
    ⦃K : Set α⦄ (hK : IsCompact K) : μ K < ∞ :=
  IsFiniteMeasureOnCompacts.lt_top_of_isCompact hK
#align is_compact.measure_lt_top IsCompact.measure_lt_top

/-- A bounded subset has finite measure for a measure which is finite on compact sets, in a
proper space. -/
theorem Metric.Bounded.measure_lt_top [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] ⦃s : Set α⦄ (hs : Metric.Bounded s) : μ s < ∞ :=
  calc
    μ s ≤ μ (closure s) := measure_mono subset_closure
    _ < ∞ := (Metric.isCompact_of_isClosed_bounded isClosed_closure hs.closure).measure_lt_top
    
#align metric.bounded.measure_lt_top Metric.Bounded.measure_lt_top

theorem measure_closedBall_lt_top [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] {x : α} {r : ℝ} : μ (Metric.closedBall x r) < ∞ :=
  Metric.bounded_closedBall.measure_lt_top
#align measure_theory.measure_closed_ball_lt_top MeasureTheory.measure_closedBall_lt_top

theorem measure_ball_lt_top [PseudoMetricSpace α] [ProperSpace α] {μ : Measure α}
    [IsFiniteMeasureOnCompacts μ] {x : α} {r : ℝ} : μ (Metric.ball x r) < ∞ :=
  Metric.bounded_ball.measure_lt_top
#align measure_theory.measure_ball_lt_top MeasureTheory.measure_ball_lt_top

protected theorem IsFiniteMeasureOnCompacts.smul [TopologicalSpace α] (μ : Measure α)
    [IsFiniteMeasureOnCompacts μ] {c : ℝ≥0∞} (hc : c ≠ ∞) : IsFiniteMeasureOnCompacts (c • μ) :=
  ⟨fun K hK => ENNReal.mul_lt_top hc hK.measure_lt_top.Ne⟩
#align measure_theory.is_finite_measure_on_compacts.smul MeasureTheory.IsFiniteMeasureOnCompacts.smul

/-- Note this cannot be an instance because it would form a typeclass loop with
`is_finite_measure_on_compacts_of_is_locally_finite_measure`. -/
theorem CompactSpace.isFiniteMeasure [TopologicalSpace α] [CompactSpace α]
    [IsFiniteMeasureOnCompacts μ] : IsFiniteMeasure μ :=
  ⟨IsFiniteMeasureOnCompacts.lt_top_of_isCompact isCompact_univ⟩
#align measure_theory.compact_space.is_finite_measure MeasureTheory.CompactSpace.isFiniteMeasure

omit m0

-- see Note [lower instance priority]
instance (priority := 100) sigmaFiniteOfLocallyFinite [TopologicalSpace α]
    [SecondCountableTopology α] [IsLocallyFiniteMeasure μ] : SigmaFinite μ :=
  by
  choose s hsx hsμ using μ.finite_at_nhds
  rcases TopologicalSpace.countable_cover_nhds hsx with ⟨t, htc, htU⟩
  refine' measure.sigma_finite_of_countable (htc.image s) (ball_image_iff.2 fun x hx => hsμ x) _
  rwa [sUnion_image]
#align measure_theory.sigma_finite_of_locally_finite MeasureTheory.sigmaFiniteOfLocallyFinite

/-- A measure which is finite on compact sets in a locally compact space is locally finite.
Not registered as an instance to avoid a loop with the other direction. -/
theorem isLocallyFiniteMeasureOfIsFiniteMeasureOnCompacts [TopologicalSpace α]
    [LocallyCompactSpace α] [IsFiniteMeasureOnCompacts μ] : IsLocallyFiniteMeasure μ :=
  ⟨by
    intro x
    rcases exists_compact_mem_nhds x with ⟨K, K_compact, K_mem⟩
    exact ⟨K, K_mem, K_compact.measure_lt_top⟩⟩
#align measure_theory.is_locally_finite_measure_of_is_finite_measure_on_compacts MeasureTheory.isLocallyFiniteMeasureOfIsFiniteMeasureOnCompacts

theorem exists_pos_measure_of_cover [Countable ι] {U : ι → Set α} (hU : (⋃ i, U i) = univ)
    (hμ : μ ≠ 0) : ∃ i, 0 < μ (U i) := by
  contrapose! hμ with H
  rw [← measure_univ_eq_zero, ← hU]
  exact measure_Union_null fun i => nonpos_iff_eq_zero.1 (H i)
#align measure_theory.exists_pos_measure_of_cover MeasureTheory.exists_pos_measure_of_cover

theorem exists_pos_preimage_ball [PseudoMetricSpace δ] (f : α → δ) (x : δ) (hμ : μ ≠ 0) :
    ∃ n : ℕ, 0 < μ (f ⁻¹' Metric.ball x n) :=
  exists_pos_measure_of_cover (by rw [← preimage_Union, Metric.unionᵢ_ball_nat, preimage_univ]) hμ
#align measure_theory.exists_pos_preimage_ball MeasureTheory.exists_pos_preimage_ball

theorem exists_pos_ball [PseudoMetricSpace α] (x : α) (hμ : μ ≠ 0) :
    ∃ n : ℕ, 0 < μ (Metric.ball x n) :=
  exists_pos_preimage_ball id x hμ
#align measure_theory.exists_pos_ball MeasureTheory.exists_pos_ball

/-- If a set has zero measure in a neighborhood of each of its points, then it has zero measure
in a second-countable space. -/
theorem null_of_locally_null [TopologicalSpace α] [SecondCountableTopology α] (s : Set α)
    (hs : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, μ u = 0) : μ s = 0 :=
  μ.toOuterMeasure.null_of_locally_null s hs
#align measure_theory.null_of_locally_null MeasureTheory.null_of_locally_null

theorem exists_mem_forall_mem_nhdsWithin_pos_measure [TopologicalSpace α]
    [SecondCountableTopology α] {s : Set α} (hs : μ s ≠ 0) : ∃ x ∈ s, ∀ t ∈ 𝓝[s] x, 0 < μ t :=
  μ.toOuterMeasure.exists_mem_forall_mem_nhds_within_pos hs
#align measure_theory.exists_mem_forall_mem_nhds_within_pos_measure MeasureTheory.exists_mem_forall_mem_nhdsWithin_pos_measure

theorem exists_ne_forall_mem_nhds_pos_measure_preimage {β} [TopologicalSpace β] [T1Space β]
    [SecondCountableTopology β] [Nonempty β] {f : α → β} (h : ∀ b, ∃ᵐ x ∂μ, f x ≠ b) :
    ∃ a b : β, a ≠ b ∧ (∀ s ∈ 𝓝 a, 0 < μ (f ⁻¹' s)) ∧ ∀ t ∈ 𝓝 b, 0 < μ (f ⁻¹' t) :=
  by
  -- We use an `outer_measure` so that the proof works without `measurable f`
  set m : outer_measure β := outer_measure.map f μ.to_outer_measure
  replace h : ∀ b : β, m ({b}ᶜ) ≠ 0 := fun b => not_eventually.mpr (h b)
  inhabit β
  have : m univ ≠ 0 := ne_bot_of_le_ne_bot (h default) (m.mono' <| subset_univ _)
  rcases m.exists_mem_forall_mem_nhds_within_pos this with ⟨b, -, hb⟩
  simp only [nhdsWithin_univ] at hb
  rcases m.exists_mem_forall_mem_nhds_within_pos (h b) with ⟨a, hab : a ≠ b, ha⟩
  simp only [is_open_compl_singleton.nhds_within_eq hab] at ha
  exact ⟨a, b, hab, ha, hb⟩
#align measure_theory.exists_ne_forall_mem_nhds_pos_measure_preimage MeasureTheory.exists_ne_forall_mem_nhds_pos_measure_preimage

/-- If two finite measures give the same mass to the whole space and coincide on a π-system made
of measurable sets, then they coincide on all sets in the σ-algebra generated by the π-system. -/
theorem ext_on_measurableSpace_of_generate_finite {α} (m₀ : MeasurableSpace α) {μ ν : Measure α}
    [IsFiniteMeasure μ] (C : Set (Set α)) (hμν : ∀ s ∈ C, μ s = ν s) {m : MeasurableSpace α}
    (h : m ≤ m₀) (hA : m = MeasurableSpace.generateFrom C) (hC : IsPiSystem C)
    (h_univ : μ Set.univ = ν Set.univ) {s : Set α} (hs : measurable_set[m] s) : μ s = ν s :=
  by
  haveI : is_finite_measure ν := by
    constructor
    rw [← h_univ]
    apply is_finite_measure.measure_univ_lt_top
  refine' induction_on_inter hA hC (by simp) hμν _ _ hs
  · intro t h1t h2t
    have h1t_ : @MeasurableSet α m₀ t := h _ h1t
    rw [@measure_compl α m₀ μ t h1t_ (@measure_ne_top α m₀ μ _ t),
      @measure_compl α m₀ ν t h1t_ (@measure_ne_top α m₀ ν _ t), h_univ, h2t]
  · intro f h1f h2f h3f
    have h2f_ : ∀ i : ℕ, @MeasurableSet α m₀ (f i) := fun i => h _ (h2f i)
    have h_Union : @MeasurableSet α m₀ (⋃ i : ℕ, f i) := @MeasurableSet.unionᵢ α ℕ m₀ _ f h2f_
    simp [measure_Union, h_Union, h1f, h3f, h2f_]
#align measure_theory.ext_on_measurable_space_of_generate_finite MeasureTheory.ext_on_measurableSpace_of_generate_finite

/-- Two finite measures are equal if they are equal on the π-system generating the σ-algebra
  (and `univ`). -/
theorem ext_of_generate_finite (C : Set (Set α)) (hA : m0 = generateFrom C) (hC : IsPiSystem C)
    [IsFiniteMeasure μ] (hμν : ∀ s ∈ C, μ s = ν s) (h_univ : μ univ = ν univ) : μ = ν :=
  Measure.ext fun s hs => ext_on_measurableSpace_of_generate_finite m0 C hμν le_rfl hA hC h_univ hs
#align measure_theory.ext_of_generate_finite MeasureTheory.ext_of_generate_finite

namespace Measure

section disjointed

include m0

/-- Given `S : μ.finite_spanning_sets_in {s | measurable_set s}`,
`finite_spanning_sets_in.disjointed` provides a `finite_spanning_sets_in {s | measurable_set s}`
such that its underlying sets are pairwise disjoint. -/
protected def FiniteSpanningSetsIn.disjointed {μ : Measure α}
    (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s }) :
    μ.FiniteSpanningSetsIn { s | MeasurableSet s } :=
  ⟨disjointed S.Set, MeasurableSet.disjointed S.set_mem, fun n =>
    lt_of_le_of_lt (measure_mono (disjointed_subset S.Set n)) (S.Finite _),
    S.spanning ▸ unionᵢ_disjointed⟩
#align measure_theory.measure.finite_spanning_sets_in.disjointed MeasureTheory.Measure.FiniteSpanningSetsIn.disjointed

theorem FiniteSpanningSetsIn.disjointed_set_eq {μ : Measure α}
    (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s }) : S.disjointed.Set = disjointed S.Set :=
  rfl
#align measure_theory.measure.finite_spanning_sets_in.disjointed_set_eq MeasureTheory.Measure.FiniteSpanningSetsIn.disjointed_set_eq

theorem exists_eq_disjoint_finiteSpanningSetsIn (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] :
    ∃ (S : μ.FiniteSpanningSetsIn { s | MeasurableSet s })(T :
      ν.FiniteSpanningSetsIn { s | MeasurableSet s }),
      S.Set = T.Set ∧ Pairwise (Disjoint on S.Set) :=
  let S := (μ + ν).toFiniteSpanningSetsIn.disjointed
  ⟨S.of_le (Measure.le_add_right le_rfl), S.of_le (Measure.le_add_left le_rfl), rfl,
    disjoint_disjointed _⟩
#align measure_theory.measure.exists_eq_disjoint_finite_spanning_sets_in MeasureTheory.Measure.exists_eq_disjoint_finiteSpanningSetsIn

end disjointed

namespace FiniteAtFilter

variable {f g : Filter α}

theorem filterMono (h : f ≤ g) : μ.FiniteAtFilter g → μ.FiniteAtFilter f := fun ⟨s, hs, hμ⟩ =>
  ⟨s, h hs, hμ⟩
#align measure_theory.measure.finite_at_filter.filter_mono MeasureTheory.Measure.FiniteAtFilter.filterMono

theorem infOfLeft (h : μ.FiniteAtFilter f) : μ.FiniteAtFilter (f ⊓ g) :=
  h.filter_mono inf_le_left
#align measure_theory.measure.finite_at_filter.inf_of_left MeasureTheory.Measure.FiniteAtFilter.infOfLeft

theorem infOfRight (h : μ.FiniteAtFilter g) : μ.FiniteAtFilter (f ⊓ g) :=
  h.filter_mono inf_le_right
#align measure_theory.measure.finite_at_filter.inf_of_right MeasureTheory.Measure.FiniteAtFilter.infOfRight

@[simp]
theorem inf_ae_iff : μ.FiniteAtFilter (f ⊓ μ.ae) ↔ μ.FiniteAtFilter f :=
  by
  refine' ⟨_, fun h => h.filter_mono inf_le_left⟩
  rintro ⟨s, ⟨t, ht, u, hu, rfl⟩, hμ⟩
  suffices : μ t ≤ μ (t ∩ u); exact ⟨t, ht, this.trans_lt hμ⟩
  exact measure_mono_ae (mem_of_superset hu fun x hu ht => ⟨ht, hu⟩)
#align measure_theory.measure.finite_at_filter.inf_ae_iff MeasureTheory.Measure.FiniteAtFilter.inf_ae_iff

alias inf_ae_iff ↔ of_inf_ae _
#align measure_theory.measure.finite_at_filter.of_inf_ae MeasureTheory.Measure.FiniteAtFilter.ofInfAe

theorem filterMonoAe (h : f ⊓ μ.ae ≤ g) (hg : μ.FiniteAtFilter g) : μ.FiniteAtFilter f :=
  inf_ae_iff.1 (hg.filter_mono h)
#align measure_theory.measure.finite_at_filter.filter_mono_ae MeasureTheory.Measure.FiniteAtFilter.filterMonoAe

protected theorem measureMono (h : μ ≤ ν) : ν.FiniteAtFilter f → μ.FiniteAtFilter f :=
  fun ⟨s, hs, hν⟩ => ⟨s, hs, (Measure.le_iff'.1 h s).trans_lt hν⟩
#align measure_theory.measure.finite_at_filter.measure_mono MeasureTheory.Measure.FiniteAtFilter.measureMono

@[mono]
protected theorem mono (hf : f ≤ g) (hμ : μ ≤ ν) : ν.FiniteAtFilter g → μ.FiniteAtFilter f :=
  fun h => (h.filter_mono hf).measure_mono hμ
#align measure_theory.measure.finite_at_filter.mono MeasureTheory.Measure.FiniteAtFilter.mono

protected theorem eventually (h : μ.FiniteAtFilter f) : ∀ᶠ s in f.smallSets, μ s < ∞ :=
  (eventually_small_sets' fun s t hst ht => (measure_mono hst).trans_lt ht).2 h
#align measure_theory.measure.finite_at_filter.eventually MeasureTheory.Measure.FiniteAtFilter.eventually

theorem filterSup : μ.FiniteAtFilter f → μ.FiniteAtFilter g → μ.FiniteAtFilter (f ⊔ g) :=
  fun ⟨s, hsf, hsμ⟩ ⟨t, htg, htμ⟩ =>
  ⟨s ∪ t, union_mem_sup hsf htg, (measure_union_le s t).trans_lt (ENNReal.add_lt_top.2 ⟨hsμ, htμ⟩)⟩
#align measure_theory.measure.finite_at_filter.filter_sup MeasureTheory.Measure.FiniteAtFilter.filterSup

end FiniteAtFilter

theorem finiteAtNhdsWithin [TopologicalSpace α] {m0 : MeasurableSpace α} (μ : Measure α)
    [IsLocallyFiniteMeasure μ] (x : α) (s : Set α) : μ.FiniteAtFilter (𝓝[s] x) :=
  (finiteAtNhds μ x).inf_of_left
#align measure_theory.measure.finite_at_nhds_within MeasureTheory.Measure.finiteAtNhdsWithin

@[simp]
theorem finite_at_principal : μ.FiniteAtFilter (𝓟 s) ↔ μ s < ∞ :=
  ⟨fun ⟨t, ht, hμ⟩ => (measure_mono ht).trans_lt hμ, fun h => ⟨s, mem_principal_self s, h⟩⟩
#align measure_theory.measure.finite_at_principal MeasureTheory.Measure.finite_at_principal

theorem isLocallyFiniteMeasureOfLe [TopologicalSpace α] {m : MeasurableSpace α} {μ ν : Measure α}
    [H : IsLocallyFiniteMeasure μ] (h : ν ≤ μ) : IsLocallyFiniteMeasure ν :=
  let F := H.finiteAtNhds
  ⟨fun x => (F x).measure_mono h⟩
#align measure_theory.measure.is_locally_finite_measure_of_le MeasureTheory.Measure.isLocallyFiniteMeasureOfLe

end Measure

end MeasureTheory

open MeasureTheory MeasureTheory.Measure

namespace MeasurableEmbedding

variable {m0 : MeasurableSpace α} {m1 : MeasurableSpace β} {f : α → β} (hf : MeasurableEmbedding f)

include hf

theorem map_apply (μ : Measure α) (s : Set β) : μ.map f s = μ (f ⁻¹' s) :=
  by
  refine' le_antisymm _ (le_map_apply hf.measurable.ae_measurable s)
  set t := f '' to_measurable μ (f ⁻¹' s) ∪ range fᶜ
  have htm : MeasurableSet t :=
    (hf.measurable_set_image.2 <| measurable_set_to_measurable _ _).union
      hf.measurable_set_range.compl
  have hst : s ⊆ t :=
    by
    rw [subset_union_compl_iff_inter_subset, ← image_preimage_eq_inter_range]
    exact image_subset _ (subset_to_measurable _ _)
  have hft : f ⁻¹' t = to_measurable μ (f ⁻¹' s) := by
    rw [preimage_union, preimage_compl, preimage_range, compl_univ, union_empty,
      hf.injective.preimage_image]
  calc
    μ.map f s ≤ μ.map f t := measure_mono hst
    _ = μ (f ⁻¹' s) := by rw [map_apply hf.measurable htm, hft, measure_to_measurable]
    
#align measurable_embedding.map_apply MeasurableEmbedding.map_apply

theorem map_comap (μ : Measure β) : (comap f μ).map f = μ.restrict (range f) :=
  by
  ext1 t ht
  rw [hf.map_apply, comap_apply f hf.injective hf.measurable_set_image' _ (hf.measurable ht),
    image_preimage_eq_inter_range, restrict_apply ht]
#align measurable_embedding.map_comap MeasurableEmbedding.map_comap

theorem comap_apply (μ : Measure β) (s : Set α) : comap f μ s = μ (f '' s) :=
  calc
    comap f μ s = comap f μ (f ⁻¹' (f '' s)) := by rw [hf.injective.preimage_image]
    _ = (comap f μ).map f (f '' s) := (hf.map_apply _ _).symm
    _ = μ (f '' s) := by
      rw [hf.map_comap, restrict_apply' hf.measurable_set_range,
        inter_eq_self_of_subset_left (image_subset_range _ _)]
    
#align measurable_embedding.comap_apply MeasurableEmbedding.comap_apply

theorem ae_map_iff {p : β → Prop} {μ : Measure α} : (∀ᵐ x ∂μ.map f, p x) ↔ ∀ᵐ x ∂μ, p (f x) := by
  simp only [ae_iff, hf.map_apply, preimage_set_of_eq]
#align measurable_embedding.ae_map_iff MeasurableEmbedding.ae_map_iff

theorem restrict_map (μ : Measure α) (s : Set β) :
    (μ.map f).restrict s = (μ.restrict <| f ⁻¹' s).map f :=
  Measure.ext fun t ht => by simp [hf.map_apply, ht, hf.measurable ht]
#align measurable_embedding.restrict_map MeasurableEmbedding.restrict_map

protected theorem comap_preimage (μ : Measure β) {s : Set β} (hs : MeasurableSet s) :
    μ.comap f (f ⁻¹' s) = μ (s ∩ range f) :=
  comap_preimage _ _ hf.Injective hf.Measurable
    (fun t ht => (hf.measurableSet_image' ht).NullMeasurableSet) hs
#align measurable_embedding.comap_preimage MeasurableEmbedding.comap_preimage

end MeasurableEmbedding

section Subtype

theorem comap_subtype_coe_apply {m0 : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s)
    (μ : Measure α) (t : Set s) : comap coe μ t = μ (coe '' t) :=
  (MeasurableEmbedding.subtype_coe hs).comap_apply _ _
#align comap_subtype_coe_apply comap_subtype_coe_apply

theorem map_comap_subtype_coe {m0 : MeasurableSpace α} {s : Set α} (hs : MeasurableSet s)
    (μ : Measure α) : (comap coe μ).map (coe : s → α) = μ.restrict s := by
  rw [(MeasurableEmbedding.subtype_coe hs).map_comap, Subtype.range_coe]
#align map_comap_subtype_coe map_comap_subtype_coe

theorem ae_restrict_iff_subtype {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {p : α → Prop} :
    (∀ᵐ x ∂μ.restrict s, p x) ↔ ∀ᵐ x ∂comap (coe : s → α) μ, p ↑x := by
  rw [← map_comap_subtype_coe hs, (MeasurableEmbedding.subtype_coe hs).ae_map_iff]
#align ae_restrict_iff_subtype ae_restrict_iff_subtype

variable [MeasureSpace α] {s t : Set α}

/-!
### Volume on `s : set α`
-/


instance SetCoe.measureSpace (s : Set α) : MeasureSpace s :=
  ⟨comap (coe : s → α) volume⟩
#align set_coe.measure_space SetCoe.measureSpace

theorem volume_set_coe_def (s : Set α) : (volume : Measure s) = comap (coe : s → α) volume :=
  rfl
#align volume_set_coe_def volume_set_coe_def

theorem MeasurableSet.map_coe_volume {s : Set α} (hs : MeasurableSet s) :
    volume.map (coe : s → α) = restrict volume s := by
  rw [volume_set_coe_def, (MeasurableEmbedding.subtype_coe hs).map_comap volume, Subtype.range_coe]
#align measurable_set.map_coe_volume MeasurableSet.map_coe_volume

theorem volume_image_subtype_coe {s : Set α} (hs : MeasurableSet s) (t : Set s) :
    volume (coe '' t : Set α) = volume t :=
  (comap_subtype_coe_apply hs volume t).symm
#align volume_image_subtype_coe volume_image_subtype_coe

@[simp]
theorem volume_preimage_coe (hs : NullMeasurableSet s) (ht : MeasurableSet t) :
    volume ((coe : s → α) ⁻¹' t) = volume (t ∩ s) := by
  rw [volume_set_coe_def,
    comap_apply₀ _ _ Subtype.coe_injective
      (fun h => measurable_set.null_measurable_set_subtype_coe hs)
      (measurable_subtype_coe ht).NullMeasurableSet,
    image_preimage_eq_inter_range, Subtype.range_coe]
#align volume_preimage_coe volume_preimage_coe

end Subtype

namespace MeasurableEquiv

/-! Interactions of measurable equivalences and measures -/


open Equiv MeasureTheory.Measure

variable [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

/-- If we map a measure along a measurable equivalence, we can compute the measure on all sets
  (not just the measurable ones). -/
protected theorem map_apply (f : α ≃ᵐ β) (s : Set β) : μ.map f s = μ (f ⁻¹' s) :=
  f.MeasurableEmbedding.map_apply _ _
#align measurable_equiv.map_apply MeasurableEquiv.map_apply

@[simp]
theorem map_symm_map (e : α ≃ᵐ β) : (μ.map e).map e.symm = μ := by
  simp [map_map e.symm.measurable e.measurable]
#align measurable_equiv.map_symm_map MeasurableEquiv.map_symm_map

@[simp]
theorem map_map_symm (e : α ≃ᵐ β) : (ν.map e.symm).map e = ν := by
  simp [map_map e.measurable e.symm.measurable]
#align measurable_equiv.map_map_symm MeasurableEquiv.map_map_symm

theorem map_measurableEquiv_injective (e : α ≃ᵐ β) : Injective (map e) :=
  by
  intro μ₁ μ₂ hμ
  apply_fun map e.symm  at hμ
  simpa [map_symm_map e] using hμ
#align measurable_equiv.map_measurable_equiv_injective MeasurableEquiv.map_measurableEquiv_injective

theorem map_apply_eq_iff_map_symm_apply_eq (e : α ≃ᵐ β) : μ.map e = ν ↔ ν.map e.symm = μ := by
  rw [← (map_measurable_equiv_injective e).eq_iff, map_map_symm, eq_comm]
#align measurable_equiv.map_apply_eq_iff_map_symm_apply_eq MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq

theorem restrict_map (e : α ≃ᵐ β) (s : Set β) :
    (μ.map e).restrict s = (μ.restrict <| e ⁻¹' s).map e :=
  e.MeasurableEmbedding.restrict_map _ _
#align measurable_equiv.restrict_map MeasurableEquiv.restrict_map

theorem map_ae (f : α ≃ᵐ β) (μ : Measure α) : Filter.map f μ.ae = (map f μ).ae :=
  by
  ext s
  simp_rw [mem_map, mem_ae_iff, ← preimage_compl, f.map_apply]
#align measurable_equiv.map_ae MeasurableEquiv.map_ae

theorem quasiMeasurePreservingSymm (μ : Measure α) (e : α ≃ᵐ β) :
    QuasiMeasurePreserving e.symm (map e μ) μ :=
  ⟨e.symm.Measurable, by rw [measure.map_map, e.symm_comp_self, measure.map_id] <;> measurability⟩
#align measurable_equiv.quasi_measure_preserving_symm MeasurableEquiv.quasiMeasurePreservingSymm

end MeasurableEquiv

namespace MeasureTheory

theorem OuterMeasure.toMeasure_zero [MeasurableSpace α] :
    (0 : OuterMeasure α).toMeasure (le_top.trans OuterMeasure.zero_caratheodory.symm.le) = 0 := by
  rw [← measure.measure_univ_eq_zero, to_measure_apply _ _ MeasurableSet.univ,
    outer_measure.coe_zero, Pi.zero_apply]
#align measure_theory.outer_measure.to_measure_zero MeasureTheory.OuterMeasure.toMeasure_zero

section Trim

/-- Restriction of a measure to a sub-sigma algebra.
It is common to see a measure `μ` on a measurable space structure `m0` as being also a measure on
any `m ≤ m0`. Since measures in mathlib have to be trimmed to the measurable space, `μ` itself
cannot be a measure on `m`, hence the definition of `μ.trim hm`.

This notion is related to `outer_measure.trim`, see the lemma
`to_outer_measure_trim_eq_trim_to_outer_measure`. -/
def Measure.trim {m m0 : MeasurableSpace α} (μ : @Measure α m0) (hm : m ≤ m0) : @Measure α m :=
  @OuterMeasure.toMeasure α m μ.toOuterMeasure (hm.trans (le_toOuterMeasure_caratheodory μ))
#align measure_theory.measure.trim MeasureTheory.Measure.trim

@[simp]
theorem trim_eq_self [MeasurableSpace α] {μ : Measure α} : μ.trim le_rfl = μ := by
  simp [measure.trim]
#align measure_theory.trim_eq_self MeasureTheory.trim_eq_self

variable {m m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

theorem toOuterMeasure_trim_eq_trim_toOuterMeasure (μ : Measure α) (hm : m ≤ m0) :
    @Measure.toOuterMeasure _ m (μ.trim hm) = @OuterMeasure.trim _ m μ.toOuterMeasure := by
  rw [measure.trim, to_measure_to_outer_measure]
#align measure_theory.to_outer_measure_trim_eq_trim_to_outer_measure MeasureTheory.toOuterMeasure_trim_eq_trim_toOuterMeasure

@[simp]
theorem zero_trim (hm : m ≤ m0) : (0 : Measure α).trim hm = (0 : @Measure α m) := by
  simp [measure.trim, outer_measure.to_measure_zero]
#align measure_theory.zero_trim MeasureTheory.zero_trim

theorem trim_measurableSet_eq (hm : m ≤ m0) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s := by
  simp [measure.trim, hs]
#align measure_theory.trim_measurable_set_eq MeasureTheory.trim_measurableSet_eq

theorem le_trim (hm : m ≤ m0) : μ s ≤ μ.trim hm s :=
  by
  simp_rw [measure.trim]
  exact @le_to_measure_apply _ m _ _ _
#align measure_theory.le_trim MeasureTheory.le_trim

theorem measure_eq_zero_of_trim_eq_zero (hm : m ≤ m0) (h : μ.trim hm s = 0) : μ s = 0 :=
  le_antisymm ((le_trim hm).trans (le_of_eq h)) (zero_le _)
#align measure_theory.measure_eq_zero_of_trim_eq_zero MeasureTheory.measure_eq_zero_of_trim_eq_zero

theorem measure_trim_toMeasurable_eq_zero {hm : m ≤ m0} (hs : μ.trim hm s = 0) :
    μ (@toMeasurable α m (μ.trim hm) s) = 0 :=
  measure_eq_zero_of_trim_eq_zero hm (by rwa [measure_to_measurable])
#align measure_theory.measure_trim_to_measurable_eq_zero MeasureTheory.measure_trim_toMeasurable_eq_zero

theorem ae_of_ae_trim (hm : m ≤ m0) {μ : Measure α} {P : α → Prop} (h : ∀ᵐ x ∂μ.trim hm, P x) :
    ∀ᵐ x ∂μ, P x :=
  measure_eq_zero_of_trim_eq_zero hm h
#align measure_theory.ae_of_ae_trim MeasureTheory.ae_of_ae_trim

theorem ae_eq_of_ae_eq_trim {E} {hm : m ≤ m0} {f₁ f₂ : α → E}
    (h12 : f₁ =ᶠ[@Measure.ae α m (μ.trim hm)] f₂) : f₁ =ᵐ[μ] f₂ :=
  measure_eq_zero_of_trim_eq_zero hm h12
#align measure_theory.ae_eq_of_ae_eq_trim MeasureTheory.ae_eq_of_ae_eq_trim

theorem ae_le_of_ae_le_trim {E} [LE E] {hm : m ≤ m0} {f₁ f₂ : α → E}
    (h12 : f₁ ≤ᶠ[@Measure.ae α m (μ.trim hm)] f₂) : f₁ ≤ᵐ[μ] f₂ :=
  measure_eq_zero_of_trim_eq_zero hm h12
#align measure_theory.ae_le_of_ae_le_trim MeasureTheory.ae_le_of_ae_le_trim

theorem trim_trim {m₁ m₂ : MeasurableSpace α} {hm₁₂ : m₁ ≤ m₂} {hm₂ : m₂ ≤ m0} :
    (μ.trim hm₂).trim hm₁₂ = μ.trim (hm₁₂.trans hm₂) :=
  by
  ext1 t ht
  rw [trim_measurable_set_eq hm₁₂ ht, trim_measurable_set_eq (hm₁₂.trans hm₂) ht,
    trim_measurable_set_eq hm₂ (hm₁₂ t ht)]
#align measure_theory.trim_trim MeasureTheory.trim_trim

theorem restrict_trim (hm : m ≤ m0) (μ : Measure α) (hs : @MeasurableSet α m s) :
    @Measure.restrict α m (μ.trim hm) s = (μ.restrict s).trim hm :=
  by
  ext1 t ht
  rw [@measure.restrict_apply α m _ _ _ ht, trim_measurable_set_eq hm ht,
    measure.restrict_apply (hm t ht),
    trim_measurable_set_eq hm (@MeasurableSet.inter α m t s ht hs)]
#align measure_theory.restrict_trim MeasureTheory.restrict_trim

instance isFiniteMeasureTrim (hm : m ≤ m0) [IsFiniteMeasure μ] : IsFiniteMeasure (μ.trim hm)
    where measure_univ_lt_top :=
    by
    rw [trim_measurable_set_eq hm (@MeasurableSet.univ _ m)]
    exact measure_lt_top _ _
#align measure_theory.is_finite_measure_trim MeasureTheory.isFiniteMeasureTrim

theorem sigmaFiniteTrimMono {m m₂ m0 : MeasurableSpace α} {μ : Measure α} (hm : m ≤ m0)
    (hm₂ : m₂ ≤ m) [SigmaFinite (μ.trim (hm₂.trans hm))] : SigmaFinite (μ.trim hm) :=
  by
  have h := measure.finite_spanning_sets_in (μ.trim (hm₂.trans hm)) Set.univ
  refine' measure.finite_spanning_sets_in.sigma_finite _
  · use Set.univ
  · refine'
      { Set := spanning_sets (μ.trim (hm₂.trans hm))
        set_mem := fun _ => Set.mem_univ _
        Finite := fun i => _
        -- This is the only one left to prove
        spanning := Union_spanning_sets _ }
    calc
      (μ.trim hm) (spanning_sets (μ.trim (hm₂.trans hm)) i) =
          ((μ.trim hm).trim hm₂) (spanning_sets (μ.trim (hm₂.trans hm)) i) :=
        by rw [@trim_measurable_set_eq α m₂ m (μ.trim hm) _ hm₂ (measurable_spanning_sets _ _)]
      _ = (μ.trim (hm₂.trans hm)) (spanning_sets (μ.trim (hm₂.trans hm)) i) := by
        rw [@trim_trim _ _ μ _ _ hm₂ hm]
      _ < ∞ := measure_spanning_sets_lt_top _ _
      
#align measure_theory.sigma_finite_trim_mono MeasureTheory.sigmaFiniteTrimMono

theorem sigmaFinite_trim_bot_iff : SigmaFinite (μ.trim bot_le) ↔ IsFiniteMeasure μ :=
  by
  rw [sigma_finite_bot_iff]
  refine' ⟨fun h => ⟨_⟩, fun h => ⟨_⟩⟩ <;> have h_univ := h.measure_univ_lt_top
  · rwa [trim_measurable_set_eq bot_le MeasurableSet.univ] at h_univ
  · rwa [trim_measurable_set_eq bot_le MeasurableSet.univ]
#align measure_theory.sigma_finite_trim_bot_iff MeasureTheory.sigmaFinite_trim_bot_iff

end Trim

end MeasureTheory

namespace IsCompact

variable [TopologicalSpace α] [MeasurableSpace α] {μ : Measure α} {s : Set α}

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (U «expr ⊇ » s) -/
/-- If `s` is a compact set and `μ` is finite at `𝓝 x` for every `x ∈ s`, then `s` admits an open
superset of finite measure. -/
theorem exists_open_superset_measure_lt_top' (h : IsCompact s)
    (hμ : ∀ x ∈ s, μ.FiniteAtFilter (𝓝 x)) : ∃ (U : _)(_ : U ⊇ s), IsOpen U ∧ μ U < ∞ :=
  by
  refine' IsCompact.induction_on h _ _ _ _
  · use ∅
    simp [Superset]
  · rintro s t hst ⟨U, htU, hUo, hU⟩
    exact ⟨U, hst.trans htU, hUo, hU⟩
  · rintro s t ⟨U, hsU, hUo, hU⟩ ⟨V, htV, hVo, hV⟩
    refine'
      ⟨U ∪ V, union_subset_union hsU htV, hUo.union hVo,
        (measure_union_le _ _).trans_lt <| ENNReal.add_lt_top.2 ⟨hU, hV⟩⟩
  · intro x hx
    rcases(hμ x hx).exists_mem_basis (nhds_basis_opens _) with ⟨U, ⟨hx, hUo⟩, hU⟩
    exact ⟨U, nhdsWithin_le_nhds (hUo.mem_nhds hx), U, subset.rfl, hUo, hU⟩
#align is_compact.exists_open_superset_measure_lt_top' IsCompact.exists_open_superset_measure_lt_top'

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (U «expr ⊇ » s) -/
/-- If `s` is a compact set and `μ` is a locally finite measure, then `s` admits an open superset of
finite measure. -/
theorem exists_open_superset_measure_lt_top (h : IsCompact s) (μ : Measure α)
    [IsLocallyFiniteMeasure μ] : ∃ (U : _)(_ : U ⊇ s), IsOpen U ∧ μ U < ∞ :=
  h.exists_open_superset_measure_lt_top' fun x hx => μ.finiteAtNhds x
#align is_compact.exists_open_superset_measure_lt_top IsCompact.exists_open_superset_measure_lt_top

theorem measure_lt_top_of_nhdsWithin (h : IsCompact s) (hμ : ∀ x ∈ s, μ.FiniteAtFilter (𝓝[s] x)) :
    μ s < ∞ :=
  IsCompact.induction_on h (by simp) (fun s t hst ht => (measure_mono hst).trans_lt ht)
    (fun s t hs ht => (measure_union_le s t).trans_lt (ENNReal.add_lt_top.2 ⟨hs, ht⟩)) hμ
#align is_compact.measure_lt_top_of_nhds_within IsCompact.measure_lt_top_of_nhdsWithin

theorem measure_zero_of_nhdsWithin (hs : IsCompact s) :
    (∀ a ∈ s, ∃ t ∈ 𝓝[s] a, μ t = 0) → μ s = 0 := by
  simpa only [← compl_mem_ae_iff] using hs.compl_mem_sets_of_nhds_within
#align is_compact.measure_zero_of_nhds_within IsCompact.measure_zero_of_nhdsWithin

end IsCompact

-- see Note [lower instance priority]
instance (priority := 100) isFiniteMeasureOnCompactsOfIsLocallyFiniteMeasure [TopologicalSpace α]
    {m : MeasurableSpace α} {μ : Measure α} [IsLocallyFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts μ :=
  ⟨fun s hs => hs.measure_lt_top_of_nhdsWithin fun x hx => μ.finiteAtNhdsWithin _ _⟩
#align is_finite_measure_on_compacts_of_is_locally_finite_measure isFiniteMeasureOnCompactsOfIsLocallyFiniteMeasure

theorem isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace [TopologicalSpace α]
    [MeasurableSpace α] {μ : Measure α} [CompactSpace α] :
    IsFiniteMeasure μ ↔ IsFiniteMeasureOnCompacts μ :=
  by
  constructor <;> intros
  · infer_instance
  · exact compact_space.is_finite_measure
#align is_finite_measure_iff_is_finite_measure_on_compacts_of_compact_space isFiniteMeasure_iff_isFiniteMeasureOnCompacts_of_compactSpace

/-- Compact covering of a `σ`-compact topological space as
`measure_theory.measure.finite_spanning_sets_in`. -/
def MeasureTheory.Measure.finiteSpanningSetsInCompact [TopologicalSpace α] [SigmaCompactSpace α]
    {m : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn { K | IsCompact K }
    where
  Set := compactCovering α
  set_mem := isCompact_compactCovering α
  Finite n := (isCompact_compactCovering α n).measure_lt_top
  spanning := unionᵢ_compactCovering α
#align measure_theory.measure.finite_spanning_sets_in_compact MeasureTheory.Measure.finiteSpanningSetsInCompact

/-- A locally finite measure on a `σ`-compact topological space admits a finite spanning sequence
of open sets. -/
def MeasureTheory.Measure.finiteSpanningSetsInOpen [TopologicalSpace α] [SigmaCompactSpace α]
    {m : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
    μ.FiniteSpanningSetsIn { K | IsOpen K }
    where
  Set n := ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).some
  set_mem n :=
    ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.snd.1
  Finite n :=
    ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.snd.2
  spanning :=
    eq_univ_of_subset
      (unionᵢ_mono fun n =>
        ((isCompact_compactCovering α n).exists_open_superset_measure_lt_top μ).choose_spec.fst)
      (unionᵢ_compactCovering α)
#align measure_theory.measure.finite_spanning_sets_in_open MeasureTheory.Measure.finiteSpanningSetsInOpen

open TopologicalSpace

/-- A locally finite measure on a second countable topological space admits a finite spanning
sequence of open sets. -/
irreducible_def MeasureTheory.Measure.finiteSpanningSetsInOpen' [TopologicalSpace α]
  [SecondCountableTopology α] {m : MeasurableSpace α} (μ : Measure α) [IsLocallyFiniteMeasure μ] :
  μ.FiniteSpanningSetsIn { K | IsOpen K } :=
  by
  suffices H : Nonempty (μ.finite_spanning_sets_in { K | IsOpen K })
  exact H.some
  cases isEmpty_or_nonempty α
  ·
    exact
      ⟨{  Set := fun n => ∅
          set_mem := fun n => by simp
          Finite := fun n => by simp
          spanning := by simp }⟩
  inhabit α
  let S : Set (Set α) := { s | IsOpen s ∧ μ s < ∞ }
  obtain ⟨T, T_count, TS, hT⟩ : ∃ T : Set (Set α), T.Countable ∧ T ⊆ S ∧ ⋃₀ T = ⋃₀ S :=
    is_open_sUnion_countable S fun s hs => hs.1
  rw [μ.is_topological_basis_is_open_lt_top.sUnion_eq] at hT
  have T_ne : T.nonempty := by
    by_contra h'T
    simp only [not_nonempty_iff_eq_empty.1 h'T, sUnion_empty] at hT
    simpa only [← hT] using mem_univ (default : α)
  obtain ⟨f, hf⟩ : ∃ f : ℕ → Set α, T = range f
  exact T_count.exists_eq_range T_ne
  have fS : ∀ n, f n ∈ S := by
    intro n
    apply TS
    rw [hf]
    exact mem_range_self n
  refine'
    ⟨{  Set := f
        set_mem := fun n => (fS n).1
        Finite := fun n => (fS n).2
        spanning := _ }⟩
  apply eq_univ_of_forall fun x => _
  obtain ⟨t, tT, xt⟩ : ∃ t : Set α, t ∈ range f ∧ x ∈ t :=
    by
    have : x ∈ ⋃₀ T := by simp only [hT]
    simpa only [mem_sUnion, exists_prop, ← hf]
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, f n = t := by simpa only using tT
  exact mem_Union_of_mem _ xt
#align measure_theory.measure.finite_spanning_sets_in_open' MeasureTheory.Measure.finiteSpanningSetsInOpen'

section MeasureIxx

variable [Preorder α] [TopologicalSpace α] [CompactIccSpace α] {m : MeasurableSpace α}
  {μ : Measure α} [IsLocallyFiniteMeasure μ] {a b : α}

theorem measure_Icc_lt_top : μ (Icc a b) < ∞ :=
  isCompact_Icc.measure_lt_top
#align measure_Icc_lt_top measure_Icc_lt_top

theorem measure_Ico_lt_top : μ (Ico a b) < ∞ :=
  (measure_mono Ico_subset_Icc_self).trans_lt measure_Icc_lt_top
#align measure_Ico_lt_top measure_Ico_lt_top

theorem measure_Ioc_lt_top : μ (Ioc a b) < ∞ :=
  (measure_mono Ioc_subset_Icc_self).trans_lt measure_Icc_lt_top
#align measure_Ioc_lt_top measure_Ioc_lt_top

theorem measure_Ioo_lt_top : μ (Ioo a b) < ∞ :=
  (measure_mono Ioo_subset_Icc_self).trans_lt measure_Icc_lt_top
#align measure_Ioo_lt_top measure_Ioo_lt_top

end MeasureIxx

section Piecewise

variable [MeasurableSpace α] {μ : Measure α} {s t : Set α} {f g : α → β}

theorem piecewise_ae_eq_restrict (hs : MeasurableSet s) : piecewise s f g =ᵐ[μ.restrict s] f :=
  by
  rw [ae_restrict_eq hs]
  exact (piecewise_eq_on s f g).EventuallyEq.filter_mono inf_le_right
#align piecewise_ae_eq_restrict piecewise_ae_eq_restrict

theorem piecewise_ae_eq_restrict_compl (hs : MeasurableSet s) :
    piecewise s f g =ᵐ[μ.restrict (sᶜ)] g :=
  by
  rw [ae_restrict_eq hs.compl]
  exact (piecewise_eq_on_compl s f g).EventuallyEq.filter_mono inf_le_right
#align piecewise_ae_eq_restrict_compl piecewise_ae_eq_restrict_compl

theorem piecewise_ae_eq_of_ae_eq_set (hst : s =ᵐ[μ] t) : s.piecewise f g =ᵐ[μ] t.piecewise f g :=
  hst.mem_iff.mono fun x hx => by simp [piecewise, hx]
#align piecewise_ae_eq_of_ae_eq_set piecewise_ae_eq_of_ae_eq_set

end Piecewise

section IndicatorFunction

variable [MeasurableSpace α] {μ : Measure α} {s t : Set α} {f : α → β}

theorem mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem [Zero β] {t : Set β}
    (ht : (0 : β) ∈ t) (hs : MeasurableSet s) :
    t ∈ Filter.map (s.indicator f) μ.ae ↔ t ∈ Filter.map f (μ.restrict s).ae :=
  by
  simp_rw [mem_map, mem_ae_iff]
  rw [measure.restrict_apply' hs, Set.indicator_preimage, Set.ite]
  simp_rw [Set.compl_union, Set.compl_inter]
  change μ (((f ⁻¹' t)ᶜ ∪ sᶜ) ∩ ((fun x => (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ ∩ s) = 0
  simp only [ht, ← Set.compl_eq_univ_diff, compl_compl, Set.compl_union, if_true,
    Set.preimage_const]
  simp_rw [Set.union_inter_distrib_right, Set.compl_inter_self s, Set.union_empty]
#align mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem

theorem mem_map_indicator_ae_iff_of_zero_nmem [Zero β] {t : Set β} (ht : (0 : β) ∉ t) :
    t ∈ Filter.map (s.indicator f) μ.ae ↔ μ ((f ⁻¹' t)ᶜ ∪ sᶜ) = 0 :=
  by
  rw [mem_map, mem_ae_iff, Set.indicator_preimage, Set.ite, Set.compl_union, Set.compl_inter]
  change μ (((f ⁻¹' t)ᶜ ∪ sᶜ) ∩ ((fun x => (0 : β)) ⁻¹' t \ s)ᶜ) = 0 ↔ μ ((f ⁻¹' t)ᶜ ∪ sᶜ) = 0
  simp only [ht, if_false, Set.compl_empty, Set.empty_diff, Set.inter_univ, Set.preimage_const]
#align mem_map_indicator_ae_iff_of_zero_nmem mem_map_indicator_ae_iff_of_zero_nmem

theorem map_restrict_ae_le_map_indicator_ae [Zero β] (hs : MeasurableSet s) :
    Filter.map f (μ.restrict s).ae ≤ Filter.map (s.indicator f) μ.ae :=
  by
  intro t
  by_cases ht : (0 : β) ∈ t
  · rw [mem_map_indicator_ae_iff_mem_map_restrict_ae_of_zero_mem ht hs]
    exact id
  rw [mem_map_indicator_ae_iff_of_zero_nmem ht, mem_map_restrict_ae_iff hs]
  exact fun h => measure_mono_null ((Set.inter_subset_left _ _).trans (Set.subset_union_left _ _)) h
#align map_restrict_ae_le_map_indicator_ae map_restrict_ae_le_map_indicator_ae

variable [Zero β]

theorem indicator_ae_eq_restrict (hs : MeasurableSet s) : indicator s f =ᵐ[μ.restrict s] f :=
  piecewise_ae_eq_restrict hs
#align indicator_ae_eq_restrict indicator_ae_eq_restrict

theorem indicator_ae_eq_restrict_compl (hs : MeasurableSet s) :
    indicator s f =ᵐ[μ.restrict (sᶜ)] 0 :=
  piecewise_ae_eq_restrict_compl hs
#align indicator_ae_eq_restrict_compl indicator_ae_eq_restrict_compl

theorem indicator_ae_eq_of_restrict_compl_ae_eq_zero (hs : MeasurableSet s)
    (hf : f =ᵐ[μ.restrict (sᶜ)] 0) : s.indicator f =ᵐ[μ] f :=
  by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs.compl] at hf
  filter_upwards [hf]with x hx
  by_cases hxs : x ∈ s
  · simp only [hxs, Set.indicator_of_mem]
  · simp only [hx hxs, Pi.zero_apply, Set.indicator_apply_eq_zero, eq_self_iff_true, imp_true_iff]
#align indicator_ae_eq_of_restrict_compl_ae_eq_zero indicator_ae_eq_of_restrict_compl_ae_eq_zero

theorem indicator_ae_eq_zero_of_restrict_ae_eq_zero (hs : MeasurableSet s)
    (hf : f =ᵐ[μ.restrict s] 0) : s.indicator f =ᵐ[μ] 0 :=
  by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs] at hf
  filter_upwards [hf]with x hx
  by_cases hxs : x ∈ s
  · simp only [hxs, hx hxs, Set.indicator_of_mem]
  · simp [hx, hxs]
#align indicator_ae_eq_zero_of_restrict_ae_eq_zero indicator_ae_eq_zero_of_restrict_ae_eq_zero

theorem indicator_ae_eq_of_ae_eq_set (hst : s =ᵐ[μ] t) : s.indicator f =ᵐ[μ] t.indicator f :=
  piecewise_ae_eq_of_ae_eq_set hst
#align indicator_ae_eq_of_ae_eq_set indicator_ae_eq_of_ae_eq_set

theorem indicator_meas_zero (hs : μ s = 0) : indicator s f =ᵐ[μ] 0 :=
  indicator_empty' f ▸ indicator_ae_eq_of_ae_eq_set (ae_eq_empty.2 hs)
#align indicator_meas_zero indicator_meas_zero

theorem ae_eq_restrict_iff_indicator_ae_eq {g : α → β} (hs : MeasurableSet s) :
    f =ᵐ[μ.restrict s] g ↔ s.indicator f =ᵐ[μ] s.indicator g :=
  by
  rw [Filter.EventuallyEq, ae_restrict_iff' hs]
  refine' ⟨fun h => _, fun h => _⟩ <;> filter_upwards [h]with x hx
  · by_cases hxs : x ∈ s
    · simp [hxs, hx hxs]
    · simp [hxs]
  · intro hxs
    simpa [hxs] using hx
#align ae_eq_restrict_iff_indicator_ae_eq ae_eq_restrict_iff_indicator_ae_eq

end IndicatorFunction

